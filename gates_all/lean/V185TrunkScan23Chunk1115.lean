import V185TrunkScan23Chunk1114

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6603880 : List Nat := [2, 1, 4, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_6603880 : Nat := 118140960795 + 6603880 * 2 ^ 59
def prefixEnd_6603880 : Nat := 4983230072969 + 3 ^ 40 * 6603880 * 2
def baseEnd_6603880 : Nat := 3390964624613727522829315

theorem tailTrace_6603880 : CollatzResearch.WordTrace tailWord_6603880 prefixEnd_6603880 3390964624613727522829315 := by
  unfold tailWord_6603880
  simp only [CollatzResearch.WordTrace]
  refine ⟨120431645657639043878076547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160575527543518725170768729 120431645657639043878076547)
  ·
    refine ⟨180647468486458565817114821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120431645657639043878076547 180647468486458565817114821)
    ·
      refine ⟨33871400341210981090709029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180647468486458565817114821 33871400341210981090709029)
      ·
        refine ⟨6350887563977058954507943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33871400341210981090709029 6350887563977058954507943)
        ·
          refine ⟨9526331345965588431761915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6350887563977058954507943 9526331345965588431761915)
          ·
            refine ⟨14289497018948382647642873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9526331345965588431761915 14289497018948382647642873)
            ·
              refine ⟨10717122764211286985732155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14289497018948382647642873 10717122764211286985732155)
              ·
                refine ⟨16075684146316930478598233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10717122764211286985732155 16075684146316930478598233)
                ·
                  refine ⟨12056763109737697858948675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16075684146316930478598233 12056763109737697858948675)
                  ·
                    refine ⟨18085144664606546788423013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12056763109737697858948675 18085144664606546788423013)
                    ·
                      refine ⟨3390964624613727522829315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18085144664606546788423013 3390964624613727522829315)
                      ·
                        rfl

theorem cell23_6603880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_6603880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603880 prefixEnd_6603880 := by exact prefixLift 6603880
  have htrace : WordTrace (prefixWord ++ tailWord_6603880) baseStart_6603880 baseEnd_6603880 := by
    simpa [prefixWord, tailWord_6603880, baseEnd_6603880] using wordTrace_append hprefix tailTrace_6603880
  have hstable : (prefixWord ++ tailWord_6603880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603880).length < 2 ^ (prefixWord ++ tailWord_6603880).sum := by decide
  have hdescent : baseEnd_6603880 < baseStart_6603880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603930 : List Nat := [3, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3]
def baseStart_6603930 : Nat := 118140960795 + 6603930 * 2 ^ 59
def prefixEnd_6603930 : Nat := 4983230072969 + 3 ^ 40 * 6603930 * 2
def baseEnd_6603930 : Nat := 3390990298646452327204085

theorem tailTrace_6603930 : CollatzResearch.WordTrace tailWord_6603930 prefixEnd_6603930 3390990298646452327204085 := by
  unfold tailWord_6603930
  simp only [CollatzResearch.WordTrace]
  refine ⟨60216278741274236573868311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160576743310064630863648829 60216278741274236573868311)
  ·
    refine ⟨90324418111911354860802467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60216278741274236573868311 90324418111911354860802467)
    ·
      refine ⟨135486627167867032291203701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90324418111911354860802467 135486627167867032291203701)
      ·
        refine ⟨12701871296987534277300347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 135486627167867032291203701 12701871296987534277300347)
        ·
          refine ⟨19052806945481301415950521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12701871296987534277300347 19052806945481301415950521)
          ·
            refine ⟨14289605209110976061962891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19052806945481301415950521 14289605209110976061962891)
            ·
              refine ⟨21434407813666464092944337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14289605209110976061962891 21434407813666464092944337)
              ·
                refine ⟨16075805860249848069708253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21434407813666464092944337 16075805860249848069708253)
                ·
                  refine ⟨6028427197593693026140595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16075805860249848069708253 6028427197593693026140595)
                  ·
                    refine ⟨9042640796390539539210893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6028427197593693026140595 9042640796390539539210893)
                    ·
                      refine ⟨3390990298646452327204085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9042640796390539539210893 3390990298646452327204085)
                      ·
                        rfl

theorem cell23_6603930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_6603930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603930 prefixEnd_6603930 := by exact prefixLift 6603930
  have htrace : WordTrace (prefixWord ++ tailWord_6603930) baseStart_6603930 baseEnd_6603930 := by
    simpa [prefixWord, tailWord_6603930, baseEnd_6603930] using wordTrace_append hprefix tailTrace_6603930
  have hstable : (prefixWord ++ tailWord_6603930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603930).length < 2 ^ (prefixWord ++ tailWord_6603930).sum := by decide
  have hdescent : baseEnd_6603930 < baseStart_6603930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603936 : List Nat := [2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 4]
def baseStart_6603936 : Nat := 118140960795 + 6603936 * 2 ^ 59
def prefixEnd_6603936 : Nat := 4983230072969 + 3 ^ 40 * 6603936 * 2
def baseEnd_6603936 : Nat := 3390993379530379303729057

theorem tailTrace_6603936 : CollatzResearch.WordTrace tailWord_6603936 prefixEnd_6603936 3390993379530379303729057 := by
  unfold tailWord_6603936
  simp only [CollatzResearch.WordTrace]
  refine ⟨120432666901537604660095831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160576889202050139546794441 120432666901537604660095831)
  ·
    refine ⟨180649000352306406990143747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120432666901537604660095831 180649000352306406990143747)
    ·
      refine ⟨270973500528459610485215621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180649000352306406990143747 270973500528459610485215621)
      ·
        refine ⟨50807531349086176965977929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 270973500528459610485215621 50807531349086176965977929)
        ·
          refine ⟨38105648511814632724483447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50807531349086176965977929 38105648511814632724483447)
          ·
            refine ⟨57158472767721949086725171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38105648511814632724483447 57158472767721949086725171)
            ·
              refine ⟨85737709151582923630087757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57158472767721949086725171 85737709151582923630087757)
              ·
                refine ⟨32151640931843596361282909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85737709151582923630087757 32151640931843596361282909)
                ·
                  refine ⟨12056865349441348635481091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32151640931843596361282909 12056865349441348635481091)
                  ·
                    refine ⟨18085298024162022953221637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12056865349441348635481091 18085298024162022953221637)
                    ·
                      refine ⟨3390993379530379303729057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18085298024162022953221637 3390993379530379303729057)
                      ·
                        rfl

theorem cell23_6603936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_6603936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603936 prefixEnd_6603936 := by exact prefixLift 6603936
  have htrace : WordTrace (prefixWord ++ tailWord_6603936) baseStart_6603936 baseEnd_6603936 := by
    simpa [prefixWord, tailWord_6603936, baseEnd_6603936] using wordTrace_append hprefix tailTrace_6603936
  have hstable : (prefixWord ++ tailWord_6603936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603936).length < 2 ^ (prefixWord ++ tailWord_6603936).sum := by decide
  have hdescent : baseEnd_6603936 < baseStart_6603936 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603940 : List Nat := [2, 3, 1, 2, 3, 1, 3, 1, 2, 3, 2]
def baseStart_6603940 : Nat := 118140960795 + 6603940 * 2 ^ 59
def prefixEnd_6603940 : Nat := 4983230072969 + 3 ^ 40 * 6603940 * 2
def baseEnd_6603940 : Nat := 3390995433452997288079039

theorem tailTrace_6603940 : CollatzResearch.WordTrace tailWord_6603940 prefixEnd_6603940 3390995433452997288079039 := by
  unfold tailWord_6603940
  simp only [CollatzResearch.WordTrace]
  refine ⟨120432739847530359001668637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160576986463373812002224849 120432739847530359001668637)
  ·
    refine ⟨45162277442823884625625739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120432739847530359001668637 45162277442823884625625739)
    ·
      refine ⟨67743416164235826938438609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45162277442823884625625739 67743416164235826938438609)
      ·
        refine ⟨50807562123176870203828957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67743416164235826938438609 50807562123176870203828957)
        ·
          refine ⟨19052835796191326326435859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50807562123176870203828957 19052835796191326326435859)
          ·
            refine ⟨28579253694286989489653789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19052835796191326326435859 28579253694286989489653789)
            ·
              refine ⟨10717220135357621058620171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28579253694286989489653789 10717220135357621058620171)
              ·
                refine ⟨16075830203036431587930257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10717220135357621058620171 16075830203036431587930257)
                ·
                  refine ⟨12056872652277323690947693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16075830203036431587930257 12056872652277323690947693)
                  ·
                    refine ⟨4521327244603996384105385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12056872652277323690947693 4521327244603996384105385)
                    ·
                      refine ⟨3390995433452997288079039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4521327244603996384105385 3390995433452997288079039)
                      ·
                        rfl

theorem cell23_6603940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_6603940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603940 prefixEnd_6603940 := by exact prefixLift 6603940
  have htrace : WordTrace (prefixWord ++ tailWord_6603940) baseStart_6603940 baseEnd_6603940 := by
    simpa [prefixWord, tailWord_6603940, baseEnd_6603940] using wordTrace_append hprefix tailTrace_6603940
  have hstable : (prefixWord ++ tailWord_6603940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603940).length < 2 ^ (prefixWord ++ tailWord_6603940).sum := by decide
  have hdescent : baseEnd_6603940 < baseStart_6603940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603959 : List Nat := [1, 1, 3, 1, 4, 1, 12]
def baseStart_6603959 : Nat := 118140960795 + 6603959 * 2 ^ 59
def prefixEnd_6603959 : Nat := 4983230072969 + 3 ^ 40 * 6603959 * 2
def baseEnd_6603959 : Nat := 41864261599820156959771

theorem tailTrace_6603959 : CollatzResearch.WordTrace tailWord_6603959 prefixEnd_6603959 41864261599820156959771 := by
  unfold tailWord_6603959
  simp only [CollatzResearch.WordTrace]
  refine ⟨240866172681991884248278931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160577448454661256165519287 240866172681991884248278931)
  ·
    refine ⟨361299259022987826372418397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240866172681991884248278931 361299259022987826372418397)
    ·
      refine ⟨135487222133620434889656899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361299259022987826372418397 135487222133620434889656899)
      ·
        refine ⟨203230833200430652334485349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135487222133620434889656899 203230833200430652334485349)
        ·
          refine ⟨38105781225080747312716003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203230833200430652334485349 38105781225080747312716003)
          ·
            refine ⟨57158671837621120969074005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38105781225080747312716003 57158671837621120969074005)
            ·
              refine ⟨41864261599820156959771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 57158671837621120969074005 41864261599820156959771)
              ·
                rfl

theorem cell23_6603959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 12].length) (baseStart_6603959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603959 prefixEnd_6603959 := by exact prefixLift 6603959
  have htrace : WordTrace (prefixWord ++ tailWord_6603959) baseStart_6603959 baseEnd_6603959 := by
    simpa [prefixWord, tailWord_6603959, baseEnd_6603959] using wordTrace_append hprefix tailTrace_6603959
  have hstable : (prefixWord ++ tailWord_6603959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603959).length < 2 ^ (prefixWord ++ tailWord_6603959).sum := by decide
  have hdescent : baseEnd_6603959 < baseStart_6603959 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6603979 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 6]
def baseStart_6603979 : Nat := 118140960795 + 6603979 * 2 ^ 59
def prefixEnd_6603979 : Nat := 4983230072969 + 3 ^ 40 * 6603979 * 2
def baseEnd_6603979 : Nat := 3391015459198522635491359

theorem tailTrace_6603979 : CollatzResearch.WordTrace tailWord_6603979 prefixEnd_6603979 3391015459198522635491359 := by
  unfold tailWord_6603979
  simp only [CollatzResearch.WordTrace]
  refine ⟨240866902141919427664006991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160577934761279618442671327 240866902141919427664006991)
  ·
    refine ⟨361300353212879141496010487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240866902141919427664006991 361300353212879141496010487)
    ·
      refine ⟨541950529819318712244015731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361300353212879141496010487 541950529819318712244015731)
      ·
        refine ⟨812925794728978068366023597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541950529819318712244015731 812925794728978068366023597)
        ·
          refine ⟨304847173023366775637258849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 812925794728978068366023597 304847173023366775637258849)
          ·
            refine ⟨228635379767525081727944137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304847173023366775637258849 228635379767525081727944137)
            ·
              refine ⟨171476534825643811295958103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228635379767525081727944137 171476534825643811295958103)
              ·
                refine ⟨257214802238465716943937155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171476534825643811295958103 257214802238465716943937155)
                ·
                  refine ⟨385822203357698575415905733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257214802238465716943937155 385822203357698575415905733)
                  ·
                    refine ⟨72341663129568482890482325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 385822203357698575415905733 72341663129568482890482325)
                    ·
                      refine ⟨3391015459198522635491359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72341663129568482890482325 3391015459198522635491359)
                      ·
                        rfl

theorem cell23_6603979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 6].length) (baseStart_6603979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6603979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6603979 prefixEnd_6603979 := by exact prefixLift 6603979
  have htrace : WordTrace (prefixWord ++ tailWord_6603979) baseStart_6603979 baseEnd_6603979 := by
    simpa [prefixWord, tailWord_6603979, baseEnd_6603979] using wordTrace_append hprefix tailTrace_6603979
  have hstable : (prefixWord ++ tailWord_6603979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6603979).length < 2 ^ (prefixWord ++ tailWord_6603979).sum := by decide
  have hdescent : baseEnd_6603979 < baseStart_6603979 := by decide
  rcases family_descends (prefixWord ++ tailWord_6603979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604026 : List Nat := [3, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4]
def baseStart_6604026 : Nat := 118140960795 + 6604026 * 2 ^ 59
def prefixEnd_6604026 : Nat := 4983230072969 + 3 ^ 40 * 6604026 * 2
def baseEnd_6604026 : Nat := 3391039592789283951603643

theorem tailTrace_6604026 : CollatzResearch.WordTrace tailWord_6604026 prefixEnd_6604026 3391039592789283951603643 := by
  unfold tailWord_6604026
  simp only [CollatzResearch.WordTrace]
  refine ⟨60217154093187288672741983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160579077581832769793978621 60217154093187288672741983)
  ·
    refine ⟨90325731139780933009112975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60217154093187288672741983 90325731139780933009112975)
    ·
      refine ⟨135488596709671399513669463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90325731139780933009112975 135488596709671399513669463)
      ·
        refine ⟨203232895064507099270504195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135488596709671399513669463 203232895064507099270504195)
        ·
          refine ⟨304849342596760648905756293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203232895064507099270504195 304849342596760648905756293)
          ·
            refine ⟨57159251736892621669829305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304849342596760648905756293 57159251736892621669829305)
            ·
              refine ⟨42869438802669466252371979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57159251736892621669829305 42869438802669466252371979)
              ·
                refine ⟨64304158204004199378557969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42869438802669466252371979 64304158204004199378557969)
                ·
                  refine ⟨48228118653003149533918477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64304158204004199378557969 48228118653003149533918477)
                  ·
                    refine ⟨18085544494876181075219429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48228118653003149533918477 18085544494876181075219429)
                    ·
                      refine ⟨3391039592789283951603643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18085544494876181075219429 3391039592789283951603643)
                      ·
                        rfl

theorem cell23_6604026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_6604026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604026 prefixEnd_6604026 := by exact prefixLift 6604026
  have htrace : WordTrace (prefixWord ++ tailWord_6604026) baseStart_6604026 baseEnd_6604026 := by
    simpa [prefixWord, tailWord_6604026, baseEnd_6604026] using wordTrace_append hprefix tailTrace_6604026
  have hstable : (prefixWord ++ tailWord_6604026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604026).length < 2 ^ (prefixWord ++ tailWord_6604026).sum := by decide
  have hdescent : baseEnd_6604026 < baseStart_6604026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604060 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 6, 2, 2]
def baseStart_6604060 : Nat := 118140960795 + 6604060 * 2 ^ 59
def prefixEnd_6604060 : Nat := 4983230072969 + 3 ^ 40 * 6604060 * 2
def baseEnd_6604060 : Nat := 3391057051131536818578487

theorem tailTrace_6604060 : CollatzResearch.WordTrace tailWord_6604060 prefixEnd_6604060 3391057051131536818578487 := by
  unfold tailWord_6604060
  simp only [CollatzResearch.WordTrace]
  refine ⟨120434928227312989248852817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160579904303083985665137089 120434928227312989248852817)
  ·
    refine ⟨90326196170484741936639613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120434928227312989248852817 90326196170484741936639613)
    ·
      refine ⟨33872323563931778226239855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90326196170484741936639613 33872323563931778226239855)
      ·
        refine ⟨50808485345897667339359783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33872323563931778226239855 50808485345897667339359783)
        ·
          refine ⟨76212728018846501009039675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50808485345897667339359783 76212728018846501009039675)
          ·
            refine ⟨114319092028269751513559513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76212728018846501009039675 114319092028269751513559513)
            ·
              refine ⟨85739319021202313635169635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114319092028269751513559513 85739319021202313635169635)
              ·
                refine ⟨128608978531803470452754453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85739319021202313635169635 128608978531803470452754453)
                ·
                  refine ⟨6028545868678287677472865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 128608978531803470452754453 6028545868678287677472865)
                  ·
                    refine ⟨4521409401508715758104649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6028545868678287677472865 4521409401508715758104649)
                    ·
                      refine ⟨3391057051131536818578487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4521409401508715758104649 3391057051131536818578487)
                      ·
                        rfl

theorem cell23_6604060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_6604060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604060 prefixEnd_6604060 := by exact prefixLift 6604060
  have htrace : WordTrace (prefixWord ++ tailWord_6604060) baseStart_6604060 baseEnd_6604060 := by
    simpa [prefixWord, tailWord_6604060, baseEnd_6604060] using wordTrace_append hprefix tailTrace_6604060
  have hstable : (prefixWord ++ tailWord_6604060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604060).length < 2 ^ (prefixWord ++ tailWord_6604060).sum := by decide
  have hdescent : baseEnd_6604060 < baseStart_6604060 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604064 : List Nat := [2, 1, 1, 5, 3, 1, 3, 1, 1, 3, 2]
def baseStart_6604064 : Nat := 118140960795 + 6604064 * 2 ^ 59
def prefixEnd_6604064 : Nat := 4983230072969 + 3 ^ 40 * 6604064 * 2
def baseEnd_6604064 : Nat := 3391059105054154802928469

theorem tailTrace_6604064 : CollatzResearch.WordTrace tailWord_6604064 prefixEnd_6604064 3391059105054154802928469 := by
  unfold tailWord_6604064
  simp only [CollatzResearch.WordTrace]
  refine ⟨120435001173305743590425623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160580001564407658120567497 120435001173305743590425623)
  ·
    refine ⟨180652501759958615385638435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120435001173305743590425623 180652501759958615385638435)
    ·
      refine ⟨270978752639937923078457653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180652501759958615385638435 270978752639937923078457653)
      ·
        refine ⟨25404258059994180288605405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 270978752639937923078457653 25404258059994180288605405)
        ·
          refine ⟨9526596772497817608227027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25404258059994180288605405 9526596772497817608227027)
          ·
            refine ⟨14289895158746726412340541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9526596772497817608227027 14289895158746726412340541)
            ·
              refine ⟨5358710684530022404627703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14289895158746726412340541 5358710684530022404627703)
              ·
                refine ⟨8038066026795033606941555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5358710684530022404627703 8038066026795033606941555)
                ·
                  refine ⟨12057099040192550410412333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8038066026795033606941555 12057099040192550410412333)
                  ·
                    refine ⟨4521412140072206403904625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12057099040192550410412333 4521412140072206403904625)
                    ·
                      refine ⟨3391059105054154802928469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4521412140072206403904625 3391059105054154802928469)
                      ·
                        rfl

theorem cell23_6604064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_6604064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604064 prefixEnd_6604064 := by exact prefixLift 6604064
  have htrace : WordTrace (prefixWord ++ tailWord_6604064) baseStart_6604064 baseEnd_6604064 := by
    simpa [prefixWord, tailWord_6604064, baseEnd_6604064] using wordTrace_append hprefix tailTrace_6604064
  have hstable : (prefixWord ++ tailWord_6604064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604064).length < 2 ^ (prefixWord ++ tailWord_6604064).sum := by decide
  have hdescent : baseEnd_6604064 < baseStart_6604064 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604096 : List Nat := [2, 1, 1, 2, 2, 1, 4, 2, 1, 7]
def baseStart_6604096 : Nat := 118140960795 + 6604096 * 2 ^ 59
def prefixEnd_6604096 : Nat := 4983230072969 + 3 ^ 40 * 6604096 * 2
def baseEnd_6604096 : Nat := 1130358512145032892576107

theorem tailTrace_6604096 : CollatzResearch.WordTrace tailWord_6604096 prefixEnd_6604096 1130358512145032892576107 := by
  unfold tailWord_6604096
  simp only [CollatzResearch.WordTrace]
  refine ⟨120435584741247778323008071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160580779654997037764010761 120435584741247778323008071)
  ·
    refine ⟨180653377111871667484512107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120435584741247778323008071 180653377111871667484512107)
    ·
      refine ⟨270980065667807501226768161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180653377111871667484512107 270980065667807501226768161)
      ·
        refine ⟨203235049250855625920076121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270980065667807501226768161 203235049250855625920076121)
        ·
          refine ⟨152426286938141719440057091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203235049250855625920076121 152426286938141719440057091)
          ·
            refine ⟨228639430407212579160085637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152426286938141719440057091 228639430407212579160085637)
            ·
              refine ⟨42869893201352358592516057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228639430407212579160085637 42869893201352358592516057)
              ·
                refine ⟨32152419901014268944387043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42869893201352358592516057 32152419901014268944387043)
                ·
                  refine ⟨48228629851521403416580565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32152419901014268944387043 48228629851521403416580565)
                  ·
                    refine ⟨1130358512145032892576107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48228629851521403416580565 1130358512145032892576107)
                    ·
                      rfl

theorem cell23_6604096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 2, 1, 7].length) (baseStart_6604096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604096 prefixEnd_6604096 := by exact prefixLift 6604096
  have htrace : WordTrace (prefixWord ++ tailWord_6604096) baseStart_6604096 baseEnd_6604096 := by
    simpa [prefixWord, tailWord_6604096, baseEnd_6604096] using wordTrace_append hprefix tailTrace_6604096
  have hstable : (prefixWord ++ tailWord_6604096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604096).length < 2 ^ (prefixWord ++ tailWord_6604096).sum := by decide
  have hdescent : baseEnd_6604096 < baseStart_6604096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604100 : List Nat := [2, 3, 4, 1, 1, 2, 1, 2, 7]
def baseStart_6604100 : Nat := 118140960795 + 6604100 * 2 ^ 59
def prefixEnd_6604100 : Nat := 4983230072969 + 3 ^ 40 * 6604100 * 2
def baseEnd_6604100 : Nat := 376786398928635184675367

theorem tailTrace_6604100 : CollatzResearch.WordTrace tailWord_6604100 prefixEnd_6604100 376786398928635184675367 := by
  unfold tailWord_6604100
  simp only [CollatzResearch.WordTrace]
  refine ⟨120435657687240532664580877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160580876916320710219441169 120435657687240532664580877)
  ·
    refine ⟨45163371632715199749217829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120435657687240532664580877 45163371632715199749217829)
    ·
      refine ⟨8468132181134099952978343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45163371632715199749217829 8468132181134099952978343)
      ·
        refine ⟨12702198271701149929467515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8468132181134099952978343 12702198271701149929467515)
        ·
          refine ⟨19053297407551724894201273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12702198271701149929467515 19053297407551724894201273)
          ·
            refine ⟨14289973055663793670650955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19053297407551724894201273 14289973055663793670650955)
            ·
              refine ⟨21434959583495690505976433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14289973055663793670650955 21434959583495690505976433)
              ·
                refine ⟨16076219687621767879482325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21434959583495690505976433 16076219687621767879482325)
                ·
                  refine ⟨376786398928635184675367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16076219687621767879482325 376786398928635184675367)
                  ·
                    rfl

theorem cell23_6604100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 7].length) (baseStart_6604100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604100 prefixEnd_6604100 := by exact prefixLift 6604100
  have htrace : WordTrace (prefixWord ++ tailWord_6604100) baseStart_6604100 baseEnd_6604100 := by
    simpa [prefixWord, tailWord_6604100, baseEnd_6604100] using wordTrace_append hprefix tailTrace_6604100
  have hstable : (prefixWord ++ tailWord_6604100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604100).length < 2 ^ (prefixWord ++ tailWord_6604100).sum := by decide
  have hdescent : baseEnd_6604100 < baseStart_6604100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604106 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 1, 1, 7]
def baseStart_6604106 : Nat := 118140960795 + 6604106 * 2 ^ 59
def prefixEnd_6604106 : Nat := 4983230072969 + 3 ^ 40 * 6604106 * 2
def baseEnd_6604106 : Nat := 3391080671241643638603275

theorem tailTrace_6604106 : CollatzResearch.WordTrace tailWord_6604106 prefixEnd_6604106 3391080671241643638603275 := by
  unfold tailWord_6604106
  simp only [CollatzResearch.WordTrace]
  refine ⟨60217883553114832088470043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160581022808306218902586781 60217883553114832088470043)
  ·
    refine ⟨90326825329672248132705065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60217883553114832088470043 90326825329672248132705065)
    ·
      refine ⟨67745118997254186099528799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90326825329672248132705065 67745118997254186099528799)
      ·
        refine ⟨101617678495881279149293199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67745118997254186099528799 101617678495881279149293199)
        ·
          refine ⟨152426517743821918723939799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101617678495881279149293199 152426517743821918723939799)
          ·
            refine ⟨228639776615732878085909699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152426517743821918723939799 228639776615732878085909699)
            ·
              refine ⟨342959664923599317128864549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228639776615732878085909699 342959664923599317128864549)
              ·
                refine ⟨64304937173174871961662103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 342959664923599317128864549 64304937173174871961662103)
                ·
                  refine ⟨96457405759762307942493155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64304937173174871961662103 96457405759762307942493155)
                  ·
                    refine ⟨144686108639643461913739733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96457405759762307942493155 144686108639643461913739733)
                    ·
                      refine ⟨3391080671241643638603275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144686108639643461913739733 3391080671241643638603275)
                      ·
                        rfl

theorem cell23_6604106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_6604106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604106 prefixEnd_6604106 := by exact prefixLift 6604106
  have htrace : WordTrace (prefixWord ++ tailWord_6604106) baseStart_6604106 baseEnd_6604106 := by
    simpa [prefixWord, tailWord_6604106, baseEnd_6604106] using wordTrace_append hprefix tailTrace_6604106
  have hstable : (prefixWord ++ tailWord_6604106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604106).length < 2 ^ (prefixWord ++ tailWord_6604106).sum := by decide
  have hdescent : baseEnd_6604106 < baseStart_6604106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604133 : List Nat := [1, 3, 1, 3, 1, 2, 2, 1, 4, 1, 4]
def baseStart_6604133 : Nat := 118140960795 + 6604133 * 2 ^ 59
def prefixEnd_6604133 : Nat := 4983230072969 + 3 ^ 40 * 6604133 * 2
def baseEnd_6604133 : Nat := 3391094535219315032965651

theorem tailTrace_6604133 : CollatzResearch.WordTrace tailWord_6604133 prefixEnd_6604133 3391094535219315032965651 := by
  unfold tailWord_6604133
  simp only [CollatzResearch.WordTrace]
  refine ⟨240872518983361511965113053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160581679322241007976742035 240872518983361511965113053)
  ·
    refine ⟨90327194618760566986917395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240872518983361511965113053 90327194618760566986917395)
    ·
      refine ⟨135490791928140850480376093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90327194618760566986917395 135490791928140850480376093)
      ·
        refine ⟨50809046973052818930141035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135490791928140850480376093 50809046973052818930141035)
        ·
          refine ⟨76213570459579228395211553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50809046973052818930141035 76213570459579228395211553)
          ·
            refine ⟨57160177844684421296408665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76213570459579228395211553 57160177844684421296408665)
            ·
              refine ⟨42870133383513315972306499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57160177844684421296408665 42870133383513315972306499)
              ·
                refine ⟨64305200075269973958459749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42870133383513315972306499 64305200075269973958459749)
                ·
                  refine ⟨12057225014113120117211203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64305200075269973958459749 12057225014113120117211203)
                  ·
                    refine ⟨18085837521169680175816805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12057225014113120117211203 18085837521169680175816805)
                    ·
                      refine ⟨3391094535219315032965651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18085837521169680175816805 3391094535219315032965651)
                      ·
                        rfl

theorem cell23_6604133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_6604133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604133 prefixEnd_6604133 := by exact prefixLift 6604133
  have htrace : WordTrace (prefixWord ++ tailWord_6604133) baseStart_6604133 baseEnd_6604133 := by
    simpa [prefixWord, tailWord_6604133, baseEnd_6604133] using wordTrace_append hprefix tailTrace_6604133
  have hstable : (prefixWord ++ tailWord_6604133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604133).length < 2 ^ (prefixWord ++ tailWord_6604133).sum := by decide
  have hdescent : baseEnd_6604133 < baseStart_6604133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604153 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 1, 4, 3]
def baseStart_6604153 : Nat := 118140960795 + 6604153 * 2 ^ 59
def prefixEnd_6604153 : Nat := 4983230072969 + 3 ^ 40 * 6604153 * 2
def baseEnd_6604153 : Nat := 3391104804832404954715559

theorem tailTrace_6604153 : CollatzResearch.WordTrace tailWord_6604153 prefixEnd_6604153 3391104804832404954715559 := by
  unfold tailWord_6604153
  simp only [CollatzResearch.WordTrace]
  refine ⟨240873248443289055380841113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160582165628859370253894075 240873248443289055380841113)
  ·
    refine ⟨180654936332466791535630835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240873248443289055380841113 180654936332466791535630835)
    ·
      refine ⟨270982404498700187303446253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180654936332466791535630835 270982404498700187303446253)
      ·
        refine ⟨101618401687012570238792345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 270982404498700187303446253 101618401687012570238792345)
        ·
          refine ⟨76213801265259427679094259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101618401687012570238792345 76213801265259427679094259)
          ·
            refine ⟨114320701897889141518641389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76213801265259427679094259 114320701897889141518641389)
            ·
              refine ⟨42870263211708428069490521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114320701897889141518641389 42870263211708428069490521)
              ·
                refine ⟨32152697408781321052117891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42870263211708428069490521 32152697408781321052117891)
                ·
                  refine ⟨48229046113171981578176837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32152697408781321052117891 48229046113171981578176837)
                  ·
                    refine ⟨9042946146219746545908157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48229046113171981578176837 9042946146219746545908157)
                    ·
                      refine ⟨3391104804832404954715559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9042946146219746545908157 3391104804832404954715559)
                      ·
                        rfl

theorem cell23_6604153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_6604153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604153 prefixEnd_6604153 := by exact prefixLift 6604153
  have htrace : WordTrace (prefixWord ++ tailWord_6604153) baseStart_6604153 baseEnd_6604153 := by
    simpa [prefixWord, tailWord_6604153, baseEnd_6604153] using wordTrace_append hprefix tailTrace_6604153
  have hstable : (prefixWord ++ tailWord_6604153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604153).length < 2 ^ (prefixWord ++ tailWord_6604153).sum := by decide
  have hdescent : baseEnd_6604153 < baseStart_6604153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604210 : List Nat := [3, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2]
def baseStart_6604210 : Nat := 118140960795 + 6604210 * 2 ^ 59
def prefixEnd_6604210 : Nat := 4983230072969 + 3 ^ 40 * 6604210 * 2
def baseEnd_6604210 : Nat := 3391134073229711231702797

theorem tailTrace_6604210 : CollatzResearch.WordTrace tailWord_6604210 prefixEnd_6604210 3391134073229711231702797 := by
  unfold tailWord_6604210
  simp only [CollatzResearch.WordTrace]
  refine ⟨60218831851020638528916521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160583551602721702743777389 60218831851020638528916521)
  ·
    refine ⟨45164123888265478896687391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60218831851020638528916521 45164123888265478896687391)
    ·
      refine ⟨67746185832398218345031087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45164123888265478896687391 67746185832398218345031087)
      ·
        refine ⟨101619278748597327517546631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67746185832398218345031087 101619278748597327517546631)
        ·
          refine ⟨152428918122895991276319947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101619278748597327517546631 152428918122895991276319947)
          ·
            refine ⟨228643377184343986914479921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152428918122895991276319947 228643377184343986914479921)
            ·
              refine ⟨171482532888257990185859941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228643377184343986914479921 171482532888257990185859941)
              ·
                refine ⟨32152974916548373159848739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171482532888257990185859941 32152974916548373159848739)
                ·
                  refine ⟨48229462374822559739773109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32152974916548373159848739 48229462374822559739773109)
                  ·
                    refine ⟨4521512097639614975603729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48229462374822559739773109 4521512097639614975603729)
                    ·
                      refine ⟨3391134073229711231702797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4521512097639614975603729 3391134073229711231702797)
                      ·
                        rfl

theorem cell23_6604210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2].length) (baseStart_6604210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604210 prefixEnd_6604210 := by exact prefixLift 6604210
  have htrace : WordTrace (prefixWord ++ tailWord_6604210) baseStart_6604210 baseEnd_6604210 := by
    simpa [prefixWord, tailWord_6604210, baseEnd_6604210] using wordTrace_append hprefix tailTrace_6604210
  have hstable : (prefixWord ++ tailWord_6604210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604210).length < 2 ^ (prefixWord ++ tailWord_6604210).sum := by decide
  have hdescent : baseEnd_6604210 < baseStart_6604210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604274 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 5, 2, 2]
def baseStart_6604274 : Nat := 118140960795 + 6604274 * 2 ^ 59
def prefixEnd_6604274 : Nat := 4983230072969 + 3 ^ 40 * 6604274 * 2
def baseEnd_6604274 : Nat := 3391166935991598981302503

theorem tailTrace_6604274 : CollatzResearch.WordTrace tailWord_6604274 prefixEnd_6604274 3391166935991598981302503 := by
  unfold tailWord_6604274
  simp only [CollatzResearch.WordTrace]
  refine ⟨60219415418962673261498969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160585107783900462030663917 60219415418962673261498969)
  ·
    refine ⟨45164561564222004946124227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60219415418962673261498969 45164561564222004946124227)
    ·
      refine ⟨67746842346333007419186341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45164561564222004946124227 67746842346333007419186341)
      ·
        refine ⟨12702532939937438891097439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67746842346333007419186341 12702532939937438891097439)
        ·
          refine ⟨19053799409906158336646159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12702532939937438891097439 19053799409906158336646159)
          ·
            refine ⟨28580699114859237504969239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19053799409906158336646159 28580699114859237504969239)
            ·
              refine ⟨42871048672288856257453859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28580699114859237504969239 42871048672288856257453859)
              ·
                refine ⟨64306573008433284386180789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42871048672288856257453859 64306573008433284386180789)
                ·
                  refine ⟨6028741219540620411204449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64306573008433284386180789 6028741219540620411204449)
                  ·
                    refine ⟨4521555914655465308403337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6028741219540620411204449 4521555914655465308403337)
                    ·
                      refine ⟨3391166935991598981302503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4521555914655465308403337 3391166935991598981302503)
                      ·
                        rfl

theorem cell23_6604274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 5, 2, 2].length) (baseStart_6604274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604274 prefixEnd_6604274 := by exact prefixLift 6604274
  have htrace : WordTrace (prefixWord ++ tailWord_6604274) baseStart_6604274 baseEnd_6604274 := by
    simpa [prefixWord, tailWord_6604274, baseEnd_6604274] using wordTrace_append hprefix tailTrace_6604274
  have hstable : (prefixWord ++ tailWord_6604274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604274).length < 2 ^ (prefixWord ++ tailWord_6604274).sum := by decide
  have hdescent : baseEnd_6604274 < baseStart_6604274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604280 : List Nat := [2, 1, 2, 1, 1, 6, 3, 7]
def baseStart_6604280 : Nat := 118140960795 + 6604280 * 2 ^ 59
def prefixEnd_6604280 : Nat := 4983230072969 + 3 ^ 40 * 6604280 * 2
def baseEnd_6604280 : Nat := 125598889513908368808425

theorem tailTrace_6604280 : CollatzResearch.WordTrace tailWord_6604280 prefixEnd_6604280 125598889513908368808425 := by
  unfold tailWord_6604280
  simp only [CollatzResearch.WordTrace]
  refine ⟨120438940256914478035357147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160585253675885970713809529 120438940256914478035357147)
  ·
    refine ⟨180658410385371717053035721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120438940256914478035357147 180658410385371717053035721)
    ·
      refine ⟨135493807789028787789776791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180658410385371717053035721 135493807789028787789776791)
      ·
        refine ⟨203240711683543181684665187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135493807789028787789776791 203240711683543181684665187)
        ·
          refine ⟨304861067525314772526997781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203240711683543181684665187 304861067525314772526997781)
          ·
            refine ⟨14290362540249129962203021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 304861067525314772526997781 14290362540249129962203021)
            ·
              refine ⟨5358885952593423735826133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14290362540249129962203021 5358885952593423735826133)
              ·
                refine ⟨125598889513908368808425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5358885952593423735826133 125598889513908368808425)
                ·
                  rfl

theorem cell23_6604280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 7].length) (baseStart_6604280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604280 prefixEnd_6604280 := by exact prefixLift 6604280
  have htrace : WordTrace (prefixWord ++ tailWord_6604280) baseStart_6604280 baseEnd_6604280 := by
    simpa [prefixWord, tailWord_6604280, baseEnd_6604280] using wordTrace_append hprefix tailTrace_6604280
  have hstable : (prefixWord ++ tailWord_6604280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604280).length < 2 ^ (prefixWord ++ tailWord_6604280).sum := by decide
  have hdescent : baseEnd_6604280 < baseStart_6604280 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604301 : List Nat := [1, 7, 1, 1, 2, 1, 1, 1, 4, 4]
def baseStart_6604301 : Nat := 118140960795 + 6604301 * 2 ^ 59
def prefixEnd_6604301 : Nat := 4983230072969 + 3 ^ 40 * 6604301 * 2
def baseEnd_6604301 : Nat := 1130393599989756791888293

theorem tailTrace_6604301 : CollatzResearch.WordTrace tailWord_6604301 prefixEnd_6604301 1130393599989756791888293 := by
  unfold tailWord_6604301
  simp only [CollatzResearch.WordTrace]
  refine ⟨240878646446752876657228757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160585764297835251104819171 240878646446752876657228757)
  ·
    refine ⟨5645593276095770546653799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 240878646446752876657228757 5645593276095770546653799)
    ·
      refine ⟨8468389914143655819980699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5645593276095770546653799 8468389914143655819980699)
      ·
        refine ⟨12702584871215483729971049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8468389914143655819980699 12702584871215483729971049)
        ·
          refine ⟨9526938653411612797478287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12702584871215483729971049 9526938653411612797478287)
          ·
            refine ⟨14290407980117419196217431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9526938653411612797478287 14290407980117419196217431)
            ·
              refine ⟨21435611970176128794326147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14290407980117419196217431 21435611970176128794326147)
              ·
                refine ⟨32153417955264193191489221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21435611970176128794326147 32153417955264193191489221)
                ·
                  refine ⟨6028765866612036223404229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32153417955264193191489221 6028765866612036223404229)
                  ·
                    refine ⟨1130393599989756791888293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6028765866612036223404229 1130393599989756791888293)
                    ·
                      rfl

theorem cell23_6604301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_6604301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604301 prefixEnd_6604301 := by exact prefixLift 6604301
  have htrace : WordTrace (prefixWord ++ tailWord_6604301) baseStart_6604301 baseEnd_6604301 := by
    simpa [prefixWord, tailWord_6604301, baseEnd_6604301] using wordTrace_append hprefix tailTrace_6604301
  have hstable : (prefixWord ++ tailWord_6604301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604301).length < 2 ^ (prefixWord ++ tailWord_6604301).sum := by decide
  have hdescent : baseEnd_6604301 < baseStart_6604301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604307 : List Nat := [1, 1, 1, 2, 1, 7, 1, 1, 4, 1, 3]
def baseStart_6604307 : Nat := 118140960795 + 6604307 * 2 ^ 59
def prefixEnd_6604307 : Nat := 4983230072969 + 3 ^ 40 * 6604307 * 2
def baseEnd_6604307 : Nat := 3391183880853197352189851

theorem tailTrace_6604307 : CollatzResearch.WordTrace tailWord_6604307 prefixEnd_6604307 3391183880853197352189851 := by
  unfold tailWord_6604307
  simp only [CollatzResearch.WordTrace]
  refine ⟨240878865284731139681947175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160585910189820759787964783 240878865284731139681947175)
  ·
    refine ⟨361318297927096709522920763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240878865284731139681947175 361318297927096709522920763)
    ·
      refine ⟨541977446890645064284381145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361318297927096709522920763 541977446890645064284381145)
      ·
        refine ⟨406483085167983798213285859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 541977446890645064284381145 406483085167983798213285859)
        ·
          refine ⟨609724627751975697319928789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406483085167983798213285859 609724627751975697319928789)
          ·
            refine ⟨14290420962936930405935831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 609724627751975697319928789 14290420962936930405935831)
            ·
              refine ⟨21435631444405395608903747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14290420962936930405935831 21435631444405395608903747)
              ·
                refine ⟨32153447166608093413355621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21435631444405395608903747 32153447166608093413355621)
                ·
                  refine ⟨6028771343739017515004179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32153447166608093413355621 6028771343739017515004179)
                  ·
                    refine ⟨9043157015608526272506269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6028771343739017515004179 9043157015608526272506269)
                    ·
                      refine ⟨3391183880853197352189851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9043157015608526272506269 3391183880853197352189851)
                      ·
                        rfl

theorem cell23_6604307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 1, 4, 1, 3].length) (baseStart_6604307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604307 prefixEnd_6604307 := by exact prefixLift 6604307
  have htrace : WordTrace (prefixWord ++ tailWord_6604307) baseStart_6604307 baseEnd_6604307 := by
    simpa [prefixWord, tailWord_6604307, baseEnd_6604307] using wordTrace_append hprefix tailTrace_6604307
  have hstable : (prefixWord ++ tailWord_6604307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604307).length < 2 ^ (prefixWord ++ tailWord_6604307).sum := by decide
  have hdescent : baseEnd_6604307 < baseStart_6604307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604308 : List Nat := [2, 4, 3, 1, 2, 1, 2, 1, 3, 2, 2]
def baseStart_6604308 : Nat := 118140960795 + 6604308 * 2 ^ 59
def prefixEnd_6604308 : Nat := 4983230072969 + 3 ^ 40 * 6604308 * 2
def baseEnd_6604308 : Nat := 3391184394333851848277347

theorem tailTrace_6604308 : CollatzResearch.WordTrace tailWord_6604308 prefixEnd_6604308 3391184394333851848277347 := by
  unfold tailWord_6604308
  simp only [CollatzResearch.WordTrace]
  refine ⟨120439450878863758426366789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160585934505151677901822385 120439450878863758426366789)
  ·
    refine ⟨22582397039786954704943773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120439450878863758426366789 22582397039786954704943773)
    ·
      refine ⟨8468398889920108014353915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22582397039786954704943773 8468398889920108014353915)
      ·
        refine ⟨12702598334880162021530873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8468398889920108014353915 12702598334880162021530873)
        ·
          refine ⟨9526948751160121516148155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12702598334880162021530873 9526948751160121516148155)
          ·
            refine ⟨14290423126740182274222233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9526948751160121516148155 14290423126740182274222233)
            ·
              refine ⟨10717817345055136705666675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14290423126740182274222233 10717817345055136705666675)
              ·
                refine ⟨16076726017582705058500013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10717817345055136705666675 16076726017582705058500013)
                ·
                  refine ⟨6028772256593514396937505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16076726017582705058500013 6028772256593514396937505)
                  ·
                    refine ⟨4521579192445135797703129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6028772256593514396937505 4521579192445135797703129)
                    ·
                      refine ⟨3391184394333851848277347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4521579192445135797703129 3391184394333851848277347)
                      ·
                        rfl

theorem cell23_6604308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 2, 1, 3, 2, 2].length) (baseStart_6604308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604308 prefixEnd_6604308 := by exact prefixLift 6604308
  have htrace : WordTrace (prefixWord ++ tailWord_6604308) baseStart_6604308 baseEnd_6604308 := by
    simpa [prefixWord, tailWord_6604308, baseEnd_6604308] using wordTrace_append hprefix tailTrace_6604308
  have hstable : (prefixWord ++ tailWord_6604308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604308).length < 2 ^ (prefixWord ++ tailWord_6604308).sum := by decide
  have hdescent : baseEnd_6604308 < baseStart_6604308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604318 : List Nat := [4, 3, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_6604318 : Nat := 118140960795 + 6604318 * 2 ^ 59
def prefixEnd_6604318 : Nat := 4983230072969 + 3 ^ 40 * 6604318 * 2
def baseEnd_6604318 : Nat := 1130396509713465603050767

theorem tailTrace_6604318 : CollatzResearch.WordTrace tailWord_6604318 prefixEnd_6604318 1130396509713465603050767 := by
  unfold tailWord_6604318
  simp only [CollatzResearch.WordTrace]
  refine ⟨30109908310961411070074701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160586177658460859040398405 30109908310961411070074701)
  ·
    refine ⟨11291215616610529151278013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30109908310961411070074701 11291215616610529151278013)
    ·
      refine ⟨4234205856228948431729255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11291215616610529151278013 4234205856228948431729255)
      ·
        refine ⟨6351308784343422647593883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4234205856228948431729255 6351308784343422647593883)
        ·
          refine ⟨9526963176515133971390825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6351308784343422647593883 9526963176515133971390825)
          ·
            refine ⟨7145222382386350478543119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9526963176515133971390825 7145222382386350478543119)
            ·
              refine ⟨10717833573579525717814679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7145222382386350478543119 10717833573579525717814679)
              ·
                refine ⟨16076750360369288576722019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10717833573579525717814679 16076750360369288576722019)
                ·
                  refine ⟨24115125540553932865083029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16076750360369288576722019 24115125540553932865083029)
                  ·
                    refine ⟨1130396509713465603050767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24115125540553932865083029 1130396509713465603050767)
                    ·
                      rfl

theorem cell23_6604318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_6604318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604318 prefixEnd_6604318 := by exact prefixLift 6604318
  have htrace : WordTrace (prefixWord ++ tailWord_6604318) baseStart_6604318 baseEnd_6604318 := by
    simpa [prefixWord, tailWord_6604318, baseEnd_6604318] using wordTrace_append hprefix tailTrace_6604318
  have hstable : (prefixWord ++ tailWord_6604318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604318).length < 2 ^ (prefixWord ++ tailWord_6604318).sum := by decide
  have hdescent : baseEnd_6604318 < baseStart_6604318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604342 : List Nat := [5, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2]
def baseStart_6604342 : Nat := 118140960795 + 6604342 * 2 ^ 59
def prefixEnd_6604342 : Nat := 4983230072969 + 3 ^ 40 * 6604342 * 2
def baseEnd_6604342 : Nat := 3391201852676104715252191

theorem tailTrace_6604342 : CollatzResearch.WordTrace tailWord_6604342 prefixEnd_6604342 3391201852676104715252191 := by
  unfold tailWord_6604342
  simp only [CollatzResearch.WordTrace]
  refine ⟨15055008864975271291216955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160586761226402893772980853 15055008864975271291216955)
  ·
    refine ⟨22582513297462906936825433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15055008864975271291216955 22582513297462906936825433)
    ·
      refine ⟨16936884973097180202619075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22582513297462906936825433 16936884973097180202619075)
      ·
        refine ⟨25405327459645770303928613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16936884973097180202619075 25405327459645770303928613)
        ·
          refine ⟨4763498898683581931986615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25405327459645770303928613 4763498898683581931986615)
          ·
            refine ⟨7145248348025372897979923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4763498898683581931986615 7145248348025372897979923)
            ·
              refine ⟨10717872522038059346969885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7145248348025372897979923 10717872522038059346969885)
              ·
                refine ⟨4019202195764272255113707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10717872522038059346969885 4019202195764272255113707)
                ·
                  refine ⟨6028803293646408382670561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4019202195764272255113707 6028803293646408382670561)
                  ·
                    refine ⟨4521602470234806287002921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6028803293646408382670561 4521602470234806287002921)
                    ·
                      refine ⟨3391201852676104715252191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4521602470234806287002921 3391201852676104715252191)
                      ·
                        rfl

theorem cell23_6604342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 3, 1, 2, 2].length) (baseStart_6604342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604342 prefixEnd_6604342 := by exact prefixLift 6604342
  have htrace : WordTrace (prefixWord ++ tailWord_6604342) baseStart_6604342 baseEnd_6604342 := by
    simpa [prefixWord, tailWord_6604342, baseEnd_6604342] using wordTrace_append hprefix tailTrace_6604342
  have hstable : (prefixWord ++ tailWord_6604342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604342).length < 2 ^ (prefixWord ++ tailWord_6604342).sum := by decide
  have hdescent : baseEnd_6604342 < baseStart_6604342 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604363 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 9]
def baseStart_6604363 : Nat := 118140960795 + 6604363 * 2 ^ 59
def prefixEnd_6604363 : Nat := 4983230072969 + 3 ^ 40 * 6604363 * 2
def baseEnd_6604363 : Nat := 3391212635769849133089593

theorem tailTrace_6604363 : CollatzResearch.WordTrace tailWord_6604363 prefixEnd_6604363 3391212635769849133089593 := by
  unfold tailWord_6604363
  simp only [CollatzResearch.WordTrace]
  refine ⟨240880907772528261245985743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160587271848352174163990495 240880907772528261245985743)
  ·
    refine ⟨361321361658792391868978615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240880907772528261245985743 361321361658792391868978615)
    ·
      refine ⟨541982042488188587803467923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361321361658792391868978615 541982042488188587803467923)
      ·
        refine ⟨812973063732282881705201885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 541982042488188587803467923 812973063732282881705201885)
        ·
          refine ⟨304864898899606080639450707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 812973063732282881705201885 304864898899606080639450707)
          ·
            refine ⟨457297348349409120959176061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304864898899606080639450707 457297348349409120959176061)
            ·
              refine ⟨171486505631028420359691023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 457297348349409120959176061 171486505631028420359691023)
              ·
                refine ⟨257229758446542630539536535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171486505631028420359691023 257229758446542630539536535)
                ·
                  refine ⟨385844637669813945809304803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257229758446542630539536535 385844637669813945809304803)
                  ·
                    refine ⟨578766956504720918713957205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 385844637669813945809304803 578766956504720918713957205)
                    ·
                      refine ⟨3391212635769849133089593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 578766956504720918713957205 3391212635769849133089593)
                      ·
                        rfl

theorem cell23_6604363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 9].length) (baseStart_6604363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604363 prefixEnd_6604363 := by exact prefixLift 6604363
  have htrace : WordTrace (prefixWord ++ tailWord_6604363) baseStart_6604363 baseEnd_6604363 := by
    simpa [prefixWord, tailWord_6604363, baseEnd_6604363] using wordTrace_append hprefix tailTrace_6604363
  have hstable : (prefixWord ++ tailWord_6604363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604363).length < 2 ^ (prefixWord ++ tailWord_6604363).sum := by decide
  have hdescent : baseEnd_6604363 < baseStart_6604363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604364 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 4, 2, 2]
def baseStart_6604364 : Nat := 118140960795 + 6604364 * 2 ^ 59
def prefixEnd_6604364 : Nat := 4983230072969 + 3 ^ 40 * 6604364 * 2
def baseEnd_6604364 : Nat := 3391213149250503629177089

theorem tailTrace_6604364 : CollatzResearch.WordTrace tailWord_6604364 prefixEnd_6604364 3391213149250503629177089 := by
  unfold tailWord_6604364
  simp only [CollatzResearch.WordTrace]
  refine ⟨120440472122762319208386073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160587296163683092277848097 120440472122762319208386073)
  ·
    refine ⟨90330354092071739406289555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120440472122762319208386073 90330354092071739406289555)
    ·
      refine ⟨135495531138107609109434333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90330354092071739406289555 135495531138107609109434333)
      ·
        refine ⟨50810824176790353416037875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135495531138107609109434333 50810824176790353416037875)
        ·
          refine ⟨76216236265185530124056813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50810824176790353416037875 76216236265185530124056813)
          ·
            refine ⟨28581088599444573796521305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76216236265185530124056813 28581088599444573796521305)
            ·
              refine ⟨21435816449583430347390979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28581088599444573796521305 21435816449583430347390979)
              ·
                refine ⟨32153724674375145521086469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21435816449583430347390979 32153724674375145521086469)
                ·
                  refine ⟨6028823376445339785203713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32153724674375145521086469 6028823376445339785203713)
                  ·
                    refine ⟨4521617532334004838902785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6028823376445339785203713 4521617532334004838902785)
                    ·
                      refine ⟨3391213149250503629177089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4521617532334004838902785 3391213149250503629177089)
                      ·
                        rfl

theorem cell23_6604364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_6604364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604364 prefixEnd_6604364 := by exact prefixLift 6604364
  have htrace : WordTrace (prefixWord ++ tailWord_6604364) baseStart_6604364 baseEnd_6604364 := by
    simpa [prefixWord, tailWord_6604364, baseEnd_6604364] using wordTrace_append hprefix tailTrace_6604364
  have hstable : (prefixWord ++ tailWord_6604364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604364).length < 2 ^ (prefixWord ++ tailWord_6604364).sum := by decide
  have hdescent : baseEnd_6604364 < baseStart_6604364 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604417 : List Nat := [1, 2, 4, 2, 1, 2, 2, 2, 2, 5]
def baseStart_6604417 : Nat := 118140960795 + 6604417 * 2 ^ 59
def prefixEnd_6604417 : Nat := 4983230072969 + 3 ^ 40 * 6604417 * 2
def baseEnd_6604417 : Nat := 1130413454575063973938115

theorem tailTrace_6604417 : CollatzResearch.WordTrace tailWord_6604417 prefixEnd_6604417 1130413454575063973938115 := by
  unfold tailWord_6604417
  simp only [CollatzResearch.WordTrace]
  refine ⟨240882877314332628468451505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160588584876221752312301003 240882877314332628468451505)
  ·
    refine ⟨180662157985749471351338629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240882877314332628468451505 180662157985749471351338629)
    ·
      refine ⟨33874154622328025878375993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 180662157985749471351338629 33874154622328025878375993)
      ·
        refine ⟨25405615966746019408781995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33874154622328025878375993 25405615966746019408781995)
        ·
          refine ⟨38108423950119029113172993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25405615966746019408781995 38108423950119029113172993)
          ·
            refine ⟨28581317962589271834879745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38108423950119029113172993 28581317962589271834879745)
            ·
              refine ⟨21435988471941953876159809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28581317962589271834879745 21435988471941953876159809)
              ·
                refine ⟨16076991353956465407119857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21435988471941953876159809 16076991353956465407119857)
                ·
                  refine ⟨12057743515467349055339893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16076991353956465407119857 12057743515467349055339893)
                  ·
                    refine ⟨1130413454575063973938115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12057743515467349055339893 1130413454575063973938115)
                    ·
                      rfl

theorem cell23_6604417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_6604417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604417 prefixEnd_6604417 := by exact prefixLift 6604417
  have htrace : WordTrace (prefixWord ++ tailWord_6604417) baseStart_6604417 baseEnd_6604417 := by
    simpa [prefixWord, tailWord_6604417, baseEnd_6604417] using wordTrace_append hprefix tailTrace_6604417
  have hstable : (prefixWord ++ tailWord_6604417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604417).length < 2 ^ (prefixWord ++ tailWord_6604417).sum := by decide
  have hdescent : baseEnd_6604417 < baseStart_6604417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604464 : List Nat := [2, 1, 1, 1, 2, 1, 5, 5, 1, 4]
def baseStart_6604464 : Nat := 118140960795 + 6604464 * 2 ^ 59
def prefixEnd_6604464 : Nat := 4983230072969 + 3 ^ 40 * 6604464 * 2
def baseEnd_6604464 : Nat := 1130421499105317745975543

theorem tailTrace_6604464 : CollatzResearch.WordTrace tailWord_6604464 prefixEnd_6604464 1130421499105317745975543 := by
  unfold tailWord_6604464
  simp only [CollatzResearch.WordTrace]
  refine ⟨120442295772581177747706223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160589727696774903663608297 120442295772581177747706223)
  ·
    refine ⟨180663443658871766621559335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120442295772581177747706223 180663443658871766621559335)
    ·
      refine ⟨270995165488307649932339003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180663443658871766621559335 270995165488307649932339003)
      ·
        refine ⟨406492748232461474898508505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270995165488307649932339003 406492748232461474898508505)
        ·
          refine ⟨304869561174346106173881379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406492748232461474898508505 304869561174346106173881379)
          ·
            refine ⟨457304341761519159260822069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304869561174346106173881379 457304341761519159260822069)
            ·
              refine ⟨42872282040142421180702069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 457304341761519159260822069 42872282040142421180702069)
              ·
                refine ⟨4019276441263351985690819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42872282040142421180702069 4019276441263351985690819)
                ·
                  refine ⟨6028914661895027978536229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4019276441263351985690819 6028914661895027978536229)
                  ·
                    refine ⟨1130421499105317745975543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6028914661895027978536229 1130421499105317745975543)
                    ·
                      rfl

theorem cell23_6604464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 5, 1, 4].length) (baseStart_6604464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604464 prefixEnd_6604464 := by exact prefixLift 6604464
  have htrace : WordTrace (prefixWord ++ tailWord_6604464) baseStart_6604464 baseEnd_6604464 := by
    simpa [prefixWord, tailWord_6604464, baseEnd_6604464] using wordTrace_append hprefix tailTrace_6604464
  have hstable : (prefixWord ++ tailWord_6604464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604464).length < 2 ^ (prefixWord ++ tailWord_6604464).sum := by decide
  have hdescent : baseEnd_6604464 < baseStart_6604464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604480 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 8]
def baseStart_6604480 : Nat := 118140960795 + 6604480 * 2 ^ 59
def prefixEnd_6604480 : Nat := 4983230072969 + 3 ^ 40 * 6604480 * 2
def baseEnd_6604480 : Nat := 3391272713006425175326555

theorem tailTrace_6604480 : CollatzResearch.WordTrace tailWord_6604480 prefixEnd_6604480 3391272713006425175326555 := by
  unfold tailWord_6604480
  simp only [CollatzResearch.WordTrace]
  refine ⟨120442587556552195113997447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160590116742069593485329929 120442587556552195113997447)
  ·
    refine ⟨180663881334828292670996171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120442587556552195113997447 180663881334828292670996171)
    ·
      refine ⟨270995822002242439006494257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180663881334828292670996171 270995822002242439006494257)
      ·
        refine ⟨203246866501681829254870693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 270995822002242439006494257 203246866501681829254870693)
        ·
          refine ⟨38108787469065342985288255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203246866501681829254870693 38108787469065342985288255)
          ·
            refine ⟨57163181203598014477932383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38108787469065342985288255 57163181203598014477932383)
            ·
              refine ⟨85744771805397021716898575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57163181203598014477932383 85744771805397021716898575)
              ·
                refine ⟨128617157708095532575347863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85744771805397021716898575 128617157708095532575347863)
                ·
                  refine ⟨192925736562143298863021795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128617157708095532575347863 192925736562143298863021795)
                  ·
                    refine ⟨289388604843214948294532693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 192925736562143298863021795 289388604843214948294532693)
                    ·
                      refine ⟨3391272713006425175326555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 289388604843214948294532693 3391272713006425175326555)
                      ·
                        rfl

theorem cell23_6604480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_6604480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604480 prefixEnd_6604480 := by exact prefixLift 6604480
  have htrace : WordTrace (prefixWord ++ tailWord_6604480) baseStart_6604480 baseEnd_6604480 := by
    simpa [prefixWord, tailWord_6604480, baseEnd_6604480] using wordTrace_append hprefix tailTrace_6604480
  have hstable : (prefixWord ++ tailWord_6604480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604480).length < 2 ^ (prefixWord ++ tailWord_6604480).sum := by decide
  have hdescent : baseEnd_6604480 < baseStart_6604480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604494 : List Nat := [4, 1, 1, 1, 3, 1, 5, 1, 6]
def baseStart_6604494 : Nat := 118140960795 + 6604494 * 2 ^ 59
def prefixEnd_6604494 : Nat := 4983230072969 + 3 ^ 40 * 6604494 * 2
def baseEnd_6604494 : Nat := 376808877970620902283499

theorem tailTrace_6604494 : CollatzResearch.WordTrace tailWord_6604494 prefixEnd_6604494 376808877970620902283499 := by
  unfold tailWord_6604494
  simp only [CollatzResearch.WordTrace]
  refine ⟨30110710716881708827375567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160590457156702447079336357 30110710716881708827375567)
  ·
    refine ⟨45166066075322563241063351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30110710716881708827375567 45166066075322563241063351)
    ·
      refine ⟨67749099112983844861595027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45166066075322563241063351 67749099112983844861595027)
      ·
        refine ⟨101623648669475767292392541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67749099112983844861595027 101623648669475767292392541)
        ·
          refine ⟨38108868251053412734647203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101623648669475767292392541 38108868251053412734647203)
          ·
            refine ⟨57163302376580119101970805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38108868251053412734647203 57163302376580119101970805)
            ·
              refine ⟨5359059597804386165809763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57163302376580119101970805 5359059597804386165809763)
              ·
                refine ⟨8038589396706579248714645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5359059597804386165809763 8038589396706579248714645)
                ·
                  refine ⟨376808877970620902283499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8038589396706579248714645 376808877970620902283499)
                  ·
                    rfl

theorem cell23_6604494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 5, 1, 6].length) (baseStart_6604494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604494 prefixEnd_6604494 := by exact prefixLift 6604494
  have htrace : WordTrace (prefixWord ++ tailWord_6604494) baseStart_6604494 baseEnd_6604494 := by
    simpa [prefixWord, tailWord_6604494, baseEnd_6604494] using wordTrace_append hprefix tailTrace_6604494
  have hstable : (prefixWord ++ tailWord_6604494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604494).length < 2 ^ (prefixWord ++ tailWord_6604494).sum := by decide
  have hdescent : baseEnd_6604494 < baseStart_6604494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604504 : List Nat := [2, 1, 2, 2, 3, 1, 1, 4, 3, 1, 3]
def baseStart_6604504 : Nat := 118140960795 + 6604504 * 2 ^ 59
def prefixEnd_6604504 : Nat := 4983230072969 + 3 ^ 40 * 6604504 * 2
def baseEnd_6604504 : Nat := 3391285036542133081426445

theorem tailTrace_6604504 : CollatzResearch.WordTrace tailWord_6604504 prefixEnd_6604504 3391285036542133081426445 := by
  unfold tailWord_6604504
  simp only [CollatzResearch.WordTrace]
  refine ⟨120443025232508721163434283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160590700310011628217912377 120443025232508721163434283)
  ·
    refine ⟨180664537848763081745151425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120443025232508721163434283 180664537848763081745151425)
    ·
      refine ⟨135498403386572311308863569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180664537848763081745151425 135498403386572311308863569)
      ·
        refine ⟨101623802539929233481647677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135498403386572311308863569 101623802539929233481647677)
        ·
          refine ⟨38108925952473462555617879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101623802539929233481647677 38108925952473462555617879)
          ·
            refine ⟨57163388928710193833426819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38108925952473462555617879 57163388928710193833426819)
            ·
              refine ⟨85745083393065290750140229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57163388928710193833426819 85745083393065290750140229)
              ·
                refine ⟨16077203136199742015651293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85745083393065290750140229 16077203136199742015651293)
                ·
                  refine ⟨6028951176074903255869235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16077203136199742015651293 6028951176074903255869235)
                  ·
                    refine ⟨9043426764112354883803853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6028951176074903255869235 9043426764112354883803853)
                    ·
                      refine ⟨3391285036542133081426445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9043426764112354883803853 3391285036542133081426445)
                      ·
                        rfl

theorem cell23_6604504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_6604504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604504 prefixEnd_6604504 := by exact prefixLift 6604504
  have htrace : WordTrace (prefixWord ++ tailWord_6604504) baseStart_6604504 baseEnd_6604504 := by
    simpa [prefixWord, tailWord_6604504, baseEnd_6604504] using wordTrace_append hprefix tailTrace_6604504
  have hstable : (prefixWord ++ tailWord_6604504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604504).length < 2 ^ (prefixWord ++ tailWord_6604504).sum := by decide
  have hdescent : baseEnd_6604504 < baseStart_6604504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604515 : List Nat := [1, 1, 1, 7, 3, 1, 1, 3, 1, 4]
def baseStart_6604515 : Nat := 118140960795 + 6604515 * 2 ^ 59
def prefixEnd_6604515 : Nat := 4983230072969 + 3 ^ 40 * 6604515 * 2
def baseEnd_6604515 : Nat := 1130430228276444179462965

theorem tailTrace_6604515 : CollatzResearch.WordTrace tailWord_6604515 prefixEnd_6604515 1130430228276444179462965 := by
  unfold tailWord_6604515
  simp only [CollatzResearch.WordTrace]
  refine ⟨240886451667977591205518999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160590967778651727470345999 240886451667977591205518999)
  ·
    refine ⟨361329677501966386808278499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240886451667977591205518999 361329677501966386808278499)
    ·
      refine ⟨541994516252949580212417749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361329677501966386808278499 541994516252949580212417749)
      ·
        refine ⟨12702996474678505786228541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 541994516252949580212417749 12702996474678505786228541)
        ·
          refine ⟨4763623678004439669835703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12702996474678505786228541 4763623678004439669835703)
          ·
            refine ⟨7145435517006659504753555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4763623678004439669835703 7145435517006659504753555)
            ·
              refine ⟨10718153275509989257130333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7145435517006659504753555 10718153275509989257130333)
              ·
                refine ⟨4019307478316245971423875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10718153275509989257130333 4019307478316245971423875)
                ·
                  refine ⟨6028961217474368957135813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4019307478316245971423875 6028961217474368957135813)
                  ·
                    refine ⟨1130430228276444179462965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6028961217474368957135813 1130430228276444179462965)
                    ·
                      rfl

theorem cell23_6604515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 3, 1, 4].length) (baseStart_6604515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604515 prefixEnd_6604515 := by exact prefixLift 6604515
  have htrace : WordTrace (prefixWord ++ tailWord_6604515) baseStart_6604515 baseEnd_6604515 := by
    simpa [prefixWord, tailWord_6604515, baseEnd_6604515] using wordTrace_append hprefix tailTrace_6604515
  have hstable : (prefixWord ++ tailWord_6604515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604515).length < 2 ^ (prefixWord ++ tailWord_6604515).sum := by decide
  have hdescent : baseEnd_6604515 < baseStart_6604515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604532 : List Nat := [2, 6, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_6604532 : Nat := 118140960795 + 6604532 * 2 ^ 59
def prefixEnd_6604532 : Nat := 4983230072969 + 3 ^ 40 * 6604532 * 2
def baseEnd_6604532 : Nat := 1130433138000152990625439

theorem tailTrace_6604532 : CollatzResearch.WordTrace tailWord_6604532 prefixEnd_6604532 1130433138000152990625439 := by
  unfold tailWord_6604532
  simp only [CollatzResearch.WordTrace]
  refine ⟨120443535854458001554443925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160591381139277335405925233 120443535854458001554443925)
  ·
    refine ⟨5645790743177718822864559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120443535854458001554443925 5645790743177718822864559)
    ·
      refine ⟨8468686114766578234296839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5645790743177718822864559 8468686114766578234296839)
      ·
        refine ⟨12703029172149867351445259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8468686114766578234296839 12703029172149867351445259)
        ·
          refine ⟨19054543758224801027167889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12703029172149867351445259 19054543758224801027167889)
          ·
            refine ⟨14290907818668600770375917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19054543758224801027167889 14290907818668600770375917)
            ·
              refine ⟨5359090432000725288890969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14290907818668600770375917 5359090432000725288890969)
              ·
                refine ⟨4019317824000543966668227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5359090432000725288890969 4019317824000543966668227)
                ·
                  refine ⟨6028976736000815950002341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4019317824000543966668227 6028976736000815950002341)
                  ·
                    refine ⟨1130433138000152990625439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6028976736000815950002341 1130433138000152990625439)
                    ·
                      rfl

theorem cell23_6604532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_6604532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604532 prefixEnd_6604532 := by exact prefixLift 6604532
  have htrace : WordTrace (prefixWord ++ tailWord_6604532) baseStart_6604532 baseEnd_6604532 := by
    simpa [prefixWord, tailWord_6604532, baseEnd_6604532] using wordTrace_append hprefix tailTrace_6604532
  have hstable : (prefixWord ++ tailWord_6604532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604532).length < 2 ^ (prefixWord ++ tailWord_6604532).sum := by decide
  have hdescent : baseEnd_6604532 < baseStart_6604532 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604547 : List Nat := [1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 5]
def baseStart_6604547 : Nat := 118140960795 + 6604547 * 2 ^ 59
def prefixEnd_6604547 : Nat := 4983230072969 + 3 ^ 40 * 6604547 * 2
def baseEnd_6604547 : Nat := 3391307116210276413188747

theorem tailTrace_6604547 : CollatzResearch.WordTrace tailWord_6604547 prefixEnd_6604547 3391307116210276413188747 := by
  unfold tailWord_6604547
  simp only [CollatzResearch.WordTrace]
  refine ⟨240887618803861660670683895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160591745869241107113789263 240887618803861660670683895)
  ·
    refine ⟨361331428205792491006025843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240887618803861660670683895 361331428205792491006025843)
    ·
      refine ⟨541997142308688736509038765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361331428205792491006025843 541997142308688736509038765)
      ·
        refine ⟨203248928365758276190889537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 541997142308688736509038765 203248928365758276190889537)
        ·
          refine ⟨152436696274318707143167153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203248928365758276190889537 152436696274318707143167153)
          ·
            refine ⟨114327522205739030357375365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152436696274318707143167153 114327522205739030357375365)
            ·
              refine ⟨21436410413576068192007881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114327522205739030357375365 21436410413576068192007881)
              ·
                refine ⟨16077307810182051144005911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21436410413576068192007881 16077307810182051144005911)
                ·
                  refine ⟨24115961715273076716008867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16077307810182051144005911 24115961715273076716008867)
                  ·
                    refine ⟨36173942572909615074013301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24115961715273076716008867 36173942572909615074013301)
                    ·
                      refine ⟨3391307116210276413188747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36173942572909615074013301 3391307116210276413188747)
                      ·
                        rfl

theorem cell23_6604547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_6604547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604547 prefixEnd_6604547 := by exact prefixLift 6604547
  have htrace : WordTrace (prefixWord ++ tailWord_6604547) baseStart_6604547 baseEnd_6604547 := by
    simpa [prefixWord, tailWord_6604547, baseEnd_6604547] using wordTrace_append hprefix tailTrace_6604547
  have hstable : (prefixWord ++ tailWord_6604547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604547).length < 2 ^ (prefixWord ++ tailWord_6604547).sum := by decide
  have hdescent : baseEnd_6604547 < baseStart_6604547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604567 : List Nat := [1, 1, 3, 4, 2, 1, 2, 9]
def baseStart_6604567 : Nat := 118140960795 + 6604567 * 2 ^ 59
def prefixEnd_6604567 : Nat := 4983230072969 + 3 ^ 40 * 6604567 * 2
def baseEnd_6604567 : Nat := 125604347623087642034765

theorem tailTrace_6604567 : CollatzResearch.WordTrace tailWord_6604567 prefixEnd_6604567 125604347623087642034765 := by
  unfold tailWord_6604567
  simp only [CollatzResearch.WordTrace]
  refine ⟨240888348263789204086411955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160592232175859469390941303 240888348263789204086411955)
  ·
    refine ⟨361332522395683806129617933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240888348263789204086411955 361332522395683806129617933)
    ·
      refine ⟨135499695898381427298606725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361332522395683806129617933 135499695898381427298606725)
      ·
        refine ⟨25406192980946517618488761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135499695898381427298606725 25406192980946517618488761)
        ·
          refine ⟨19054644735709888213866571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25406192980946517618488761 19054644735709888213866571)
          ·
            refine ⟨28581967103564832320799857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19054644735709888213866571 28581967103564832320799857)
            ·
              refine ⟨21436475327673624240599893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28581967103564832320799857 21436475327673624240599893)
              ·
                refine ⟨125604347623087642034765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21436475327673624240599893 125604347623087642034765)
                ·
                  rfl

theorem cell23_6604567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 9].length) (baseStart_6604567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604567 prefixEnd_6604567 := by exact prefixLift 6604567
  have htrace : WordTrace (prefixWord ++ tailWord_6604567) baseStart_6604567 baseEnd_6604567 := by
    simpa [prefixWord, tailWord_6604567, baseEnd_6604567] using wordTrace_append hprefix tailTrace_6604567
  have hstable : (prefixWord ++ tailWord_6604567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604567).length < 2 ^ (prefixWord ++ tailWord_6604567).sum := by decide
  have hdescent : baseEnd_6604567 < baseStart_6604567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604595 : List Nat := [1, 1, 1, 2, 7, 1, 1, 4, 1, 2, 2]
def baseStart_6604595 : Nat := 118140960795 + 6604595 * 2 ^ 59
def prefixEnd_6604595 : Nat := 4983230072969 + 3 ^ 40 * 6604595 * 2
def baseEnd_6604595 : Nat := 3391331763281692225388527

theorem tailTrace_6604595 : CollatzResearch.WordTrace tailWord_6604595 prefixEnd_6604595 3391331763281692225388527 := by
  unfold tailWord_6604595
  simp only [CollatzResearch.WordTrace]
  refine ⟨240889369507687764868431239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160592913005125176578954159 240889369507687764868431239)
  ·
    refine ⟨361334054261531647302646859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240889369507687764868431239 361334054261531647302646859)
    ·
      refine ⟨542001081392297470953970289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361334054261531647302646859 542001081392297470953970289)
      ·
        refine ⟨406500811044223103215477717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542001081392297470953970289 406500811044223103215477717)
        ·
          refine ⟨9527362758848978981612759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 406500811044223103215477717 9527362758848978981612759)
          ·
            refine ⟨14291044138273468472419139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9527362758848978981612759 14291044138273468472419139)
            ·
              refine ⟨21436566207410202708628709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14291044138273468472419139 21436566207410202708628709)
              ·
                refine ⟨4019356163889413007867883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21436566207410202708628709 4019356163889413007867883)
                ·
                  refine ⟨6029034245834119511801825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4019356163889413007867883 6029034245834119511801825)
                  ·
                    refine ⟨4521775684375589633851369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6029034245834119511801825 4521775684375589633851369)
                    ·
                      refine ⟨3391331763281692225388527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4521775684375589633851369 3391331763281692225388527)
                      ·
                        rfl

theorem cell23_6604595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 4, 1, 2, 2].length) (baseStart_6604595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604595 prefixEnd_6604595 := by exact prefixLift 6604595
  have htrace : WordTrace (prefixWord ++ tailWord_6604595) baseStart_6604595 baseEnd_6604595 := by
    simpa [prefixWord, tailWord_6604595, baseEnd_6604595] using wordTrace_append hprefix tailTrace_6604595
  have hstable : (prefixWord ++ tailWord_6604595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604595).length < 2 ^ (prefixWord ++ tailWord_6604595).sum := by decide
  have hdescent : baseEnd_6604595 < baseStart_6604595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604601 : List Nat := [1, 2, 1, 7, 1, 2, 1, 8]
def baseStart_6604601 : Nat := 118140960795 + 6604601 * 2 ^ 59
def prefixEnd_6604601 : Nat := 4983230072969 + 3 ^ 40 * 6604601 * 2
def baseEnd_6604601 : Nat := 125604994228356266737537

theorem tailTrace_6604601 : CollatzResearch.WordTrace tailWord_6604601 prefixEnd_6604601 125604994228356266737537 := by
  unfold tailWord_6604601
  simp only [CollatzResearch.WordTrace]
  refine ⟨240889588345666027893149657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160593058897110685262099771 240889588345666027893149657)
  ·
    refine ⟨180667191259249520919862243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240889588345666027893149657 180667191259249520919862243)
    ·
      refine ⟨271000786888874281379793365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180667191259249520919862243 271000786888874281379793365)
      ·
        refine ⟨6351580942707990969838907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 271000786888874281379793365 6351580942707990969838907)
        ·
          refine ⟨9527371414061986454758361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6351580942707990969838907 9527371414061986454758361)
          ·
            refine ⟨7145528560546489841068771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9527371414061986454758361 7145528560546489841068771)
            ·
              refine ⟨10718292840819734761603157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7145528560546489841068771 10718292840819734761603157)
              ·
                refine ⟨125604994228356266737537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10718292840819734761603157 125604994228356266737537)
                ·
                  rfl

theorem cell23_6604601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 8].length) (baseStart_6604601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604601 prefixEnd_6604601 := by exact prefixLift 6604601
  have htrace : WordTrace (prefixWord ++ tailWord_6604601) baseStart_6604601 baseEnd_6604601 := by
    simpa [prefixWord, tailWord_6604601, baseEnd_6604601] using wordTrace_append hprefix tailTrace_6604601
  have hstable : (prefixWord ++ tailWord_6604601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604601).length < 2 ^ (prefixWord ++ tailWord_6604601).sum := by decide
  have hdescent : baseEnd_6604601 < baseStart_6604601 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604611 : List Nat := [1, 1, 1, 3, 1, 5, 2, 3, 2, 1, 3]
def baseStart_6604611 : Nat := 118140960795 + 6604611 * 2 ^ 59
def prefixEnd_6604611 : Nat := 4983230072969 + 3 ^ 40 * 6604611 * 2
def baseEnd_6604611 : Nat := 3391339978972164162788453

theorem tailTrace_6604611 : CollatzResearch.WordTrace tailWord_6604611 prefixEnd_6604611 3391339978972164162788453 := by
  unfold tailWord_6604611
  simp only [CollatzResearch.WordTrace]
  refine ⟨240889953075629799601013687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160593302050419866400675791 240889953075629799601013687)
  ·
    refine ⟨361334929613444699401520531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240889953075629799601013687 361334929613444699401520531)
    ·
      refine ⟨542002394420167049102280797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361334929613444699401520531 542002394420167049102280797)
      ·
        refine ⟨203250897907562643413355299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 542002394420167049102280797 203250897907562643413355299)
        ·
          refine ⟨304876346861343965120032949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203250897907562643413355299 304876346861343965120032949)
          ·
            refine ⟨28582157518250996730003089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 304876346861343965120032949 28582157518250996730003089)
            ·
              refine ⟨21436618138688247547502317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28582157518250996730003089 21436618138688247547502317)
              ·
                refine ⟨8038731802008092830313369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21436618138688247547502317 8038731802008092830313369)
                ·
                  refine ⟨6029048851506069622735027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8038731802008092830313369 6029048851506069622735027)
                  ·
                    refine ⟨9043573277259104434102541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6029048851506069622735027 9043573277259104434102541)
                    ·
                      refine ⟨3391339978972164162788453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9043573277259104434102541 3391339978972164162788453)
                      ·
                        rfl

theorem cell23_6604611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_6604611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604611 prefixEnd_6604611 := by exact prefixLift 6604611
  have htrace : WordTrace (prefixWord ++ tailWord_6604611) baseStart_6604611 baseEnd_6604611 := by
    simpa [prefixWord, tailWord_6604611, baseEnd_6604611] using wordTrace_append hprefix tailTrace_6604611
  have hstable : (prefixWord ++ tailWord_6604611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604611).length < 2 ^ (prefixWord ++ tailWord_6604611).sum := by decide
  have hdescent : baseEnd_6604611 < baseStart_6604611 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604617 : List Nat := [1, 2, 1, 1, 2, 4, 1, 2, 2, 3, 4]
def baseStart_6604617 : Nat := 118140960795 + 6604617 * 2 ^ 59
def prefixEnd_6604617 : Nat := 4983230072969 + 3 ^ 40 * 6604617 * 2
def baseEnd_6604617 : Nat := 3391343059856091139313425

theorem tailTrace_6604617 : CollatzResearch.WordTrace tailWord_6604617 prefixEnd_6604617 3391343059856091139313425 := by
  unfold tailWord_6604617
  simp only [CollatzResearch.WordTrace]
  refine ⟨240890171913608062625732105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160593447942405375083821403 240890171913608062625732105)
  ·
    refine ⟨180667628935206046969299079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240890171913608062625732105 180667628935206046969299079)
    ·
      refine ⟨271001443402809070453948619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180667628935206046969299079 271001443402809070453948619)
      ·
        refine ⟨406502165104213605680922929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271001443402809070453948619 406502165104213605680922929)
        ·
          refine ⟨304876623828160204260692197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406502165104213605680922929 304876623828160204260692197)
          ·
            refine ⟨57164366967780038298879787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304876623828160204260692197 57164366967780038298879787)
            ·
              refine ⟨85746550451670057448319681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57164366967780038298879787 85746550451670057448319681)
              ·
                refine ⟨64309912838752543086239761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85746550451670057448319681 64309912838752543086239761)
                ·
                  refine ⟨48232434629064407314679821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64309912838752543086239761 48232434629064407314679821)
                  ·
                    refine ⟨18087162985899152743004933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48232434629064407314679821 18087162985899152743004933)
                    ·
                      refine ⟨3391343059856091139313425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18087162985899152743004933 3391343059856091139313425)
                      ·
                        rfl

theorem cell23_6604617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 3, 4].length) (baseStart_6604617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604617 prefixEnd_6604617 := by exact prefixLift 6604617
  have htrace : WordTrace (prefixWord ++ tailWord_6604617) baseStart_6604617 baseEnd_6604617 := by
    simpa [prefixWord, tailWord_6604617, baseEnd_6604617] using wordTrace_append hprefix tailTrace_6604617
  have hstable : (prefixWord ++ tailWord_6604617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604617).length < 2 ^ (prefixWord ++ tailWord_6604617).sum := by decide
  have hdescent : baseEnd_6604617 < baseStart_6604617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604662 : List Nat := [5, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_6604662 : Nat := 118140960795 + 6604662 * 2 ^ 59
def prefixEnd_6604662 : Nat := 4983230072969 + 3 ^ 40 * 6604662 * 2
def baseEnd_6604662 : Nat := 3391366166485543463250719

theorem tailTrace_6604662 : CollatzResearch.WordTrace tailWord_6604662 prefixEnd_6604662 3391366166485543463250719 := by
  unfold tailWord_6604662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15055738324902814706945015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160594542132296690207413493 15055738324902814706945015)
  ·
    refine ⟨22583607487354222060417523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15055738324902814706945015 22583607487354222060417523)
    ·
      refine ⟨33875411231031333090626285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22583607487354222060417523 33875411231031333090626285)
      ·
        refine ⟨12703279211636749908984857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33875411231031333090626285 12703279211636749908984857)
        ·
          refine ⟨9527459408727562431738643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12703279211636749908984857 9527459408727562431738643)
          ·
            refine ⟨14291189113091343647607965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9527459408727562431738643 14291189113091343647607965)
            ·
              refine ⟨5359195917409253867852987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14291189113091343647607965 5359195917409253867852987)
              ·
                refine ⟨8038793876113880801779481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5359195917409253867852987 8038793876113880801779481)
                ·
                  refine ⟨6029095407085410601334611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8038793876113880801779481 6029095407085410601334611)
                  ·
                    refine ⟨9043643110628115902001917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6029095407085410601334611 9043643110628115902001917)
                    ·
                      refine ⟨3391366166485543463250719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9043643110628115902001917 3391366166485543463250719)
                      ·
                        rfl

theorem cell23_6604662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_6604662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604662 prefixEnd_6604662 := by exact prefixLift 6604662
  have htrace : WordTrace (prefixWord ++ tailWord_6604662) baseStart_6604662 baseEnd_6604662 := by
    simpa [prefixWord, tailWord_6604662, baseEnd_6604662] using wordTrace_append hprefix tailTrace_6604662
  have hstable : (prefixWord ++ tailWord_6604662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604662).length < 2 ^ (prefixWord ++ tailWord_6604662).sum := by decide
  have hdescent : baseEnd_6604662 < baseStart_6604662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604708 : List Nat := [2, 3, 1, 2, 1, 4, 3, 2, 5]
def baseStart_6604708 : Nat := 118140960795 + 6604708 * 2 ^ 59
def prefixEnd_6604708 : Nat := 4983230072969 + 3 ^ 40 * 6604708 * 2
def baseEnd_6604708 : Nat := 376821087399516698141723

theorem tailTrace_6604708 : CollatzResearch.WordTrace tailWord_6604708 prefixEnd_6604708 376821087399516698141723 := by
  unfold tailWord_6604708
  simp only [CollatzResearch.WordTrace]
  refine ⟨120446745478139192583647389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160595660637518923444863185 120446745478139192583647389)
  ·
    refine ⟨45167529554302197218867771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120446745478139192583647389 45167529554302197218867771)
    ·
      refine ⟨67751294331453295828301657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45167529554302197218867771 67751294331453295828301657)
      ·
        refine ⟨50813470748589971871226243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67751294331453295828301657 50813470748589971871226243)
        ·
          refine ⟨76220206122884957806839365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50813470748589971871226243 76220206122884957806839365)
          ·
            refine ⟨14291288648040929588782381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76220206122884957806839365 14291288648040929588782381)
            ·
              refine ⟨5359233243015348595793393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14291288648040929588782381 5359233243015348595793393)
              ·
                refine ⟨4019424932261511446845045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5359233243015348595793393 4019424932261511446845045)
                ·
                  refine ⟨376821087399516698141723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4019424932261511446845045 376821087399516698141723)
                  ·
                    rfl

theorem cell23_6604708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 5].length) (baseStart_6604708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604708 prefixEnd_6604708 := by exact prefixLift 6604708
  have htrace : WordTrace (prefixWord ++ tailWord_6604708) baseStart_6604708 baseEnd_6604708 := by
    simpa [prefixWord, tailWord_6604708, baseEnd_6604708] using wordTrace_append hprefix tailTrace_6604708
  have hstable : (prefixWord ++ tailWord_6604708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604708).length < 2 ^ (prefixWord ++ tailWord_6604708).sum := by decide
  have hdescent : baseEnd_6604708 < baseStart_6604708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604811 : List Nat := [1, 1, 1, 1, 6, 1, 3, 3, 1, 5]
def baseStart_6604811 : Nat := 118140960795 + 6604811 * 2 ^ 59
def prefixEnd_6604811 : Nat := 4983230072969 + 3 ^ 40 * 6604811 * 2
def baseEnd_6604811 : Nat := 1130480891701021126762511

theorem tailTrace_6604811 : CollatzResearch.WordTrace tailWord_6604811 prefixEnd_6604811 1130480891701021126762511 := by
  unfold tailWord_6604811
  simp only [CollatzResearch.WordTrace]
  refine ⟨240897247674905233758294287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160598165116603489172196191 240897247674905233758294287)
  ·
    refine ⟨361345871512357850637441431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240897247674905233758294287 361345871512357850637441431)
    ·
      refine ⟨542018807268536775956162147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361345871512357850637441431 542018807268536775956162147)
      ·
        refine ⟨813028210902805163934243221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542018807268536775956162147 813028210902805163934243221)
        ·
          refine ⟨38110697386068992059417651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 813028210902805163934243221 38110697386068992059417651)
          ·
            refine ⟨57166046079103488089126477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38110697386068992059417651 57166046079103488089126477)
            ·
              refine ⟨21437267279663808033422429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57166046079103488089126477 21437267279663808033422429)
              ·
                refine ⟨8038975229873928012533411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21437267279663808033422429 8038975229873928012533411)
                ·
                  refine ⟨12058462844810892018800117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8038975229873928012533411 12058462844810892018800117)
                  ·
                    refine ⟨1130480891701021126762511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12058462844810892018800117 1130480891701021126762511)
                    ·
                      rfl

theorem cell23_6604811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 1, 5].length) (baseStart_6604811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604811 prefixEnd_6604811 := by exact prefixLift 6604811
  have htrace : WordTrace (prefixWord ++ tailWord_6604811) baseStart_6604811 baseEnd_6604811 := by
    simpa [prefixWord, tailWord_6604811, baseEnd_6604811] using wordTrace_append hprefix tailTrace_6604811
  have hstable : (prefixWord ++ tailWord_6604811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604811).length < 2 ^ (prefixWord ++ tailWord_6604811).sum := by decide
  have hdescent : baseEnd_6604811 < baseStart_6604811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604848 : List Nat := [2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 4]
def baseStart_6604848 : Nat := 118140960795 + 6604848 * 2 ^ 59
def prefixEnd_6604848 : Nat := 4983230072969 + 3 ^ 40 * 6604848 * 2
def baseEnd_6604848 : Nat := 3391461673887279735524863

theorem tailTrace_6604848 : CollatzResearch.WordTrace tailWord_6604848 prefixEnd_6604848 3391461673887279735524863 := by
  unfold tailWord_6604848
  simp only [CollatzResearch.WordTrace]
  refine ⟨120449298587885594538695599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160599064783847459384927465 120449298587885594538695599)
  ·
    refine ⟨180673947881828391808043399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120449298587885594538695599 180673947881828391808043399)
    ·
      refine ⟨271010921822742587712065099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180673947881828391808043399 271010921822742587712065099)
      ·
        refine ⟨406516382734113881568097649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271010921822742587712065099 406516382734113881568097649)
        ·
          refine ⟨304887287050585411176073237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406516382734113881568097649 304887287050585411176073237)
          ·
            refine ⟨14291591580496191148878433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 304887287050585411176073237 14291591580496191148878433)
            ·
              refine ⟨10718693685372143361658825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14291591580496191148878433 10718693685372143361658825)
              ·
                refine ⟨8039020264029107521244119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10718693685372143361658825 8039020264029107521244119)
                ·
                  refine ⟨12058530396043661281866179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8039020264029107521244119 12058530396043661281866179)
                  ·
                    refine ⟨18087795594065491922799269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12058530396043661281866179 18087795594065491922799269)
                    ·
                      refine ⟨3391461673887279735524863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18087795594065491922799269 3391461673887279735524863)
                      ·
                        rfl

theorem cell23_6604848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 4].length) (baseStart_6604848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604848 prefixEnd_6604848 := by exact prefixLift 6604848
  have htrace : WordTrace (prefixWord ++ tailWord_6604848) baseStart_6604848 baseEnd_6604848 := by
    simpa [prefixWord, tailWord_6604848, baseEnd_6604848] using wordTrace_append hprefix tailTrace_6604848
  have hstable : (prefixWord ++ tailWord_6604848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604848).length < 2 ^ (prefixWord ++ tailWord_6604848).sum := by decide
  have hdescent : baseEnd_6604848 < baseStart_6604848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604851 : List Nat := [1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 3]
def baseStart_6604851 : Nat := 118140960795 + 6604851 * 2 ^ 59
def prefixEnd_6604851 : Nat := 4983230072969 + 3 ^ 40 * 6604851 * 2
def baseEnd_6604851 : Nat := 3391463214329243223787349

theorem tailTrace_6604851 : CollatzResearch.WordTrace tailWord_6604851 prefixEnd_6604851 3391463214329243223787349 := by
  unfold tailWord_6604851
  simp only [CollatzResearch.WordTrace]
  refine ⟨240898706594760320589750407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160599137729840213726500271 240898706594760320589750407)
  ·
    refine ⟨361348059892140480884625611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240898706594760320589750407 361348059892140480884625611)
    ·
      refine ⟨542022089838210721326938417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361348059892140480884625611 542022089838210721326938417)
      ·
        refine ⟨406516567378658040995203813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542022089838210721326938417 406516567378658040995203813)
        ·
          refine ⟨76221856383498382686600715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 406516567378658040995203813 76221856383498382686600715)
          ·
            refine ⟨114332784575247574029901073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76221856383498382686600715 114332784575247574029901073)
            ·
              refine ⟨85749588431435680522425805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114332784575247574029901073 85749588431435680522425805)
              ·
                refine ⟨32156095661788380195909677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85749588431435680522425805 32156095661788380195909677)
                ·
                  refine ⟨12058535873170642573466129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32156095661788380195909677 12058535873170642573466129)
                  ·
                    refine ⟨9043901904877981930099597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12058535873170642573466129 9043901904877981930099597)
                    ·
                      refine ⟨3391463214329243223787349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9043901904877981930099597 3391463214329243223787349)
                      ·
                        rfl

theorem cell23_6604851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 3, 2, 3].length) (baseStart_6604851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604851 prefixEnd_6604851 := by exact prefixLift 6604851
  have htrace : WordTrace (prefixWord ++ tailWord_6604851) baseStart_6604851 baseEnd_6604851 := by
    simpa [prefixWord, tailWord_6604851, baseEnd_6604851] using wordTrace_append hprefix tailTrace_6604851
  have hstable : (prefixWord ++ tailWord_6604851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604851).length < 2 ^ (prefixWord ++ tailWord_6604851).sum := by decide
  have hdescent : baseEnd_6604851 < baseStart_6604851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604861 : List Nat := [1, 4, 1, 3, 1, 1, 2, 1, 3, 2, 4]
def baseStart_6604861 : Nat := 118140960795 + 6604861 * 2 ^ 59
def prefixEnd_6604861 : Nat := 4983230072969 + 3 ^ 40 * 6604861 * 2
def baseEnd_6604861 : Nat := 3391468349135788184662303

theorem tailTrace_6604861 : CollatzResearch.WordTrace tailWord_6604861 prefixEnd_6604861 3391468349135788184662303 := by
  unfold tailWord_6604861
  simp only [CollatzResearch.WordTrace]
  refine ⟨240899071324724092297614437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160599380883149394865076291 240899071324724092297614437)
  ·
    refine ⟨45168575873385767305802707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240899071324724092297614437 45168575873385767305802707)
    ·
      refine ⟨67752863810078650958704061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45168575873385767305802707 67752863810078650958704061)
      ·
        refine ⟨25407323928779494109514023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67752863810078650958704061 25407323928779494109514023)
        ·
          refine ⟨38110985893169241164271035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25407323928779494109514023 38110985893169241164271035)
          ·
            refine ⟨57166478839753861746406553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38110985893169241164271035 57166478839753861746406553)
            ·
              refine ⟨42874859129815396309804915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57166478839753861746406553 42874859129815396309804915)
              ·
                refine ⟨64312288694723094464707373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42874859129815396309804915 64312288694723094464707373)
                ·
                  refine ⟨24117108260521160424265265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64312288694723094464707373 24117108260521160424265265)
                  ·
                    refine ⟨18087831195390870318198949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24117108260521160424265265 18087831195390870318198949)
                    ·
                      refine ⟨3391468349135788184662303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18087831195390870318198949 3391468349135788184662303)
                      ·
                        rfl

theorem cell23_6604861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_6604861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604861 prefixEnd_6604861 := by exact prefixLift 6604861
  have htrace : WordTrace (prefixWord ++ tailWord_6604861) baseStart_6604861 baseEnd_6604861 := by
    simpa [prefixWord, tailWord_6604861, baseEnd_6604861] using wordTrace_append hprefix tailTrace_6604861
  have hstable : (prefixWord ++ tailWord_6604861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604861).length < 2 ^ (prefixWord ++ tailWord_6604861).sum := by decide
  have hdescent : baseEnd_6604861 < baseStart_6604861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604892 : List Nat := [2, 2, 4, 1, 1, 4, 2, 1, 2, 4]
def baseStart_6604892 : Nat := 118140960795 + 6604892 * 2 ^ 59
def prefixEnd_6604892 : Nat := 4983230072969 + 3 ^ 40 * 6604892 * 2
def baseEnd_6604892 : Nat := 1130494755678692521124887

theorem tailTrace_6604892 : CollatzResearch.WordTrace tailWord_6604892 prefixEnd_6604892 1130494755678692521124887 := by
  unfold tailWord_6604892
  simp only [CollatzResearch.WordTrace]
  refine ⟨120450100993805892295996465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160600134658407856394661953 120450100993805892295996465)
  ·
    refine ⟨90337575745354419221997349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120450100993805892295996465 90337575745354419221997349)
    ·
      refine ⟨16938295452253953604124503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 90337575745354419221997349 16938295452253953604124503)
      ·
        refine ⟨25407443178380930406186755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16938295452253953604124503 25407443178380930406186755)
        ·
          refine ⟨38111164767571395609280133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25407443178380930406186755 38111164767571395609280133)
          ·
            refine ⟨7145843393919636676740025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38111164767571395609280133 7145843393919636676740025)
            ·
              refine ⟨5359382545439727507555019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7145843393919636676740025 5359382545439727507555019)
              ·
                refine ⟨8039073818159591261332529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5359382545439727507555019 8039073818159591261332529)
                ·
                  refine ⟨6029305363619693445999397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8039073818159591261332529 6029305363619693445999397)
                  ·
                    refine ⟨1130494755678692521124887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6029305363619693445999397 1130494755678692521124887)
                    ·
                      rfl

theorem cell23_6604892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 1, 2, 4].length) (baseStart_6604892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604892 prefixEnd_6604892 := by exact prefixLift 6604892
  have htrace : WordTrace (prefixWord ++ tailWord_6604892) baseStart_6604892 baseEnd_6604892 := by
    simpa [prefixWord, tailWord_6604892, baseEnd_6604892] using wordTrace_append hprefix tailTrace_6604892
  have hstable : (prefixWord ++ tailWord_6604892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604892).length < 2 ^ (prefixWord ++ tailWord_6604892).sum := by decide
  have hdescent : baseEnd_6604892 < baseStart_6604892 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604955 : List Nat := [1, 1, 1, 1, 1, 1, 2, 9, 2, 2, 2]
def baseStart_6604955 : Nat := 118140960795 + 6604955 * 2 ^ 59
def prefixEnd_6604955 : Nat := 4983230072969 + 3 ^ 40 * 6604955 * 2
def baseEnd_6604955 : Nat := 3391516616317310816886871

theorem tailTrace_6604955 : CollatzResearch.WordTrace tailWord_6604955 prefixEnd_6604955 3391516616317310816886871 := by
  unfold tailWord_6604955
  simp only [CollatzResearch.WordTrace]
  refine ⟨240902499786383546351536319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160601666524255697567690879 240902499786383546351536319)
  ·
    refine ⟨361353749679575319527304479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240902499786383546351536319 361353749679575319527304479)
    ·
      refine ⟨542030624519362979290956719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361353749679575319527304479 542030624519362979290956719)
      ·
        refine ⟨813045936779044468936435079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542030624519362979290956719 813045936779044468936435079)
        ·
          refine ⟨1219568905168566703404652619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813045936779044468936435079 1219568905168566703404652619)
          ·
            refine ⟨1829353357752850055106978929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219568905168566703404652619 1829353357752850055106978929)
            ·
              refine ⟨1372015018314637541330234197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829353357752850055106978929 1372015018314637541330234197)
              ·
                refine ⟨8039150497937329343731841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1372015018314637541330234197 8039150497937329343731841)
                ·
                  refine ⟨6029362873452997007798881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8039150497937329343731841 6029362873452997007798881)
                  ·
                    refine ⟨4522022155089747755849161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6029362873452997007798881 4522022155089747755849161)
                    ·
                      refine ⟨3391516616317310816886871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522022155089747755849161 3391516616317310816886871)
                      ·
                        rfl

theorem cell23_6604955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 9, 2, 2, 2].length) (baseStart_6604955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604955 prefixEnd_6604955 := by exact prefixLift 6604955
  have htrace : WordTrace (prefixWord ++ tailWord_6604955) baseStart_6604955 baseEnd_6604955 := by
    simpa [prefixWord, tailWord_6604955, baseEnd_6604955] using wordTrace_append hprefix tailTrace_6604955
  have hstable : (prefixWord ++ tailWord_6604955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604955).length < 2 ^ (prefixWord ++ tailWord_6604955).sum := by decide
  have hdescent : baseEnd_6604955 < baseStart_6604955 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604961 : List Nat := [1, 2, 3, 3, 1, 2, 1, 1, 9]
def baseStart_6604961 : Nat := 118140960795 + 6604961 * 2 ^ 59
def prefixEnd_6604961 : Nat := 4983230072969 + 3 ^ 40 * 6604961 * 2
def baseEnd_6604961 : Nat := 376835521911248643712427

theorem tailTrace_6604961 : CollatzResearch.WordTrace tailWord_6604961 prefixEnd_6604961 376835521911248643712427 := by
  unfold tailWord_6604961
  simp only [CollatzResearch.WordTrace]
  refine ⟨240902718624361809376254737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160601812416241206250836491 240902718624361809376254737)
  ·
    refine ⟨180677038968271357032191053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240902718624361809376254737 180677038968271357032191053)
    ·
      refine ⟨67753889613101758887071645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180677038968271357032191053 67753889613101758887071645)
      ·
        refine ⟨25407708604913159582651867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67753889613101758887071645 25407708604913159582651867)
        ·
          refine ⟨38111562907369739373977801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25407708604913159582651867 38111562907369739373977801)
          ·
            refine ⟨28583672180527304530483351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38111562907369739373977801 28583672180527304530483351)
            ·
              refine ⟨42875508270790956795725027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28583672180527304530483351 42875508270790956795725027)
              ·
                refine ⟨64313262406186435193587541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42875508270790956795725027 64313262406186435193587541)
                ·
                  refine ⟨376835521911248643712427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64313262406186435193587541 376835521911248643712427)
                  ·
                    rfl

theorem cell23_6604961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 9].length) (baseStart_6604961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604961 prefixEnd_6604961 := by exact prefixLift 6604961
  have htrace : WordTrace (prefixWord ++ tailWord_6604961) baseStart_6604961 baseEnd_6604961 := by
    simpa [prefixWord, tailWord_6604961, baseEnd_6604961] using wordTrace_append hprefix tailTrace_6604961
  have hstable : (prefixWord ++ tailWord_6604961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604961).length < 2 ^ (prefixWord ++ tailWord_6604961).sum := by decide
  have hdescent : baseEnd_6604961 < baseStart_6604961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6604991 : List Nat := [1, 1, 2, 2, 2, 2, 1, 3, 4, 5]
def baseStart_6604991 : Nat := 118140960795 + 6604991 * 2 ^ 59
def prefixEnd_6604991 : Nat := 4983230072969 + 3 ^ 40 * 6604991 * 2
def baseEnd_6604991 : Nat := 1130511700540290892012235

theorem tailTrace_6604991 : CollatzResearch.WordTrace tailWord_6604991 prefixEnd_6604991 1130511700540290892012235 := by
  unfold tailWord_6604991
  simp only [CollatzResearch.WordTrace]
  refine ⟨240903812814253124499846827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160602541876168749666564551 240903812814253124499846827)
  ·
    refine ⟨361355719221379686749770241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240903812814253124499846827 361355719221379686749770241)
    ·
      refine ⟨271016789416034765062327681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361355719221379686749770241 271016789416034765062327681)
      ·
        refine ⟨203262592062026073796745761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271016789416034765062327681 203262592062026073796745761)
        ·
          refine ⟨152446944046519555347559321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203262592062026073796745761 152446944046519555347559321)
          ·
            refine ⟨114335208034889666510669491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152446944046519555347559321 114335208034889666510669491)
            ·
              refine ⟨171502812052334499766004237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114335208034889666510669491 171502812052334499766004237)
              ·
                refine ⟨64313554519625437412251589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171502812052334499766004237 64313554519625437412251589)
                ·
                  refine ⟨12058791472429769514797173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64313554519625437412251589 12058791472429769514797173)
                  ·
                    refine ⟨1130511700540290892012235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12058791472429769514797173 1130511700540290892012235)
                    ·
                      rfl

theorem cell23_6604991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 4, 5].length) (baseStart_6604991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6604991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6604991 prefixEnd_6604991 := by exact prefixLift 6604991
  have htrace : WordTrace (prefixWord ++ tailWord_6604991) baseStart_6604991 baseEnd_6604991 := by
    simpa [prefixWord, tailWord_6604991, baseEnd_6604991] using wordTrace_append hprefix tailTrace_6604991
  have hstable : (prefixWord ++ tailWord_6604991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6604991).length < 2 ^ (prefixWord ++ tailWord_6604991).sum := by decide
  have hdescent : baseEnd_6604991 < baseStart_6604991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6604991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605028 : List Nat := [2, 3, 1, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_6605028 : Nat := 118140960795 + 6605028 * 2 ^ 59
def prefixEnd_6605028 : Nat := 4983230072969 + 3 ^ 40 * 6605028 * 2
def baseEnd_6605028 : Nat := 3391554100405089031274035

theorem tailTrace_6605028 : CollatzResearch.WordTrace tailWord_6605028 prefixEnd_6605028 3391554100405089031274035 := by
  unfold tailWord_6605028
  simp only [CollatzResearch.WordTrace]
  refine ⟨120452581157559539909471869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160603441543412719879295825 120452581157559539909471869)
  ·
    refine ⟨45169717934084827466051951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120452581157559539909471869 45169717934084827466051951)
    ·
      refine ⟨67754576901127241199077927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45169717934084827466051951 67754576901127241199077927)
      ·
        refine ⟨101631865351690861798616891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67754576901127241199077927 101631865351690861798616891)
        ·
          refine ⟨152447798027536292697925337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101631865351690861798616891 152447798027536292697925337)
          ·
            refine ⟨114335848520652219523444003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152447798027536292697925337 114335848520652219523444003)
            ·
              refine ⟨171503772780978329285166005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114335848520652219523444003 171503772780978329285166005)
              ·
                refine ⟨16078478698216718370484313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 171503772780978329285166005 16078478698216718370484313)
                ·
                  refine ⟨12058859023662538777863235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16078478698216718370484313 12058859023662538777863235)
                  ·
                    refine ⟨18088288535493808166794853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12058859023662538777863235 18088288535493808166794853)
                    ·
                      refine ⟨3391554100405089031274035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18088288535493808166794853 3391554100405089031274035)
                      ·
                        rfl

theorem cell23_6605028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_6605028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605028 prefixEnd_6605028 := by exact prefixLift 6605028
  have htrace : WordTrace (prefixWord ++ tailWord_6605028) baseStart_6605028 baseEnd_6605028 := by
    simpa [prefixWord, tailWord_6605028, baseEnd_6605028] using wordTrace_append hprefix tailTrace_6605028
  have hstable : (prefixWord ++ tailWord_6605028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605028).length < 2 ^ (prefixWord ++ tailWord_6605028).sum := by decide
  have hdescent : baseEnd_6605028 < baseStart_6605028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605041 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 6]
def baseStart_6605041 : Nat := 118140960795 + 6605041 * 2 ^ 59
def prefixEnd_6605041 : Nat := 4983230072969 + 3 ^ 40 * 6605041 * 2
def baseEnd_6605041 : Nat := 3391560775653597480411475

theorem tailTrace_6605041 : CollatzResearch.WordTrace tailWord_6605041 prefixEnd_6605041 3391560775653597480411475 := by
  unfold tailWord_6605041
  simp only [CollatzResearch.WordTrace]
  refine ⟨240905636464071983039166977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160603757642714655359444651 240905636464071983039166977)
  ·
    refine ⟨180679227348053987279375233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240905636464071983039166977 180679227348053987279375233)
    ·
      refine ⟨135509420511040490459531425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180679227348053987279375233 135509420511040490459531425)
      ·
        refine ⟨101632065383280367844648569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135509420511040490459531425 101632065383280367844648569)
        ·
          refine ⟨76224049037460275883486427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101632065383280367844648569 76224049037460275883486427)
          ·
            refine ⟨114336073556190413825229641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76224049037460275883486427 114336073556190413825229641)
            ·
              refine ⟨85752055167142810368922231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114336073556190413825229641 85752055167142810368922231)
              ·
                refine ⟨128628082750714215553383347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85752055167142810368922231 128628082750714215553383347)
                ·
                  refine ⟨192942124126071323330075021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128628082750714215553383347 192942124126071323330075021)
                  ·
                    refine ⟨72353296547276746248778133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 192942124126071323330075021 72353296547276746248778133)
                    ·
                      refine ⟨3391560775653597480411475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72353296547276746248778133 3391560775653597480411475)
                      ·
                        rfl

theorem cell23_6605041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 1, 3, 6].length) (baseStart_6605041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605041 prefixEnd_6605041 := by exact prefixLift 6605041
  have htrace : WordTrace (prefixWord ++ tailWord_6605041) baseStart_6605041 baseEnd_6605041 := by
    simpa [prefixWord, tailWord_6605041, baseEnd_6605041] using wordTrace_append hprefix tailTrace_6605041
  have hstable : (prefixWord ++ tailWord_6605041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605041).length < 2 ^ (prefixWord ++ tailWord_6605041).sum := by decide
  have hdescent : baseEnd_6605041 < baseStart_6605041 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605068 : List Nat := [2, 2, 1, 2, 2, 2, 3, 3, 6]
def baseStart_6605068 : Nat := 118140960795 + 6605068 * 2 ^ 59
def prefixEnd_6605068 : Nat := 4983230072969 + 3 ^ 40 * 6605068 * 2
def baseEnd_6605068 : Nat := 376841626625696541641539

theorem tailTrace_6605068 : CollatzResearch.WordTrace tailWord_6605068 prefixEnd_6605068 376841626625696541641539 := by
  unfold tailWord_6605068
  simp only [CollatzResearch.WordTrace]
  refine ⟨120453310617487083325199929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160604414156649444433599905 120453310617487083325199929)
  ·
    refine ⟨90339982963115312493899947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120453310617487083325199929 90339982963115312493899947)
    ·
      refine ⟨135509974444672968740849921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90339982963115312493899947 135509974444672968740849921)
      ·
        refine ⟨101632480833504726555637441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135509974444672968740849921 101632480833504726555637441)
        ·
          refine ⟨76224360625128544916728081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101632480833504726555637441 76224360625128544916728081)
          ·
            refine ⟨57168270468846408687546061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76224360625128544916728081 57168270468846408687546061)
            ·
              refine ⟨21438101425817403257829773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57168270468846408687546061 21438101425817403257829773)
              ·
                refine ⟨8039288034681526221686165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21438101425817403257829773 8039288034681526221686165)
                ·
                  refine ⟨376841626625696541641539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8039288034681526221686165 376841626625696541641539)
                  ·
                    rfl

theorem cell23_6605068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 6].length) (baseStart_6605068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605068 prefixEnd_6605068 := by exact prefixLift 6605068
  have htrace : WordTrace (prefixWord ++ tailWord_6605068) baseStart_6605068 baseEnd_6605068 := by
    simpa [prefixWord, tailWord_6605068, baseEnd_6605068] using wordTrace_append hprefix tailTrace_6605068
  have hstable : (prefixWord ++ tailWord_6605068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605068).length < 2 ^ (prefixWord ++ tailWord_6605068).sum := by decide
  have hdescent : baseEnd_6605068 < baseStart_6605068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605071 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 6]
def baseStart_6605071 : Nat := 118140960795 + 6605071 * 2 ^ 59
def prefixEnd_6605071 : Nat := 4983230072969 + 3 ^ 40 * 6605071 * 2
def baseEnd_6605071 : Nat := 3391576180073232363036337

theorem tailTrace_6605071 : CollatzResearch.WordTrace tailWord_6605071 prefixEnd_6605071 3391576180073232363036337 := by
  unfold tailWord_6605071
  simp only [CollatzResearch.WordTrace]
  refine ⟨240906730653963298162759067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160604487102642198775172711 240906730653963298162759067)
  ·
    refine ⟨361360095980944947244138601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240906730653963298162759067 361360095980944947244138601)
    ·
      refine ⟨271020071985708710433103951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361360095980944947244138601 271020071985708710433103951)
      ·
        refine ⟨406530107978563065649655927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271020071985708710433103951 406530107978563065649655927)
        ·
          refine ⟨609795161967844598474483891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406530107978563065649655927 609795161967844598474483891)
          ·
            refine ⟨914692742951766897711725837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609795161967844598474483891 914692742951766897711725837)
            ·
              refine ⟨343009778606912586641897189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 914692742951766897711725837 343009778606912586641897189)
              ·
                refine ⟨64314333488796109995355723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 343009778606912586641897189 64314333488796109995355723)
                ·
                  refine ⟨96471500233194164993033585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64314333488796109995355723 96471500233194164993033585)
                  ·
                    refine ⟨72353625174895623744775189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 96471500233194164993033585 72353625174895623744775189)
                    ·
                      refine ⟨3391576180073232363036337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72353625174895623744775189 3391576180073232363036337)
                      ·
                        rfl

theorem cell23_6605071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 6].length) (baseStart_6605071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605071 prefixEnd_6605071 := by exact prefixLift 6605071
  have htrace : WordTrace (prefixWord ++ tailWord_6605071) baseStart_6605071 baseEnd_6605071 := by
    simpa [prefixWord, tailWord_6605071, baseEnd_6605071] using wordTrace_append hprefix tailTrace_6605071
  have hstable : (prefixWord ++ tailWord_6605071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605071).length < 2 ^ (prefixWord ++ tailWord_6605071).sum := by decide
  have hdescent : baseEnd_6605071 < baseStart_6605071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605082 : List Nat := [3, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3]
def baseStart_6605082 : Nat := 118140960795 + 6605082 * 2 ^ 59
def prefixEnd_6605082 : Nat := 4983230072969 + 3 ^ 40 * 6605082 * 2
def baseEnd_6605082 : Nat := 3391581828360431819998787

theorem tailTrace_6605082 : CollatzResearch.WordTrace tailWord_6605082 prefixEnd_6605082 3391581828360431819998787 := by
  unfold tailWord_6605082
  simp only [CollatzResearch.WordTrace]
  refine ⟨60226782964230861760352375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160604754571282298027606333 60226782964230861760352375)
  ·
    refine ⟨90340174446346292640528563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60226782964230861760352375 90340174446346292640528563)
    ·
      refine ⟨135510261669519438960792845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90340174446346292640528563 135510261669519438960792845)
      ·
        refine ⟨50816348126069789610297317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135510261669519438960792845 50816348126069789610297317)
        ·
          refine ⟨9528065273638085551930747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50816348126069789610297317 9528065273638085551930747)
          ·
            refine ⟨14292097910457128327896121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9528065273638085551930747 14292097910457128327896121)
            ·
              refine ⟨10719073432842846245922091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14292097910457128327896121 10719073432842846245922091)
              ·
                refine ⟨16078610149264269368883137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10719073432842846245922091 16078610149264269368883137)
                ·
                  refine ⟨12058957611948202026662353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16078610149264269368883137 12058957611948202026662353)
                  ·
                    refine ⟨9044218208961151519996765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12058957611948202026662353 9044218208961151519996765)
                    ·
                      refine ⟨3391581828360431819998787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9044218208961151519996765 3391581828360431819998787)
                      ·
                        rfl

theorem cell23_6605082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3].length) (baseStart_6605082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605082 prefixEnd_6605082 := by exact prefixLift 6605082
  have htrace : WordTrace (prefixWord ++ tailWord_6605082) baseStart_6605082 baseEnd_6605082 := by
    simpa [prefixWord, tailWord_6605082, baseEnd_6605082] using wordTrace_append hprefix tailTrace_6605082
  have hstable : (prefixWord ++ tailWord_6605082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605082).length < 2 ^ (prefixWord ++ tailWord_6605082).sum := by decide
  have hdescent : baseEnd_6605082 < baseStart_6605082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605106 : List Nat := [3, 2, 1, 1, 5, 2, 2, 2, 1, 4]
def baseStart_6605106 : Nat := 118140960795 + 6605106 * 2 ^ 59
def prefixEnd_6605106 : Nat := 4983230072969 + 3 ^ 40 * 6605106 * 2
def baseEnd_6605106 : Nat := 1130531383965379908699559

theorem tailTrace_6605106 : CollatzResearch.WordTrace tailWord_6605106 prefixEnd_6605106 1130531383965379908699559 := by
  unfold tailWord_6605106
  simp only [CollatzResearch.WordTrace]
  refine ⟨60227001802209124785070793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160605338139224332760188781 60227001802209124785070793)
  ·
    refine ⟨45170251351656843588803095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60227001802209124785070793 45170251351656843588803095)
    ·
      refine ⟨67755377027485265383204643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45170251351656843588803095 67755377027485265383204643)
      ·
        refine ⟨101633065541227898074806965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67755377027485265383204643 101633065541227898074806965)
        ·
          refine ⟨9528099894490115444513153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101633065541227898074806965 9528099894490115444513153)
          ·
            refine ⟨7146074920867586583384865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9528099894490115444513153 7146074920867586583384865)
            ·
              refine ⟨5359556190650689937538649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7146074920867586583384865 5359556190650689937538649)
              ·
                refine ⟨4019667142988017453153987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5359556190650689937538649 4019667142988017453153987)
                ·
                  refine ⟨6029500714482026179730981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4019667142988017453153987 6029500714482026179730981)
                  ·
                    refine ⟨1130531383965379908699559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6029500714482026179730981 1130531383965379908699559)
                    ·
                      rfl

theorem cell23_6605106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_6605106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605106 prefixEnd_6605106 := by exact prefixLift 6605106
  have htrace : WordTrace (prefixWord ++ tailWord_6605106) baseStart_6605106 baseEnd_6605106 := by
    simpa [prefixWord, tailWord_6605106, baseEnd_6605106] using wordTrace_append hprefix tailTrace_6605106
  have hstable : (prefixWord ++ tailWord_6605106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605106).length < 2 ^ (prefixWord ++ tailWord_6605106).sum := by decide
  have hdescent : baseEnd_6605106 < baseStart_6605106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605128 : List Nat := [2, 1, 3, 1, 1, 2, 3, 3, 1, 6]
def baseStart_6605128 : Nat := 118140960795 + 6605128 * 2 ^ 59
def prefixEnd_6605128 : Nat := 4983230072969 + 3 ^ 40 * 6605128 * 2
def baseEnd_6605128 : Nat := 1130535149490179546674525

theorem tailTrace_6605128 : CollatzResearch.WordTrace tailWord_6605128 prefixEnd_6605128 1130535149490179546674525 := by
  unfold tailWord_6605128
  simp only [CollatzResearch.WordTrace]
  refine ⟨120454404807378398448792019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160605873076504531265056025 120454404807378398448792019)
  ·
    refine ⟨180681607211067597673188029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120454404807378398448792019 180681607211067597673188029)
    ·
      refine ⟨67755602704150349127445511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180681607211067597673188029 67755602704150349127445511)
      ·
        refine ⟨101633404056225523691168267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67755602704150349127445511 101633404056225523691168267)
        ·
          refine ⟨152450106084338285536752401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101633404056225523691168267 152450106084338285536752401)
          ·
            refine ⟨114337579563253714152564301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152450106084338285536752401 114337579563253714152564301)
            ·
              refine ⟨42876592336220142807211613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114337579563253714152564301 42876592336220142807211613)
              ·
                refine ⟨16078722126082553552704355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42876592336220142807211613 16078722126082553552704355)
                ·
                  refine ⟨24118083189123830329056533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16078722126082553552704355 24118083189123830329056533)
                  ·
                    refine ⟨1130535149490179546674525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24118083189123830329056533 1130535149490179546674525)
                    ·
                      rfl

theorem cell23_6605128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_6605128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605128 prefixEnd_6605128 := by exact prefixLift 6605128
  have htrace : WordTrace (prefixWord ++ tailWord_6605128) baseStart_6605128 baseEnd_6605128 := by
    simpa [prefixWord, tailWord_6605128, baseEnd_6605128] using wordTrace_append hprefix tailTrace_6605128
  have hstable : (prefixWord ++ tailWord_6605128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605128).length < 2 ^ (prefixWord ++ tailWord_6605128).sum := by decide
  have hdescent : baseEnd_6605128 < baseStart_6605128 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605152 : List Nat := [2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 4]
def baseStart_6605152 : Nat := 118140960795 + 6605152 * 2 ^ 59
def prefixEnd_6605152 : Nat := 4983230072969 + 3 ^ 40 * 6605152 * 2
def baseEnd_6605152 : Nat := 3391617772006246546123465

theorem tailTrace_6605152 : CollatzResearch.WordTrace tailWord_6605152 prefixEnd_6605152 3391617772006246546123465 := by
  unfold tailWord_6605152
  simp only [CollatzResearch.WordTrace]
  refine ⟨120454842483334924498228855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160606456644446565997638473 120454842483334924498228855)
  ·
    refine ⟨180682263725002386747343283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120454842483334924498228855 180682263725002386747343283)
    ·
      refine ⟨271023395587503580121014925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180682263725002386747343283 271023395587503580121014925)
      ·
        refine ⟨101633773345313842545380597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271023395587503580121014925 101633773345313842545380597)
        ·
          refine ⟨9528166251123172738629431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101633773345313842545380597 9528166251123172738629431)
          ·
            refine ⟨14292249376684759107944147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9528166251123172738629431 14292249376684759107944147)
            ·
              refine ⟨21438374065027138661916221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14292249376684759107944147 21438374065027138661916221)
              ·
                refine ⟨8039390274385176998218583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21438374065027138661916221 8039390274385176998218583)
                ·
                  refine ⟨12059085411577765497327875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8039390274385176998218583 12059085411577765497327875)
                  ·
                    refine ⟨18088628117366648245991813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12059085411577765497327875 18088628117366648245991813)
                    ·
                      refine ⟨3391617772006246546123465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18088628117366648245991813 3391617772006246546123465)
                      ·
                        rfl

theorem cell23_6605152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_6605152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605152 prefixEnd_6605152 := by exact prefixLift 6605152
  have htrace : WordTrace (prefixWord ++ tailWord_6605152) baseStart_6605152 baseEnd_6605152 := by
    simpa [prefixWord, tailWord_6605152, baseEnd_6605152] using wordTrace_append hprefix tailTrace_6605152
  have hstable : (prefixWord ++ tailWord_6605152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605152).length < 2 ^ (prefixWord ++ tailWord_6605152).sum := by decide
  have hdescent : baseEnd_6605152 < baseStart_6605152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605162 : List Nat := [3, 1, 3, 3, 1, 2, 1, 1, 4, 4]
def baseStart_6605162 : Nat := 118140960795 + 6605162 * 2 ^ 59
def prefixEnd_6605162 : Nat := 4983230072969 + 3 ^ 40 * 6605162 * 2
def baseEnd_6605162 : Nat := 1130540968937597168999473

theorem tailTrace_6605162 : CollatzResearch.WordTrace tailWord_6605162 prefixEnd_6605162 1130540968937597168999473 := by
  unfold tailWord_6605162
  simp only [CollatzResearch.WordTrace]
  refine ⟨60227512424158405176080435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160606699797755747136214493 60227512424158405176080435)
  ·
    refine ⟨90341268636237607764120653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60227512424158405176080435 90341268636237607764120653)
    ·
      refine ⟨33877975738589102911545245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90341268636237607764120653 33877975738589102911545245)
      ·
        refine ⟨12704240901970913591829467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33877975738589102911545245 12704240901970913591829467)
        ·
          refine ⟨19056361352956370387744201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12704240901970913591829467 19056361352956370387744201)
          ·
            refine ⟨14292271014717277790808151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19056361352956370387744201 14292271014717277790808151)
            ·
              refine ⟨21438406522075916686212227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14292271014717277790808151 21438406522075916686212227)
              ·
                refine ⟨32157609783113875029318341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21438406522075916686212227 32157609783113875029318341)
                ·
                  refine ⟨6029551834333851567997189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32157609783113875029318341 6029551834333851567997189)
                  ·
                    refine ⟨1130540968937597168999473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6029551834333851567997189 1130540968937597168999473)
                    ·
                      rfl

theorem cell23_6605162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_6605162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605162 prefixEnd_6605162 := by exact prefixLift 6605162
  have htrace : WordTrace (prefixWord ++ tailWord_6605162) baseStart_6605162 baseEnd_6605162 := by
    simpa [prefixWord, tailWord_6605162, baseEnd_6605162] using wordTrace_append hprefix tailTrace_6605162
  have hstable : (prefixWord ++ tailWord_6605162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605162).length < 2 ^ (prefixWord ++ tailWord_6605162).sum := by decide
  have hdescent : baseEnd_6605162 < baseStart_6605162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605186 : List Nat := [3, 4, 2, 1, 2, 1, 2, 2, 1, 1, 4]
def baseStart_6605186 : Nat := 118140960795 + 6605186 * 2 ^ 59
def prefixEnd_6605186 : Nat := 4983230072969 + 3 ^ 40 * 6605186 * 2
def baseEnd_6605186 : Nat := 3391635230348499413098309

theorem tailTrace_6605186 : CollatzResearch.WordTrace tailWord_6605186 prefixEnd_6605186 3391635230348499413098309 := by
  unfold tailWord_6605186
  simp only [CollatzResearch.WordTrace]
  refine ⟨60227731262136668200798853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160607283365697781868796941 60227731262136668200798853)
  ·
    refine ⟨11292699611650625287649785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60227731262136668200798853 11292699611650625287649785)
    ·
      refine ⟨8469524708737968965737339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11292699611650625287649785 8469524708737968965737339)
      ·
        refine ⟨12704287063106953448606009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8469524708737968965737339 12704287063106953448606009)
        ·
          refine ⟨9528215297330215086454507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12704287063106953448606009 9528215297330215086454507)
          ·
            refine ⟨14292322945995322629681761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9528215297330215086454507 14292322945995322629681761)
            ·
              refine ⟨10719242209496491972261321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14292322945995322629681761 10719242209496491972261321)
              ·
                refine ⟨8039431657122368979195991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10719242209496491972261321 8039431657122368979195991)
                ·
                  refine ⟨12059147485683553468793987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8039431657122368979195991 12059147485683553468793987)
                  ·
                    refine ⟨18088721228525330203190981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12059147485683553468793987 18088721228525330203190981)
                    ·
                      refine ⟨3391635230348499413098309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18088721228525330203190981 3391635230348499413098309)
                      ·
                        rfl

theorem cell23_6605186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_6605186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605186 prefixEnd_6605186 := by exact prefixLift 6605186
  have htrace : WordTrace (prefixWord ++ tailWord_6605186) baseStart_6605186 baseEnd_6605186 := by
    simpa [prefixWord, tailWord_6605186, baseEnd_6605186] using wordTrace_append hprefix tailTrace_6605186
  have hstable : (prefixWord ++ tailWord_6605186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605186).length < 2 ^ (prefixWord ++ tailWord_6605186).sum := by decide
  have hdescent : baseEnd_6605186 < baseStart_6605186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605228 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 5]
def baseStart_6605228 : Nat := 118140960795 + 6605228 * 2 ^ 59
def prefixEnd_6605228 : Nat := 4983230072969 + 3 ^ 40 * 6605228 * 2
def baseEnd_6605228 : Nat := 3391656796535988248773115

theorem tailTrace_6605228 : CollatzResearch.WordTrace tailWord_6605228 prefixEnd_6605228 3391656796535988248773115 := by
  unfold tailWord_6605228
  simp only [CollatzResearch.WordTrace]
  refine ⟨120456228457197256988112169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160608304609596342650816225 120456228457197256988112169)
  ·
    refine ⟨90342171342897942741084127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120456228457197256988112169 90342171342897942741084127)
    ·
      refine ⟨135513257014346914111626191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90342171342897942741084127 135513257014346914111626191)
      ·
        refine ⟨203269885521520371167439287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135513257014346914111626191 203269885521520371167439287)
        ·
          refine ⟨304904828282280556751158931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203269885521520371167439287 304904828282280556751158931)
          ·
            refine ⟨457357242423420835126738397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304904828282280556751158931 457357242423420835126738397)
            ·
              refine ⟨171508965908782813172526899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 457357242423420835126738397 171508965908782813172526899)
              ·
                refine ⟨257263448863174219758790349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171508965908782813172526899 257263448863174219758790349)
                ·
                  refine ⟨96473793323690332409546381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257263448863174219758790349 96473793323690332409546381)
                  ·
                    refine ⟨36177672496383874653579893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 96473793323690332409546381 36177672496383874653579893)
                    ·
                      refine ⟨3391656796535988248773115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36177672496383874653579893 3391656796535988248773115)
                      ·
                        rfl

theorem cell23_6605228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_6605228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605228 prefixEnd_6605228 := by exact prefixLift 6605228
  have htrace : WordTrace (prefixWord ++ tailWord_6605228) baseStart_6605228 baseEnd_6605228 := by
    simpa [prefixWord, tailWord_6605228, baseEnd_6605228] using wordTrace_append hprefix tailTrace_6605228
  have hstable : (prefixWord ++ tailWord_6605228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605228).length < 2 ^ (prefixWord ++ tailWord_6605228).sum := by decide
  have hdescent : baseEnd_6605228 < baseStart_6605228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605245 : List Nat := [1, 4, 1, 2, 2, 2, 1, 2, 2, 1, 5]
def baseStart_6605245 : Nat := 118140960795 + 6605245 * 2 ^ 59
def prefixEnd_6605245 : Nat := 4983230072969 + 3 ^ 40 * 6605245 * 2
def baseEnd_6605245 : Nat := 3391665525707114682260537

theorem tailTrace_6605245 : CollatzResearch.WordTrace tailWord_6605245 prefixEnd_6605245 3391665525707114682260537 := by
  unfold tailWord_6605245
  simp only [CollatzResearch.WordTrace]
  refine ⟨240913076955332925879593189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160608717970221950586395459 240913076955332925879593189)
  ·
    refine ⟨45171201929124923602423723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 240913076955332925879593189 45171201929124923602423723)
    ·
      refine ⟨67756802893687385403635585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45171201929124923602423723 67756802893687385403635585)
      ·
        refine ⟨50817602170265539052726689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67756802893687385403635585 50817602170265539052726689)
        ·
          refine ⟨38113201627699154289545017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50817602170265539052726689 38113201627699154289545017)
          ·
            refine ⟨28584901220774365717158763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38113201627699154289545017 28584901220774365717158763)
            ·
              refine ⟨42877351831161548575738145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28584901220774365717158763 42877351831161548575738145)
              ·
                refine ⟨32158013873371161431803609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42877351831161548575738145 32158013873371161431803609)
                ·
                  refine ⟨24118510405028371073852707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32158013873371161431803609 24118510405028371073852707)
                  ·
                    refine ⟨36177765607542556610779061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24118510405028371073852707 36177765607542556610779061)
                    ·
                      refine ⟨3391665525707114682260537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36177765607542556610779061 3391665525707114682260537)
                      ·
                        rfl

theorem cell23_6605245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_6605245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605245 prefixEnd_6605245 := by exact prefixLift 6605245
  have htrace : WordTrace (prefixWord ++ tailWord_6605245) baseStart_6605245 baseEnd_6605245 := by
    simpa [prefixWord, tailWord_6605245, baseEnd_6605245] using wordTrace_append hprefix tailTrace_6605245
  have hstable : (prefixWord ++ tailWord_6605245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605245).length < 2 ^ (prefixWord ++ tailWord_6605245).sum := by decide
  have hdescent : baseEnd_6605245 < baseStart_6605245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605248 : List Nat := [2, 1, 1, 2, 3, 1, 1, 3, 9]
def baseStart_6605248 : Nat := 118140960795 + 6605248 * 2 ^ 59
def prefixEnd_6605248 : Nat := 4983230072969 + 3 ^ 40 * 6605248 * 2
def baseEnd_6605248 : Nat := 376851896238786463391447

theorem tailTrace_6605248 : CollatzResearch.WordTrace tailWord_6605248 prefixEnd_6605248 376851896238786463391447 := by
  unfold tailWord_6605248
  simp only [CollatzResearch.WordTrace]
  refine ⟨120456593187161028695976199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160608790916214704927968265 120456593187161028695976199)
  ·
    refine ⟨180684889780741543043964299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120456593187161028695976199 180684889780741543043964299)
    ·
      refine ⟨271027334671112314565946449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180684889780741543043964299 271027334671112314565946449)
      ·
        refine ⟨203270501003334235924459837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271027334671112314565946449 203270501003334235924459837)
        ·
          refine ⟨76226437876250338471672439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203270501003334235924459837 76226437876250338471672439)
          ·
            refine ⟨114339656814375507707508659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76226437876250338471672439 114339656814375507707508659)
            ·
              refine ⟨171509485221563261561262989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114339656814375507707508659 171509485221563261561262989)
              ·
                refine ⟨64316056958086223085473621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171509485221563261561262989 64316056958086223085473621)
                ·
                  refine ⟨376851896238786463391447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64316056958086223085473621 376851896238786463391447)
                  ·
                    rfl

theorem cell23_6605248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 9].length) (baseStart_6605248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605248 prefixEnd_6605248 := by exact prefixLift 6605248
  have htrace : WordTrace (prefixWord ++ tailWord_6605248) baseStart_6605248 baseEnd_6605248 := by
    simpa [prefixWord, tailWord_6605248, baseEnd_6605248] using wordTrace_append hprefix tailTrace_6605248
  have hstable : (prefixWord ++ tailWord_6605248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605248).length < 2 ^ (prefixWord ++ tailWord_6605248).sum := by decide
  have hdescent : baseEnd_6605248 < baseStart_6605248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605315 : List Nat := [1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 4]
def baseStart_6605315 : Nat := 118140960795 + 6605315 * 2 ^ 59
def prefixEnd_6605315 : Nat := 4983230072969 + 3 ^ 40 * 6605315 * 2
def baseEnd_6605315 : Nat := 3391701469352929408385215

theorem tailTrace_6605315 : CollatzResearch.WordTrace tailWord_6605315 prefixEnd_6605315 3391701469352929408385215 := by
  unfold tailWord_6605315
  simp only [CollatzResearch.WordTrace]
  refine ⟨240915630065079327834641399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160610420043386218556427599 240915630065079327834641399)
  ·
    refine ⟨361373445097618991751962099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240915630065079327834641399 361373445097618991751962099)
    ·
      refine ⟨542060167646428487627943149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361373445097618991751962099 542060167646428487627943149)
      ·
        refine ⟨203272562867410682860478681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 542060167646428487627943149 203272562867410682860478681)
        ·
          refine ⟨152454422150558012145359011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203272562867410682860478681 152454422150558012145359011)
          ·
            refine ⟨228681633225837018218038517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152454422150558012145359011 228681633225837018218038517)
            ·
              refine ⟨21438903114922220457941111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 228681633225837018218038517 21438903114922220457941111)
              ·
                refine ⟨32158354672383330686911667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21438903114922220457941111 32158354672383330686911667)
                ·
                  refine ⟨48237532008574996030367501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32158354672383330686911667 48237532008574996030367501)
                  ·
                    refine ⟨18089074503215623511387813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48237532008574996030367501 18089074503215623511387813)
                    ·
                      refine ⟨3391701469352929408385215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18089074503215623511387813 3391701469352929408385215)
                      ·
                        rfl

theorem cell23_6605315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_6605315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605315 prefixEnd_6605315 := by exact prefixLift 6605315
  have htrace : WordTrace (prefixWord ++ tailWord_6605315) baseStart_6605315 baseEnd_6605315 := by
    simpa [prefixWord, tailWord_6605315, baseEnd_6605315] using wordTrace_append hprefix tailTrace_6605315
  have hstable : (prefixWord ++ tailWord_6605315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605315).length < 2 ^ (prefixWord ++ tailWord_6605315).sum := by decide
  have hdescent : baseEnd_6605315 < baseStart_6605315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605345 : List Nat := [1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_6605345 : Nat := 118140960795 + 6605345 * 2 ^ 59
def prefixEnd_6605345 : Nat := 4983230072969 + 3 ^ 40 * 6605345 * 2
def baseEnd_6605345 : Nat := 3391716873772564291010077

theorem tailTrace_6605345 : CollatzResearch.WordTrace tailWord_6605345 prefixEnd_6605345 3391716873772564291010077 := by
  unfold tailWord_6605345
  simp only [CollatzResearch.WordTrace]
  refine ⟨240916724254970642958233489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160611149503313761972155659 240916724254970642958233489)
  ·
    refine ⟨180687543191227982218675117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240916724254970642958233489 180687543191227982218675117)
    ·
      refine ⟨67757828696710493332003169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180687543191227982218675117 67757828696710493332003169)
      ·
        refine ⟨50818371522532869999002377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67757828696710493332003169 50818371522532869999002377)
        ·
          refine ⟨38113778641899652499251783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50818371522532869999002377 38113778641899652499251783)
          ·
            refine ⟨57170667962849478748877675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38113778641899652499251783 57170667962849478748877675)
            ·
              refine ⟨85756001944274218123316513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57170667962849478748877675 85756001944274218123316513)
              ·
                refine ⟨64317001458205663592487385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85756001944274218123316513 64317001458205663592487385)
                ·
                  refine ⟨48237751093654247694365539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64317001458205663592487385 48237751093654247694365539)
                  ·
                    refine ⟨72356626640481371541548309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48237751093654247694365539 72356626640481371541548309)
                    ·
                      refine ⟨3391716873772564291010077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72356626640481371541548309 3391716873772564291010077)
                      ·
                        rfl

theorem cell23_6605345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_6605345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605345 prefixEnd_6605345 := by exact prefixLift 6605345
  have htrace : WordTrace (prefixWord ++ tailWord_6605345) baseStart_6605345 baseEnd_6605345 := by
    simpa [prefixWord, tailWord_6605345, baseEnd_6605345] using wordTrace_append hprefix tailTrace_6605345
  have hstable : (prefixWord ++ tailWord_6605345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605345).length < 2 ^ (prefixWord ++ tailWord_6605345).sum := by decide
  have hdescent : baseEnd_6605345 < baseStart_6605345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605355 : List Nat := [1, 1, 1, 1, 2, 1, 3, 7, 6]
def baseStart_6605355 : Nat := 118140960795 + 6605355 * 2 ^ 59
def prefixEnd_6605355 : Nat := 4983230072969 + 3 ^ 40 * 6605355 * 2
def baseEnd_6605355 : Nat := 376858000953234361320559

theorem tailTrace_6605355 : CollatzResearch.WordTrace tailWord_6605355 prefixEnd_6605355 376858000953234361320559 := by
  unfold tailWord_6605355
  simp only [CollatzResearch.WordTrace]
  refine ⟨240917088984934414666097519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160611392656622943110731679 240917088984934414666097519)
  ·
    refine ⟨361375633477401621999146279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240917088984934414666097519 361375633477401621999146279)
    ·
      refine ⟨542063450216102432998719419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361375633477401621999146279 542063450216102432998719419)
      ·
        refine ⟨813095175324153649498079129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542063450216102432998719419 813095175324153649498079129)
        ·
          refine ⟨609821381493115237123559347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 813095175324153649498079129 609821381493115237123559347)
          ·
            refine ⟨914732072239672855685339021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609821381493115237123559347 914732072239672855685339021)
            ·
              refine ⟨343024527089877320882002133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 914732072239672855685339021 343024527089877320882002133)
              ·
                refine ⟨8039637353668999708171925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 343024527089877320882002133 8039637353668999708171925)
                ·
                  refine ⟨376858000953234361320559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8039637353668999708171925 376858000953234361320559)
                  ·
                    rfl

theorem cell23_6605355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 7, 6].length) (baseStart_6605355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605355 prefixEnd_6605355 := by exact prefixLift 6605355
  have htrace : WordTrace (prefixWord ++ tailWord_6605355) baseStart_6605355 baseEnd_6605355 := by
    simpa [prefixWord, tailWord_6605355, baseEnd_6605355] using wordTrace_append hprefix tailTrace_6605355
  have hstable : (prefixWord ++ tailWord_6605355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605355).length < 2 ^ (prefixWord ++ tailWord_6605355).sum := by decide
  have hdescent : baseEnd_6605355 < baseStart_6605355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605385 : List Nat := [1, 2, 1, 1, 2, 2, 1, 1, 7, 5]
def baseStart_6605385 : Nat := 118140960795 + 6605385 * 2 ^ 59
def prefixEnd_6605385 : Nat := 4983230072969 + 3 ^ 40 * 6605385 * 2
def baseEnd_6605385 : Nat := 1130579137666248044836631

theorem tailTrace_6605385 : CollatzResearch.WordTrace tailWord_6605385 prefixEnd_6605385 1130579137666248044836631 := by
  unfold tailWord_6605385
  simp only [CollatzResearch.WordTrace]
  refine ⟨240918183174825729789689609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160612122116550486526459739 240918183174825729789689609)
  ·
    refine ⟨180688637381119297342267207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240918183174825729789689609 180688637381119297342267207)
    ·
      refine ⟨271032956071678946013400811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180688637381119297342267207 271032956071678946013400811)
      ·
        refine ⟨406549434107518419020101217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271032956071678946013400811 406549434107518419020101217)
        ·
          refine ⟨304912075580638814265075913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406549434107518419020101217 304912075580638814265075913)
          ·
            refine ⟨228684056685479110698806935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304912075580638814265075913 228684056685479110698806935)
            ·
              refine ⟨343026085028218666048210403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228684056685479110698806935 343026085028218666048210403)
              ·
                refine ⟨514539127542327999072315605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343026085028218666048210403 514539127542327999072315605)
                ·
                  refine ⟨12059510801773312478257397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 514539127542327999072315605 12059510801773312478257397)
                  ·
                    refine ⟨1130579137666248044836631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12059510801773312478257397 1130579137666248044836631)
                    ·
                      rfl

theorem cell23_6605385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 1, 7, 5].length) (baseStart_6605385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605385 prefixEnd_6605385 := by exact prefixLift 6605385
  have htrace : WordTrace (prefixWord ++ tailWord_6605385) baseStart_6605385 baseEnd_6605385 := by
    simpa [prefixWord, tailWord_6605385, baseEnd_6605385] using wordTrace_append hprefix tailTrace_6605385
  have hstable : (prefixWord ++ tailWord_6605385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605385).length < 2 ^ (prefixWord ++ tailWord_6605385).sum := by decide
  have hdescent : baseEnd_6605385 < baseStart_6605385 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605392 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 3, 5, 2]
def baseStart_6605392 : Nat := 118140960795 + 6605392 * 2 ^ 59
def prefixEnd_6605392 : Nat := 4983230072969 + 3 ^ 40 * 6605392 * 2
def baseEnd_6605392 : Nat := 3391741007363325607122361

theorem tailTrace_6605392 : CollatzResearch.WordTrace tailWord_6605392 prefixEnd_6605392 3391741007363325607122361 := by
  unfold tailWord_6605392
  simp only [CollatzResearch.WordTrace]
  refine ⟨120459219242900184992597215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160612292323866913323462953 120459219242900184992597215)
  ·
    refine ⟨180688828864350277488895823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120459219242900184992597215 180688828864350277488895823)
    ·
      refine ⟨271033243296525416233343735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180688828864350277488895823 271033243296525416233343735)
      ·
        refine ⟨406549864944788124350015603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271033243296525416233343735 406549864944788124350015603)
        ·
          refine ⟨609824797417182186525023405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406549864944788124350015603 609824797417182186525023405)
          ·
            refine ⟨228684299031443319946883777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 609824797417182186525023405 228684299031443319946883777)
            ·
              refine ⟨171513224273582489960162833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228684299031443319946883777 171513224273582489960162833)
              ·
                refine ⟨128634918205186867470122125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171513224273582489960162833 128634918205186867470122125)
                ·
                  refine ⟨48238094326945075301295797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128634918205186867470122125 48238094326945075301295797)
                  ·
                    refine ⟨4522321343151100809496481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48238094326945075301295797 4522321343151100809496481)
                    ·
                      refine ⟨3391741007363325607122361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522321343151100809496481 3391741007363325607122361)
                      ·
                        rfl

theorem cell23_6605392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 3, 5, 2].length) (baseStart_6605392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605392 prefixEnd_6605392 := by exact prefixLift 6605392
  have htrace : WordTrace (prefixWord ++ tailWord_6605392) baseStart_6605392 baseEnd_6605392 := by
    simpa [prefixWord, tailWord_6605392, baseEnd_6605392] using wordTrace_append hprefix tailTrace_6605392
  have hstable : (prefixWord ++ tailWord_6605392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605392).length < 2 ^ (prefixWord ++ tailWord_6605392).sum := by decide
  have hdescent : baseEnd_6605392 < baseStart_6605392 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605425 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 2, 5, 5]
def baseStart_6605425 : Nat := 118140960795 + 6605425 * 2 ^ 59
def prefixEnd_6605425 : Nat := 4983230072969 + 3 ^ 40 * 6605425 * 2
def baseEnd_6605425 : Nat := 3391757952224923978009709

theorem tailTrace_6605425 : CollatzResearch.WordTrace tailWord_6605425 prefixEnd_6605425 3391757952224923978009709 := by
  unfold tailWord_6605425
  simp only [CollatzResearch.WordTrace]
  refine ⟨240919642094680816621145729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160613094729787211080763819 240919642094680816621145729)
  ·
    refine ⟨180689731571010612465859297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240919642094680816621145729 180689731571010612465859297)
    ·
      refine ⟨135517298678257959349394473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180689731571010612465859297 135517298678257959349394473)
      ·
        refine ⟨101637974008693469512045855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135517298678257959349394473 101637974008693469512045855)
        ·
          refine ⟨152456961013040204268068783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101637974008693469512045855 152456961013040204268068783)
          ·
            refine ⟨228685441519560306402103175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152456961013040204268068783 228685441519560306402103175)
            ·
              refine ⟨343028162279340459603154763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228685441519560306402103175 343028162279340459603154763)
              ·
                refine ⟨514542243419010689404732145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343028162279340459603154763 514542243419010689404732145)
                ·
                  refine ⟨385906682564258017053549109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514542243419010689404732145 385906682564258017053549109)
                  ·
                    refine ⟨36178751490399189098770229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 385906682564258017053549109 36178751490399189098770229)
                    ·
                      refine ⟨3391757952224923978009709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36178751490399189098770229 3391757952224923978009709)
                      ·
                        rfl

theorem cell23_6605425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 5, 5].length) (baseStart_6605425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605425 prefixEnd_6605425 := by exact prefixLift 6605425
  have htrace : WordTrace (prefixWord ++ tailWord_6605425) baseStart_6605425 baseEnd_6605425 := by
    simpa [prefixWord, tailWord_6605425, baseEnd_6605425] using wordTrace_append hprefix tailTrace_6605425
  have hstable : (prefixWord ++ tailWord_6605425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605425).length < 2 ^ (prefixWord ++ tailWord_6605425).sum := by decide
  have hdescent : baseEnd_6605425 < baseStart_6605425 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605435 : List Nat := [1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 6]
def baseStart_6605435 : Nat := 118140960795 + 6605435 * 2 ^ 59
def prefixEnd_6605435 : Nat := 4983230072969 + 3 ^ 40 * 6605435 * 2
def baseEnd_6605435 : Nat := 3391763087031468938884663

theorem tailTrace_6605435 : CollatzResearch.WordTrace tailWord_6605435 prefixEnd_6605435 3391763087031468938884663 := by
  unfold tailWord_6605435
  simp only [CollatzResearch.WordTrace]
  refine ⟨240920006824644588329009759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160613337883096392219339839 240920006824644588329009759)
  ·
    refine ⟨361380010236966882493514639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240920006824644588329009759 361380010236966882493514639)
    ·
      refine ⟨542070015355450323740271959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361380010236966882493514639 542070015355450323740271959)
      ·
        refine ⟨813105023033175485610407939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542070015355450323740271959 813105023033175485610407939)
        ·
          refine ⟨1219657534549763228415611909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813105023033175485610407939 1219657534549763228415611909)
          ·
            refine ⟨228685787728080605327927233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1219657534549763228415611909 228685787728080605327927233)
            ·
              refine ⟨171514340796060453995945425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228685787728080605327927233 171514340796060453995945425)
              ·
                refine ⟨128635755597045340496959069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171514340796060453995945425 128635755597045340496959069)
                ·
                  refine ⟨48238408348892002686359651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128635755597045340496959069 48238408348892002686359651)
                  ·
                    refine ⟨72357612523338004029539477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48238408348892002686359651 72357612523338004029539477)
                    ·
                      refine ⟨3391763087031468938884663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72357612523338004029539477 3391763087031468938884663)
                      ·
                        rfl

theorem cell23_6605435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 6].length) (baseStart_6605435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605435 prefixEnd_6605435 := by exact prefixLift 6605435
  have htrace : WordTrace (prefixWord ++ tailWord_6605435) baseStart_6605435 baseEnd_6605435 := by
    simpa [prefixWord, tailWord_6605435, baseEnd_6605435] using wordTrace_append hprefix tailTrace_6605435
  have hstable : (prefixWord ++ tailWord_6605435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605435).length < 2 ^ (prefixWord ++ tailWord_6605435).sum := by decide
  have hdescent : baseEnd_6605435 < baseStart_6605435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605439 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 7, 2, 2]
def baseStart_6605439 : Nat := 118140960795 + 6605439 * 2 ^ 59
def prefixEnd_6605439 : Nat := 4983230072969 + 3 ^ 40 * 6605439 * 2
def baseEnd_6605439 : Nat := 3391765140954086923234645

theorem tailTrace_6605439 : CollatzResearch.WordTrace tailWord_6605439 prefixEnd_6605439 3391765140954086923234645 := by
  unfold tailWord_6605439
  simp only [CollatzResearch.WordTrace]
  refine ⟨240920152716630097012155371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160613435144420064674770247 240920152716630097012155371)
  ·
    refine ⟨361380229074945145518233057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240920152716630097012155371 361380229074945145518233057)
    ·
      refine ⟨271035171806208859138674793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361380229074945145518233057 271035171806208859138674793)
      ·
        refine ⟨203276378854656644354006095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271035171806208859138674793 203276378854656644354006095)
        ·
          refine ⟨304914568281984966531009143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203276378854656644354006095 304914568281984966531009143)
          ·
            refine ⟨457371852422977449796513715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304914568281984966531009143 457371852422977449796513715)
            ·
              refine ⟨686057778634466174694770573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457371852422977449796513715 686057778634466174694770573)
              ·
                refine ⟨257271666987924815510538965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 686057778634466174694770573 257271666987924815510538965)
                ·
                  refine ⟨6029804695029487863528257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 257271666987924815510538965 6029804695029487863528257)
                  ·
                    refine ⟨4522353521272115897646193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6029804695029487863528257 4522353521272115897646193)
                    ·
                      refine ⟨3391765140954086923234645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522353521272115897646193 3391765140954086923234645)
                      ·
                        rfl

theorem cell23_6605439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 7, 2, 2].length) (baseStart_6605439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605439 prefixEnd_6605439 := by exact prefixLift 6605439
  have htrace : WordTrace (prefixWord ++ tailWord_6605439) baseStart_6605439 baseEnd_6605439 := by
    simpa [prefixWord, tailWord_6605439, baseEnd_6605439] using wordTrace_append hprefix tailTrace_6605439
  have hstable : (prefixWord ++ tailWord_6605439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605439).length < 2 ^ (prefixWord ++ tailWord_6605439).sum := by decide
  have hdescent : baseEnd_6605439 < baseStart_6605439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605445 : List Nat := [1, 3, 1, 1, 4, 13]
def baseStart_6605445 : Nat := 118140960795 + 6605445 * 2 ^ 59
def prefixEnd_6605445 : Nat := 4983230072969 + 3 ^ 40 * 6605445 * 2
def baseEnd_6605445 : Nat := 13957893917028863785019

theorem tailTrace_6605445 : CollatzResearch.WordTrace tailWord_6605445 prefixEnd_6605445 13957893917028863785019 := by
  unfold tailWord_6605445
  simp only [CollatzResearch.WordTrace]
  refine ⟨240920371554608360036873789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160613581036405573357915859 240920371554608360036873789)
  ·
    refine ⟨90345139332978135013827671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240920371554608360036873789 90345139332978135013827671)
    ·
      refine ⟨135517708999467202520741507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90345139332978135013827671 135517708999467202520741507)
      ·
        refine ⟨203276563499200803781112261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135517708999467202520741507 203276563499200803781112261)
        ·
          refine ⟨38114355656100150708958549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203276563499200803781112261 38114355656100150708958549)
          ·
            refine ⟨13957893917028863785019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 38114355656100150708958549 13957893917028863785019)
            ·
              rfl

theorem cell23_6605445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 13].length) (baseStart_6605445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605445 prefixEnd_6605445 := by exact prefixLift 6605445
  have htrace : WordTrace (prefixWord ++ tailWord_6605445) baseStart_6605445 baseEnd_6605445 := by
    simpa [prefixWord, tailWord_6605445, baseEnd_6605445] using wordTrace_append hprefix tailTrace_6605445
  have hstable : (prefixWord ++ tailWord_6605445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605445).length < 2 ^ (prefixWord ++ tailWord_6605445).sum := by decide
  have hdescent : baseEnd_6605445 < baseStart_6605445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605466 : List Nat := [3, 1, 1, 6, 1, 1, 2, 1, 1, 6]
def baseStart_6605466 : Nat := 118140960795 + 6605466 * 2 ^ 59
def prefixEnd_6605466 : Nat := 4983230072969 + 3 ^ 40 * 6605466 * 2
def baseEnd_6605466 : Nat := 1130593001643919439199007

theorem tailTrace_6605466 : CollatzResearch.WordTrace tailWord_6605466 prefixEnd_6605466 1130593001643919439199007 := by
  unfold tailWord_6605466
  simp only [CollatzResearch.WordTrace]
  refine ⟨60230284371883070155847063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160614091658354853748925501 60230284371883070155847063)
  ·
    refine ⟨90345426557824605233770595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60230284371883070155847063 90345426557824605233770595)
    ·
      refine ⟨135518139836736907850655893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90345426557824605233770595 135518139836736907850655893)
      ·
        refine ⟨6352412804847042555499495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135518139836736907850655893 6352412804847042555499495)
        ·
          refine ⟨9528619207270563833249243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6352412804847042555499495 9528619207270563833249243)
          ·
            refine ⟨14292928810905845749873865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9528619207270563833249243 14292928810905845749873865)
            ·
              refine ⟨10719696608179384312405399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14292928810905845749873865 10719696608179384312405399)
              ·
                refine ⟨16079544912269076468608099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10719696608179384312405399 16079544912269076468608099)
                ·
                  refine ⟨24119317368403614702912149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16079544912269076468608099 24119317368403614702912149)
                  ·
                    refine ⟨1130593001643919439199007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24119317368403614702912149 1130593001643919439199007)
                    ·
                      rfl

theorem cell23_6605466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 1, 2, 1, 1, 6].length) (baseStart_6605466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605466 prefixEnd_6605466 := by exact prefixLift 6605466
  have htrace : WordTrace (prefixWord ++ tailWord_6605466) baseStart_6605466 baseEnd_6605466 := by
    simpa [prefixWord, tailWord_6605466, baseEnd_6605466] using wordTrace_append hprefix tailTrace_6605466
  have hstable : (prefixWord ++ tailWord_6605466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605466).length < 2 ^ (prefixWord ++ tailWord_6605466).sum := by decide
  have hdescent : baseEnd_6605466 < baseStart_6605466 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605473 : List Nat := [1, 2, 3, 3, 3, 1, 1, 2, 3, 2, 2]
def baseStart_6605473 : Nat := 118140960795 + 6605473 * 2 ^ 59
def prefixEnd_6605473 : Nat := 4983230072969 + 3 ^ 40 * 6605473 * 2
def baseEnd_6605473 : Nat := 3391782599296339790209489

theorem tailTrace_6605473 : CollatzResearch.WordTrace tailWord_6605473 prefixEnd_6605473 3391782599296339790209489 := by
  unfold tailWord_6605473
  simp only [CollatzResearch.WordTrace]
  refine ⟨240921392798506920818893073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160614261865671280545928715 240921392798506920818893073)
  ·
    refine ⟨180691044598880190614169805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240921392798506920818893073 180691044598880190614169805)
    ·
      refine ⟨67759141724580071480313677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180691044598880190614169805 67759141724580071480313677)
      ·
        refine ⟨25409678146717526805117629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67759141724580071480313677 25409678146717526805117629)
        ·
          refine ⟨9528629305019072551919111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25409678146717526805117629 9528629305019072551919111)
          ·
            refine ⟨14292943957528608827878667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9528629305019072551919111 14292943957528608827878667)
            ·
              refine ⟨21439415936292913241818001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14292943957528608827878667 21439415936292913241818001)
              ·
                refine ⟨16079561952219684931363501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21439415936292913241818001 16079561952219684931363501)
                ·
                  refine ⟨6029835732082381849261313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16079561952219684931363501 6029835732082381849261313)
                  ·
                    refine ⟨4522376799061786386945985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6029835732082381849261313 4522376799061786386945985)
                    ·
                      refine ⟨3391782599296339790209489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522376799061786386945985 3391782599296339790209489)
                      ·
                        rfl

theorem cell23_6605473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_6605473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605473 prefixEnd_6605473 := by exact prefixLift 6605473
  have htrace : WordTrace (prefixWord ++ tailWord_6605473) baseStart_6605473 baseEnd_6605473 := by
    simpa [prefixWord, tailWord_6605473, baseEnd_6605473] using wordTrace_append hprefix tailTrace_6605473
  have hstable : (prefixWord ++ tailWord_6605473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605473).length < 2 ^ (prefixWord ++ tailWord_6605473).sum := by decide
  have hdescent : baseEnd_6605473 < baseStart_6605473 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605486 : List Nat := [4, 1, 4, 1, 1, 1, 2, 2, 1, 2, 4]
def baseStart_6605486 : Nat := 118140960795 + 6605486 * 2 ^ 59
def prefixEnd_6605486 : Nat := 4983230072969 + 3 ^ 40 * 6605486 * 2
def baseEnd_6605486 : Nat := 3391789274544848239346929

theorem tailTrace_6605486 : CollatzResearch.WordTrace tailWord_6605486 prefixEnd_6605486 3391789274544848239346929 := by
  unfold tailWord_6605486
  simp only [CollatzResearch.WordTrace]
  refine ⟨30115233368432478004889539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160614577964973216026077541 30115233368432478004889539)
  ·
    refine ⟨45172850052648717007334309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30115233368432478004889539 45172850052648717007334309)
    ·
      refine ⟨8469909384871634438875183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45172850052648717007334309 8469909384871634438875183)
      ·
        refine ⟨12704864077307451658312775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8469909384871634438875183 12704864077307451658312775)
        ·
          refine ⟨19057296115961177487469163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12704864077307451658312775 19057296115961177487469163)
          ·
            refine ⟨28585944173941766231203745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19057296115961177487469163 28585944173941766231203745)
            ·
              refine ⟨21439458130456324673402809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28585944173941766231203745 21439458130456324673402809)
              ·
                refine ⟨16079593597842243505052107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21439458130456324673402809 16079593597842243505052107)
                ·
                  refine ⟨24119390396763365257578161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16079593597842243505052107 24119390396763365257578161)
                  ·
                    refine ⟨18089542797572523943183621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24119390396763365257578161 18089542797572523943183621)
                    ·
                      refine ⟨3391789274544848239346929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18089542797572523943183621 3391789274544848239346929)
                      ·
                        rfl

theorem cell23_6605486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_6605486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605486 prefixEnd_6605486 := by exact prefixLift 6605486
  have htrace : WordTrace (prefixWord ++ tailWord_6605486) baseStart_6605486 baseEnd_6605486 := by
    simpa [prefixWord, tailWord_6605486, baseEnd_6605486] using wordTrace_append hprefix tailTrace_6605486
  have hstable : (prefixWord ++ tailWord_6605486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605486).length < 2 ^ (prefixWord ++ tailWord_6605486).sum := by decide
  have hdescent : baseEnd_6605486 < baseStart_6605486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605493 : List Nat := [1, 3, 3, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_6605493 : Nat := 118140960795 + 6605493 * 2 ^ 59
def prefixEnd_6605493 : Nat := 4983230072969 + 3 ^ 40 * 6605493 * 2
def baseEnd_6605493 : Nat := 3391792868909429711959397

theorem tailTrace_6605493 : CollatzResearch.WordTrace tailWord_6605493 prefixEnd_6605493 3391792868909429711959397 := by
  unfold tailWord_6605493
  simp only [CollatzResearch.WordTrace]
  refine ⟨240922122258434464234621133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160614748172289642823080755 240922122258434464234621133)
  ·
    refine ⟨90345795846912924087982925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240922122258434464234621133 90345795846912924087982925)
    ·
      refine ⟨33879673442592346532993597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90345795846912924087982925 33879673442592346532993597)
      ·
        refine ⟨12704877540972129949872599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33879673442592346532993597 12704877540972129949872599)
        ·
          refine ⟨19057316311458194924808899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12704877540972129949872599 19057316311458194924808899)
          ·
            refine ⟨28585974467187292387213349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19057316311458194924808899 28585974467187292387213349)
            ·
              refine ⟨5359870212597617322602503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28585974467187292387213349 5359870212597617322602503)
              ·
                refine ⟨8039805318896425983903755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5359870212597617322602503 8039805318896425983903755)
                ·
                  refine ⟨12059707978344638975855633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8039805318896425983903755 12059707978344638975855633)
                  ·
                    refine ⟨9044780983758479231891725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12059707978344638975855633 9044780983758479231891725)
                    ·
                      refine ⟨3391792868909429711959397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9044780983758479231891725 3391792868909429711959397)
                      ·
                        rfl

theorem cell23_6605493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_6605493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605493 prefixEnd_6605493 := by exact prefixLift 6605493
  have htrace : WordTrace (prefixWord ++ tailWord_6605493) baseStart_6605493 baseEnd_6605493 := by
    simpa [prefixWord, tailWord_6605493, baseEnd_6605493] using wordTrace_append hprefix tailTrace_6605493
  have hstable : (prefixWord ++ tailWord_6605493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605493).length < 2 ^ (prefixWord ++ tailWord_6605493).sum := by decide
  have hdescent : baseEnd_6605493 < baseStart_6605493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605549 : List Nat := [1, 5, 1, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_6605549 : Nat := 118140960795 + 6605549 * 2 ^ 59
def prefixEnd_6605549 : Nat := 4983230072969 + 3 ^ 40 * 6605549 * 2
def baseEnd_6605549 : Nat := 3391821623826081492859139

theorem tailTrace_6605549 : CollatzResearch.WordTrace tailWord_6605549 prefixEnd_6605549 3391821623826081492859139 := by
  unfold tailWord_6605549
  simp only [CollatzResearch.WordTrace]
  refine ⟨240924164746231585798659701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160616109830821057199106467 240924164746231585798659701)
  ·
    refine ⟨22586640444959211168624347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 240924164746231585798659701 22586640444959211168624347)
    ·
      refine ⟨33879960667438816752936521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22586640444959211168624347 33879960667438816752936521)
      ·
        refine ⟨25409970500579112564702391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33879960667438816752936521 25409970500579112564702391)
        ·
          refine ⟨38114955750868668847053587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25409970500579112564702391 38114955750868668847053587)
          ·
            refine ⟨57172433626303003270580381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38114955750868668847053587 57172433626303003270580381)
            ·
              refine ⟨21439662609863626226467643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57172433626303003270580381 21439662609863626226467643)
              ·
                refine ⟨32159493914795439339701465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21439662609863626226467643 32159493914795439339701465)
                ·
                  refine ⟨24119620436096579504776099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32159493914795439339701465 24119620436096579504776099)
                  ·
                    refine ⟨36179430654144869257164149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24119620436096579504776099 36179430654144869257164149)
                    ·
                      refine ⟨3391821623826081492859139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36179430654144869257164149 3391821623826081492859139)
                      ·
                        rfl

theorem cell23_6605549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_6605549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605549 prefixEnd_6605549 := by exact prefixLift 6605549
  have htrace : WordTrace (prefixWord ++ tailWord_6605549) baseStart_6605549 baseEnd_6605549 := by
    simpa [prefixWord, tailWord_6605549, baseEnd_6605549] using wordTrace_append hprefix tailTrace_6605549
  have hstable : (prefixWord ++ tailWord_6605549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605549).length < 2 ^ (prefixWord ++ tailWord_6605549).sum := by decide
  have hdescent : baseEnd_6605549 < baseStart_6605549 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605592 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_6605592 : Nat := 118140960795 + 6605592 * 2 ^ 59
def prefixEnd_6605592 : Nat := 4983230072969 + 3 ^ 40 * 6605592 * 2
def baseEnd_6605592 : Nat := 3391843703494224824621441

theorem tailTrace_6605592 : CollatzResearch.WordTrace tailWord_6605592 prefixEnd_6605592 3391843703494224824621441 := by
  unfold tailWord_6605592
  simp only [CollatzResearch.WordTrace]
  refine ⟨120462866542537902071237515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160617155390050536094983353 120462866542537902071237515)
  ·
    refine ⟨180694299813806853106856273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120462866542537902071237515 180694299813806853106856273)
    ·
      refine ⟨135520724860355139830142205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180694299813806853106856273 135520724860355139830142205)
      ·
        refine ⟨50820271822633177436303327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135520724860355139830142205 50820271822633177436303327)
        ·
          refine ⟨76230407733949766154454991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50820271822633177436303327 76230407733949766154454991)
          ·
            refine ⟨114345611600924649231682487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76230407733949766154454991 114345611600924649231682487)
            ·
              refine ⟨171518417401386973847523731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114345611600924649231682487 171518417401386973847523731)
              ·
                refine ⟨257277626102080460771285597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171518417401386973847523731 257277626102080460771285597)
                ·
                  refine ⟨96479109788280172789232099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257277626102080460771285597 96479109788280172789232099)
                  ·
                    refine ⟨144718664682420259183848149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96479109788280172789232099 144718664682420259183848149)
                    ·
                      refine ⟨3391843703494224824621441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144718664682420259183848149 3391843703494224824621441)
                      ·
                        rfl

theorem cell23_6605592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_6605592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605592 prefixEnd_6605592 := by exact prefixLift 6605592
  have htrace : WordTrace (prefixWord ++ tailWord_6605592) baseStart_6605592 baseEnd_6605592 := by
    simpa [prefixWord, tailWord_6605592, baseEnd_6605592] using wordTrace_append hprefix tailTrace_6605592
  have hstable : (prefixWord ++ tailWord_6605592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605592).length < 2 ^ (prefixWord ++ tailWord_6605592).sum := by decide
  have hdescent : baseEnd_6605592 < baseStart_6605592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605599 : List Nat := [1, 1, 2, 4, 2, 2, 1, 3, 2, 5]
def baseStart_6605599 : Nat := 118140960795 + 6605599 * 2 ^ 59
def prefixEnd_6605599 : Nat := 4983230072969 + 3 ^ 40 * 6605599 * 2
def baseEnd_6605599 : Nat := 1130615765952935432411303

theorem tailTrace_6605599 : CollatzResearch.WordTrace tailWord_6605599 prefixEnd_6605599 1130615765952935432411303 := by
  unfold tailWord_6605599
  simp only [CollatzResearch.WordTrace]
  refine ⟨240925988396050444337979851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160617325597366962891986567 240925988396050444337979851)
  ·
    refine ⟨361388982594075666506969777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240925988396050444337979851 361388982594075666506969777)
    ·
      refine ⟨271041736945556749880227333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361388982594075666506969777 271041736945556749880227333)
      ·
        refine ⟨50820325677291890602542625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271041736945556749880227333 50820325677291890602542625)
        ·
          refine ⟨38115244257968917951906969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50820325677291890602542625 38115244257968917951906969)
          ·
            refine ⟨28586433193476688463930227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38115244257968917951906969 28586433193476688463930227)
            ·
              refine ⟨42879649790215032695895341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28586433193476688463930227 42879649790215032695895341)
              ·
                refine ⟨16079868671330637260960753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42879649790215032695895341 16079868671330637260960753)
                ·
                  refine ⟨12059901503497977945720565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16079868671330637260960753 12059901503497977945720565)
                  ·
                    refine ⟨1130615765952935432411303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12059901503497977945720565 1130615765952935432411303)
                    ·
                      rfl

theorem cell23_6605599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3, 2, 5].length) (baseStart_6605599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605599 prefixEnd_6605599 := by exact prefixLift 6605599
  have htrace : WordTrace (prefixWord ++ tailWord_6605599) baseStart_6605599 baseEnd_6605599 := by
    simpa [prefixWord, tailWord_6605599, baseEnd_6605599] using wordTrace_append hprefix tailTrace_6605599
  have hstable : (prefixWord ++ tailWord_6605599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605599).length < 2 ^ (prefixWord ++ tailWord_6605599).sum := by decide
  have hdescent : baseEnd_6605599 < baseStart_6605599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605639 : List Nat := [1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_6605639 : Nat := 118140960795 + 6605639 * 2 ^ 59
def prefixEnd_6605639 : Nat := 4983230072969 + 3 ^ 40 * 6605639 * 2
def baseEnd_6605639 : Nat := 3391867837084986140733725

theorem tailTrace_6605639 : CollatzResearch.WordTrace tailWord_6605639 prefixEnd_6605639 3391867837084986140733725 := by
  unfold tailWord_6605639
  simp only [CollatzResearch.WordTrace]
  refine ⟨240927447315905531169435971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160618298210603687446290647 240927447315905531169435971)
  ·
    refine ⟨361391170973858296754153957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240927447315905531169435971 361391170973858296754153957)
    ·
      refine ⟨67760844557598430641403867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361391170973858296754153957 67760844557598430641403867)
      ·
        refine ⟨101641266836397645962105801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67760844557598430641403867 101641266836397645962105801)
        ·
          refine ⟨76230950127298234471579351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101641266836397645962105801 76230950127298234471579351)
          ·
            refine ⟨114346425190947351707369027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76230950127298234471579351 114346425190947351707369027)
            ·
              refine ⟨171519637786421027561053541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114346425190947351707369027 171519637786421027561053541)
              ·
                refine ⟨32159932084953942667697539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171519637786421027561053541 32159932084953942667697539)
                ·
                  refine ⟨48239898127430914001546309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32159932084953942667697539 48239898127430914001546309)
                  ·
                    refine ⟨9044980898893296375289933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48239898127430914001546309 9044980898893296375289933)
                    ·
                      refine ⟨3391867837084986140733725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9044980898893296375289933 3391867837084986140733725)
                      ·
                        rfl

theorem cell23_6605639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_6605639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605639 prefixEnd_6605639 := by exact prefixLift 6605639
  have htrace : WordTrace (prefixWord ++ tailWord_6605639) baseStart_6605639 baseEnd_6605639 := by
    simpa [prefixWord, tailWord_6605639, baseEnd_6605639] using wordTrace_append hprefix tailTrace_6605639
  have hstable : (prefixWord ++ tailWord_6605639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605639).length < 2 ^ (prefixWord ++ tailWord_6605639).sum := by decide
  have hdescent : baseEnd_6605639 < baseStart_6605639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605663 : List Nat := [1, 1, 2, 3, 1, 3, 4, 3, 1, 4]
def baseStart_6605663 : Nat := 118140960795 + 6605663 * 2 ^ 59
def prefixEnd_6605663 : Nat := 4983230072969 + 3 ^ 40 * 6605663 * 2
def baseEnd_6605663 : Nat := 1130626720206898015611205

theorem tailTrace_6605663 : CollatzResearch.WordTrace tailWord_6605663 prefixEnd_6605663 1130626720206898015611205 := by
  unfold tailWord_6605663
  simp only [CollatzResearch.WordTrace]
  refine ⟨240928322667818583268309643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160618881778545722178873095 240928322667818583268309643)
  ·
    refine ⟨361392484001727874902464465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240928322667818583268309643 361392484001727874902464465)
    ·
      refine ⟨271044363001295906176848349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361392484001727874902464465 271044363001295906176848349)
      ·
        refine ⟨101641636125485964816318131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271044363001295906176848349 101641636125485964816318131)
        ·
          refine ⟨152462454188228947224477197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101641636125485964816318131 152462454188228947224477197)
          ·
            refine ⟨57173420320585855209178949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152462454188228947224477197 57173420320585855209178949)
            ·
              refine ⟨10720016310109847851721053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57173420320585855209178949 10720016310109847851721053)
              ·
                refine ⟨4020006116291192944395395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10720016310109847851721053 4020006116291192944395395)
                ·
                  refine ⟨6030009174436789416593093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4020006116291192944395395 6030009174436789416593093)
                  ·
                    refine ⟨1130626720206898015611205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6030009174436789416593093 1130626720206898015611205)
                    ·
                      rfl

theorem cell23_6605663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 3, 1, 4].length) (baseStart_6605663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605663 prefixEnd_6605663 := by exact prefixLift 6605663
  have htrace : WordTrace (prefixWord ++ tailWord_6605663) baseStart_6605663 baseEnd_6605663 := by
    simpa [prefixWord, tailWord_6605663, baseEnd_6605663] using wordTrace_append hprefix tailTrace_6605663
  have hstable : (prefixWord ++ tailWord_6605663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605663).length < 2 ^ (prefixWord ++ tailWord_6605663).sum := by decide
  have hdescent : baseEnd_6605663 < baseStart_6605663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605696 : List Nat := [2, 1, 1, 2, 1, 2, 2, 1, 6, 3, 2]
def baseStart_6605696 : Nat := 118140960795 + 6605696 * 2 ^ 59
def prefixEnd_6605696 : Nat := 4983230072969 + 3 ^ 40 * 6605696 * 2
def baseEnd_6605696 : Nat := 3391897105482292417720963

theorem tailTrace_6605696 : CollatzResearch.WordTrace tailWord_6605696 prefixEnd_6605696 3391897105482292417720963 := by
  unfold tailWord_6605696
  simp only [CollatzResearch.WordTrace]
  refine ⟨120464763138349514952130471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160619684184466019936173961 120464763138349514952130471)
  ·
    refine ⟨180697144707524272428195707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120464763138349514952130471 180697144707524272428195707)
    ·
      refine ⟨271045717061286408642293561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180697144707524272428195707 271045717061286408642293561)
      ·
        refine ⟨203284287795964806481720171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271045717061286408642293561 203284287795964806481720171)
        ·
          refine ⟨304926431693947209722580257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203284287795964806481720171 304926431693947209722580257)
          ·
            refine ⟨228694823770460407291935193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304926431693947209722580257 228694823770460407291935193)
            ·
              refine ⟨171521117827845305468951395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228694823770460407291935193 171521117827845305468951395)
              ·
                refine ⟨257281676741767958203427093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171521117827845305468951395 257281676741767958203427093)
                ·
                  refine ⟨12060078597270373040785645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 257281676741767958203427093 12060078597270373040785645)
                  ·
                    refine ⟨4522529473976389890294617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12060078597270373040785645 4522529473976389890294617)
                    ·
                      refine ⟨3391897105482292417720963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522529473976389890294617 3391897105482292417720963)
                      ·
                        rfl

theorem cell23_6605696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 6, 3, 2].length) (baseStart_6605696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605696 prefixEnd_6605696 := by exact prefixLift 6605696
  have htrace : WordTrace (prefixWord ++ tailWord_6605696) baseStart_6605696 baseEnd_6605696 := by
    simpa [prefixWord, tailWord_6605696, baseEnd_6605696] using wordTrace_append hprefix tailTrace_6605696
  have hstable : (prefixWord ++ tailWord_6605696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605696).length < 2 ^ (prefixWord ++ tailWord_6605696).sum := by decide
  have hdescent : baseEnd_6605696 < baseStart_6605696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605703 : List Nat := [1, 1, 4, 2, 3, 1, 2, 2, 3, 1, 3]
def baseStart_6605703 : Nat := 118140960795 + 6605703 * 2 ^ 59
def prefixEnd_6605703 : Nat := 4983230072969 + 3 ^ 40 * 6605703 * 2
def baseEnd_6605703 : Nat := 3391900699846873890333431

theorem tailTrace_6605703 : CollatzResearch.WordTrace tailWord_6605703 prefixEnd_6605703 3391900699846873890333431 := by
  unfold tailWord_6605703
  simp only [CollatzResearch.WordTrace]
  refine ⟨240929781587673670099765763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160619854391782446733177175 240929781587673670099765763)
  ·
    refine ⟨361394672381510505149648645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240929781587673670099765763 361394672381510505149648645)
    ·
      refine ⟨67761501071533219715559121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361394672381510505149648645 67761501071533219715559121)
      ·
        refine ⟨50821125803649914786669341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67761501071533219715559121 50821125803649914786669341)
        ·
          refine ⟨19057922176368718045001003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50821125803649914786669341 19057922176368718045001003)
          ·
            refine ⟨28586883264553077067501505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19057922176368718045001003 28586883264553077067501505)
            ·
              refine ⟨21440162448414807800626129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28586883264553077067501505 21440162448414807800626129)
              ·
                refine ⟨16080121836311105850469597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21440162448414807800626129 16080121836311105850469597)
                ·
                  refine ⟨6030045688616664693926099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16080121836311105850469597 6030045688616664693926099)
                  ·
                    refine ⟨9045068532924997040889149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6030045688616664693926099 9045068532924997040889149)
                    ·
                      refine ⟨3391900699846873890333431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9045068532924997040889149 3391900699846873890333431)
                      ·
                        rfl

theorem cell23_6605703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_6605703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605703 prefixEnd_6605703 := by exact prefixLift 6605703
  have htrace : WordTrace (prefixWord ++ tailWord_6605703) baseStart_6605703 baseEnd_6605703 := by
    simpa [prefixWord, tailWord_6605703, baseEnd_6605703] using wordTrace_append hprefix tailTrace_6605703
  have hstable : (prefixWord ++ tailWord_6605703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605703).length < 2 ^ (prefixWord ++ tailWord_6605703).sum := by decide
  have hdescent : baseEnd_6605703 < baseStart_6605703 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605714 : List Nat := [3, 2, 3, 2, 3, 1, 1, 3, 1, 4]
def baseStart_6605714 : Nat := 118140960795 + 6605714 * 2 ^ 59
def prefixEnd_6605714 : Nat := 4983230072969 + 3 ^ 40 * 6605714 * 2
def baseEnd_6605714 : Nat := 1130635449378024449098627

theorem tailTrace_6605714 : CollatzResearch.WordTrace tailWord_6605714 prefixEnd_6605714 1130635449378024449098627 := by
  unfold tailWord_6605714
  simp only [CollatzResearch.WordTrace]
  refine ⟨60232545697658454744604049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160620121860422545985610797 60232545697658454744604049)
  ·
    refine ⟨45174409273243841058453037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60232545697658454744604049 45174409273243841058453037)
    ·
      refine ⟨16940403477466440396919889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45174409273243841058453037 16940403477466440396919889)
      ·
        refine ⟨12705302608099830297689917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16940403477466440396919889 12705302608099830297689917)
        ·
          refine ⟨4764488478037436361633719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12705302608099830297689917 4764488478037436361633719)
          ·
            refine ⟨7146732717056154542450579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4764488478037436361633719 7146732717056154542450579)
            ·
              refine ⟨10720099075584231813675869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7146732717056154542450579 10720099075584231813675869)
              ·
                refine ⟨4020037153344086930128451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10720099075584231813675869 4020037153344086930128451)
                ·
                  refine ⟨6030055730016130395192677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4020037153344086930128451 6030055730016130395192677)
                  ·
                    refine ⟨1130635449378024449098627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6030055730016130395192677 1130635449378024449098627)
                    ·
                      rfl

theorem cell23_6605714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_6605714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605714 prefixEnd_6605714 := by exact prefixLift 6605714
  have htrace : WordTrace (prefixWord ++ tailWord_6605714) baseStart_6605714 baseEnd_6605714 := by
    simpa [prefixWord, tailWord_6605714, baseEnd_6605714] using wordTrace_append hprefix tailTrace_6605714
  have hstable : (prefixWord ++ tailWord_6605714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605714).length < 2 ^ (prefixWord ++ tailWord_6605714).sum := by decide
  have hdescent : baseEnd_6605714 < baseStart_6605714 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605719 : List Nat := [1, 1, 3, 3, 1, 2, 2, 1, 3, 6]
def baseStart_6605719 : Nat := 118140960795 + 6605719 * 2 ^ 59
def prefixEnd_6605719 : Nat := 4983230072969 + 3 ^ 40 * 6605719 * 2
def baseEnd_6605719 : Nat := 1130636305179115275911119

theorem tailTrace_6605719 : CollatzResearch.WordTrace tailWord_6605719 prefixEnd_6605719 1130636305179115275911119 := by
  unfold tailWord_6605719
  simp only [CollatzResearch.WordTrace]
  refine ⟨240930365155615704832348211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160620243437077136554898807 240930365155615704832348211)
  ·
    refine ⟨361395547733423557248522317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240930365155615704832348211 361395547733423557248522317)
    ·
      refine ⟨135523330400033833968195869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361395547733423557248522317 135523330400033833968195869)
      ·
        refine ⟨50821248900012687738073451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135523330400033833968195869 50821248900012687738073451)
        ·
          refine ⟨76231873350019031607110177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50821248900012687738073451 76231873350019031607110177)
          ·
            refine ⟨57173905012514273705332633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76231873350019031607110177 57173905012514273705332633)
            ·
              refine ⟨42880428759385705278999475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57173905012514273705332633 42880428759385705278999475)
              ·
                refine ⟨64320643139078557918499213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42880428759385705278999475 64320643139078557918499213)
                ·
                  refine ⟨24120241177154459219437205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64320643139078557918499213 24120241177154459219437205)
                  ·
                    refine ⟨1130636305179115275911119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24120241177154459219437205 1130636305179115275911119)
                    ·
                      rfl

theorem cell23_6605719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 1, 3, 6].length) (baseStart_6605719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605719 prefixEnd_6605719 := by exact prefixLift 6605719
  have htrace : WordTrace (prefixWord ++ tailWord_6605719) baseStart_6605719 baseEnd_6605719 := by
    simpa [prefixWord, tailWord_6605719, baseEnd_6605719] using wordTrace_append hprefix tailTrace_6605719
  have hstable : (prefixWord ++ tailWord_6605719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605719).length < 2 ^ (prefixWord ++ tailWord_6605719).sum := by decide
  have hdescent : baseEnd_6605719 < baseStart_6605719 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605730 : List Nat := [3, 3, 1, 2, 2, 2, 1, 2, 2, 3, 2]
def baseStart_6605730 : Nat := 118140960795 + 6605730 * 2 ^ 59
def prefixEnd_6605730 : Nat := 4983230072969 + 3 ^ 40 * 6605730 * 2
def baseEnd_6605730 : Nat := 3391914563824545284695807

theorem tailTrace_6605730 : CollatzResearch.WordTrace tailWord_6605730 prefixEnd_6605730 3391914563824545284695807 := by
  unfold tailWord_6605730
  simp only [CollatzResearch.WordTrace]
  refine ⟨60232691589643963427749661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160620510905717235807332429 60232691589643963427749661)
  ·
    refine ⟨22587259346116486285406123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60232691589643963427749661 22587259346116486285406123)
    ·
      refine ⟨33880889019174729428109185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22587259346116486285406123 33880889019174729428109185)
      ·
        refine ⟨25410666764381047071081889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33880889019174729428109185 25410666764381047071081889)
        ·
          refine ⟨19058000073285785303311417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25410666764381047071081889 19058000073285785303311417)
          ·
            refine ⟨14293500054964338977483563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19058000073285785303311417 14293500054964338977483563)
            ·
              refine ⟨21440250082446508466225345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14293500054964338977483563 21440250082446508466225345)
              ·
                refine ⟨16080187561834881349669009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21440250082446508466225345 16080187561834881349669009)
                ·
                  refine ⟨12060140671376161012251757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16080187561834881349669009 12060140671376161012251757)
                  ·
                    refine ⟨4522552751766060379594409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12060140671376161012251757 4522552751766060379594409)
                    ·
                      refine ⟨3391914563824545284695807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522552751766060379594409 3391914563824545284695807)
                      ·
                        rfl

theorem cell23_6605730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_6605730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605730 prefixEnd_6605730 := by exact prefixLift 6605730
  have htrace : WordTrace (prefixWord ++ tailWord_6605730) baseStart_6605730 baseEnd_6605730 := by
    simpa [prefixWord, tailWord_6605730, baseEnd_6605730] using wordTrace_append hprefix tailTrace_6605730
  have hstable : (prefixWord ++ tailWord_6605730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605730).length < 2 ^ (prefixWord ++ tailWord_6605730).sum := by decide
  have hdescent : baseEnd_6605730 < baseStart_6605730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605739 : List Nat := [1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 4]
def baseStart_6605739 : Nat := 118140960795 + 6605739 * 2 ^ 59
def prefixEnd_6605739 : Nat := 4983230072969 + 3 ^ 40 * 6605739 * 2
def baseEnd_6605739 : Nat := 3391919185150435749483265

theorem tailTrace_6605739 : CollatzResearch.WordTrace tailWord_6605739 prefixEnd_6605739 3391919185150435749483265 := by
  unfold tailWord_6605739
  simp only [CollatzResearch.WordTrace]
  refine ⟨240931094615543248248076271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160620729743695498832050847 240931094615543248248076271)
  ·
    refine ⟨361396641923314872372114407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240931094615543248248076271 361396641923314872372114407)
    ·
      refine ⟨542094962884972308558171611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361396641923314872372114407 542094962884972308558171611)
      ·
        refine ⟨813142444327458462837257417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542094962884972308558171611 813142444327458462837257417)
        ·
          refine ⟨609856833245593847127943063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 813142444327458462837257417 609856833245593847127943063)
          ·
            refine ⟨914785249868390770691914595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609856833245593847127943063 914785249868390770691914595)
            ·
              refine ⟨1372177874802586156037871893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 914785249868390770691914595 1372177874802586156037871893)
              ·
                refine ⟨64320837881371226064275245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1372177874802586156037871893 64320837881371226064275245)
                ·
                  refine ⟨24120314205514209774103217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64320837881371226064275245 24120314205514209774103217)
                  ·
                    refine ⟨18090235654135657330577413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24120314205514209774103217 18090235654135657330577413)
                    ·
                      refine ⟨3391919185150435749483265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18090235654135657330577413 3391919185150435749483265)
                      ·
                        rfl

theorem cell23_6605739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 4].length) (baseStart_6605739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605739 prefixEnd_6605739 := by exact prefixLift 6605739
  have htrace : WordTrace (prefixWord ++ tailWord_6605739) baseStart_6605739 baseEnd_6605739 := by
    simpa [prefixWord, tailWord_6605739, baseEnd_6605739] using wordTrace_append hprefix tailTrace_6605739
  have hstable : (prefixWord ++ tailWord_6605739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605739).length < 2 ^ (prefixWord ++ tailWord_6605739).sum := by decide
  have hdescent : baseEnd_6605739 < baseStart_6605739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605743 : List Nat := [1, 1, 2, 1, 2, 2, 2, 5, 3, 2, 2]
def baseStart_6605743 : Nat := 118140960795 + 6605743 * 2 ^ 59
def prefixEnd_6605743 : Nat := 4983230072969 + 3 ^ 40 * 6605743 * 2
def baseEnd_6605743 : Nat := 3391921239073053733833247

theorem tailTrace_6605743 : CollatzResearch.WordTrace tailWord_6605743 prefixEnd_6605743 3391921239073053733833247 := by
  unfold tailWord_6605743
  simp only [CollatzResearch.WordTrace]
  refine ⟨240931240507528756931221883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160620827005019171287481255 240931240507528756931221883)
  ·
    refine ⟨361396860761293135396832825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240931240507528756931221883 361396860761293135396832825)
    ·
      refine ⟨271047645570969851547624619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361396860761293135396832825 271047645570969851547624619)
      ·
        refine ⟨406571468356454777321436929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271047645570969851547624619 406571468356454777321436929)
        ·
          refine ⟨304928601267341082991077697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406571468356454777321436929 304928601267341082991077697)
          ·
            refine ⟨228696450950505812243308273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304928601267341082991077697 228696450950505812243308273)
            ·
              refine ⟨171522338212879359182481205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228696450950505812243308273 171522338212879359182481205)
              ·
                refine ⟨16080219207457439923357613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 171522338212879359182481205 16080219207457439923357613)
                ·
                  refine ⟨6030082202796539971259105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16080219207457439923357613 6030082202796539971259105)
                  ·
                    refine ⟨4522561652097404978444329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6030082202796539971259105 4522561652097404978444329)
                    ·
                      refine ⟨3391921239073053733833247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522561652097404978444329 3391921239073053733833247)
                      ·
                        rfl

theorem cell23_6605743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 5, 3, 2, 2].length) (baseStart_6605743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605743 prefixEnd_6605743 := by exact prefixLift 6605743
  have htrace : WordTrace (prefixWord ++ tailWord_6605743) baseStart_6605743 baseEnd_6605743 := by
    simpa [prefixWord, tailWord_6605743, baseEnd_6605743] using wordTrace_append hprefix tailTrace_6605743
  have hstable : (prefixWord ++ tailWord_6605743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605743).length < 2 ^ (prefixWord ++ tailWord_6605743).sum := by decide
  have hdescent : baseEnd_6605743 < baseStart_6605743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605753 : List Nat := [1, 2, 1, 4, 2, 3, 1, 3, 2, 4]
def baseStart_6605753 : Nat := 118140960795 + 6605753 * 2 ^ 59
def prefixEnd_6605753 : Nat := 4983230072969 + 3 ^ 40 * 6605753 * 2
def baseEnd_6605753 : Nat := 1130642124626532898236067

theorem tailTrace_6605753 : CollatzResearch.WordTrace tailWord_6605753 prefixEnd_6605753 1130642124626532898236067 := by
  unfold tailWord_6605753
  simp only [CollatzResearch.WordTrace]
  refine ⟨240931605237492528639085913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160621070158328352426057275 240931605237492528639085913)
  ·
    refine ⟨180698703928119396479314435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240931605237492528639085913 180698703928119396479314435)
    ·
      refine ⟨271048055892179094718971653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180698703928119396479314435 271048055892179094718971653)
      ·
        refine ⟨50821510479783580259807185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271048055892179094718971653 50821510479783580259807185)
        ·
          refine ⟨38116132859837685194855389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50821510479783580259807185 38116132859837685194855389)
          ·
            refine ⟨14293549822439131948070771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38116132859837685194855389 14293549822439131948070771)
            ·
              refine ⟨21440324733658697922106157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14293549822439131948070771 21440324733658697922106157)
              ·
                refine ⟨8040121775122011720789809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21440324733658697922106157 8040121775122011720789809)
                ·
                  refine ⟨6030091331341508790592357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8040121775122011720789809 6030091331341508790592357)
                  ·
                    refine ⟨1130642124626532898236067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6030091331341508790592357 1130642124626532898236067)
                    ·
                      rfl

theorem cell23_6605753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 2, 4].length) (baseStart_6605753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605753 prefixEnd_6605753 := by exact prefixLift 6605753
  have htrace : WordTrace (prefixWord ++ tailWord_6605753) baseStart_6605753 baseEnd_6605753 := by
    simpa [prefixWord, tailWord_6605753, baseEnd_6605753] using wordTrace_append hprefix tailTrace_6605753
  have hstable : (prefixWord ++ tailWord_6605753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605753).length < 2 ^ (prefixWord ++ tailWord_6605753).sum := by decide
  have hdescent : baseEnd_6605753 < baseStart_6605753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605850 : List Nat := [3, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2]
def baseStart_6605850 : Nat := 118140960795 + 6605850 * 2 ^ 59
def prefixEnd_6605850 : Nat := 4983230072969 + 3 ^ 40 * 6605850 * 2
def baseEnd_6605850 : Nat := 3391976181503084815195255

theorem tailTrace_6605850 : CollatzResearch.WordTrace tailWord_6605850 prefixEnd_6605850 3391976181503084815195255 := by
  unfold tailWord_6605850
  simp only [CollatzResearch.WordTrace]
  refine ⟨60233785779535278551341751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160623428745427409470244669 60233785779535278551341751)
  ·
    refine ⟨90350678669302917827012627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60233785779535278551341751 90350678669302917827012627)
    ·
      refine ⟨135526018003954376740518941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90350678669302917827012627 135526018003954376740518941)
      ·
        refine ⟨50822256751482891277694603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135526018003954376740518941 50822256751482891277694603)
        ·
          refine ⟨76233385127224336916541905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50822256751482891277694603 76233385127224336916541905)
          ·
            refine ⟨57175038845418252687406429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76233385127224336916541905 57175038845418252687406429)
            ·
              refine ⟨21440639567031844757777411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57175038845418252687406429 21440639567031844757777411)
              ·
                refine ⟨32160959350547767136666117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21440639567031844757777411 32160959350547767136666117)
                ·
                  refine ⟨6030179878227706338124897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32160959350547767136666117 6030179878227706338124897)
                  ·
                    refine ⟨4522634908670779753593673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6030179878227706338124897 4522634908670779753593673)
                    ·
                      refine ⟨3391976181503084815195255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522634908670779753593673 3391976181503084815195255)
                      ·
                        rfl

theorem cell23_6605850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 1, 4, 2, 2].length) (baseStart_6605850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605850 prefixEnd_6605850 := by exact prefixLift 6605850
  have htrace : WordTrace (prefixWord ++ tailWord_6605850) baseStart_6605850 baseEnd_6605850 := by
    simpa [prefixWord, tailWord_6605850, baseEnd_6605850] using wordTrace_append hprefix tailTrace_6605850
  have hstable : (prefixWord ++ tailWord_6605850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605850).length < 2 ^ (prefixWord ++ tailWord_6605850).sum := by decide
  have hdescent : baseEnd_6605850 < baseStart_6605850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605867 : List Nat := [1, 1, 1, 1, 2, 1, 9, 1, 2, 2, 2]
def baseStart_6605867 : Nat := 118140960795 + 6605867 * 2 ^ 59
def prefixEnd_6605867 : Nat := 4983230072969 + 3 ^ 40 * 6605867 * 2
def baseEnd_6605867 : Nat := 3391984910674211248682677

theorem tailTrace_6605867 : CollatzResearch.WordTrace tailWord_6605867 prefixEnd_6605867 3391984910674211248682677 := by
  unfold tailWord_6605867
  simp only [CollatzResearch.WordTrace]
  refine ⟨240935763159079526108735855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160623842106053017405823903 240935763159079526108735855)
  ·
    refine ⟨361403644738619289163103783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240935763159079526108735855 361403644738619289163103783)
    ·
      refine ⟨542105467107928933744655675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361403644738619289163103783 542105467107928933744655675)
      ·
        refine ⟨813158200661893400616983513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542105467107928933744655675 813158200661893400616983513)
        ·
          refine ⟨609868650496420050462737635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 813158200661893400616983513 609868650496420050462737635)
          ·
            refine ⟨914802975744630075694106453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609868650496420050462737635 914802975744630075694106453)
            ·
              refine ⟨5360173686003691849770155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 914802975744630075694106453 5360173686003691849770155)
              ·
                refine ⟨8040260529005537774655233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5360173686003691849770155 8040260529005537774655233)
                ·
                  refine ⟨6030195396754153330991425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8040260529005537774655233 6030195396754153330991425)
                  ·
                    refine ⟨4522646547565614998243569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6030195396754153330991425 4522646547565614998243569)
                    ·
                      refine ⟨3391984910674211248682677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522646547565614998243569 3391984910674211248682677)
                      ·
                        rfl

theorem cell23_6605867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 9, 1, 2, 2, 2].length) (baseStart_6605867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605867 prefixEnd_6605867 := by exact prefixLift 6605867
  have htrace : WordTrace (prefixWord ++ tailWord_6605867) baseStart_6605867 baseEnd_6605867 := by
    simpa [prefixWord, tailWord_6605867, baseEnd_6605867] using wordTrace_append hprefix tailTrace_6605867
  have hstable : (prefixWord ++ tailWord_6605867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605867).length < 2 ^ (prefixWord ++ tailWord_6605867).sum := by decide
  have hdescent : baseEnd_6605867 < baseStart_6605867 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605896 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_6605896 : Nat := 118140960795 + 6605896 * 2 ^ 59
def prefixEnd_6605896 : Nat := 4983230072969 + 3 ^ 40 * 6605896 * 2
def baseEnd_6605896 : Nat := 3391999801613191635220043

theorem tailTrace_6605896 : CollatzResearch.WordTrace tailWord_6605896 prefixEnd_6605896 3391999801613191635220043 := by
  unfold tailWord_6605896
  simp only [CollatzResearch.WordTrace]
  refine ⟨120468410437987232030770771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160624547250649642707694361 120468410437987232030770771)
  ·
    refine ⟨180702615656980848046156157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120468410437987232030770771 180702615656980848046156157)
    ·
      refine ⟨67763480871367818017308559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180702615656980848046156157 67763480871367818017308559)
      ·
        refine ⟨101645221307051727025962839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67763480871367818017308559 101645221307051727025962839)
        ·
          refine ⟨152467831960577590538944259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101645221307051727025962839 152467831960577590538944259)
          ·
            refine ⟨228701747940866385808416389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152467831960577590538944259 228701747940866385808416389)
            ·
              refine ⟨42881577738912447339078073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228701747940866385808416389 42881577738912447339078073)
              ·
                refine ⟨32161183304184335504308555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42881577738912447339078073 32161183304184335504308555)
                ·
                  refine ⟨48241774956276503256462833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32161183304184335504308555 48241774956276503256462833)
                  ·
                    refine ⟨36181331217207377442347125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48241774956276503256462833 36181331217207377442347125)
                    ·
                      refine ⟨3391999801613191635220043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36181331217207377442347125 3391999801613191635220043)
                      ·
                        rfl

theorem cell23_6605896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_6605896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605896 prefixEnd_6605896 := by exact prefixLift 6605896
  have htrace : WordTrace (prefixWord ++ tailWord_6605896) baseStart_6605896 baseEnd_6605896 := by
    simpa [prefixWord, tailWord_6605896, baseEnd_6605896] using wordTrace_append hprefix tailTrace_6605896
  have hstable : (prefixWord ++ tailWord_6605896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605896).length < 2 ^ (prefixWord ++ tailWord_6605896).sum := by decide
  have hdescent : baseEnd_6605896 < baseStart_6605896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605918 : List Nat := [4, 4, 1, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_6605918 : Nat := 118140960795 + 6605918 * 2 ^ 59
def prefixEnd_6605918 : Nat := 4983230072969 + 3 ^ 40 * 6605918 * 2
def baseEnd_6605918 : Nat := 3392011098187590549144943

theorem tailTrace_6605918 : CollatzResearch.WordTrace tailWord_6605918 prefixEnd_6605918 3392011098187590549144943 := by
  unfold tailWord_6605918
  simp only [CollatzResearch.WordTrace]
  refine ⟨30117202910236845227355301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160625082187929841212561605 30117202910236845227355301)
  ·
    refine ⟨5646975545669408480129119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30117202910236845227355301 5646975545669408480129119)
    ·
      refine ⟨8470463318504112720193679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5646975545669408480129119 8470463318504112720193679)
      ·
        refine ⟨12705694977756169080290519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8470463318504112720193679 12705694977756169080290519)
        ·
          refine ⟨19058542466634253620435779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12705694977756169080290519 19058542466634253620435779)
          ·
            refine ⟨28587813699951380430653669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19058542466634253620435779 28587813699951380430653669)
            ·
              refine ⟨5360215068740883830747563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28587813699951380430653669 5360215068740883830747563)
              ·
                refine ⟨8040322603111325746121345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5360215068740883830747563 8040322603111325746121345)
                ·
                  refine ⟨6030241952333494309591009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8040322603111325746121345 6030241952333494309591009)
                  ·
                    refine ⟨4522681464250120732193257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6030241952333494309591009 4522681464250120732193257)
                    ·
                      refine ⟨3392011098187590549144943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522681464250120732193257 3392011098187590549144943)
                      ·
                        rfl

theorem cell23_6605918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_6605918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605918 prefixEnd_6605918 := by exact prefixLift 6605918
  have htrace : WordTrace (prefixWord ++ tailWord_6605918) baseStart_6605918 baseEnd_6605918 := by
    simpa [prefixWord, tailWord_6605918, baseEnd_6605918] using wordTrace_append hprefix tailTrace_6605918
  have hstable : (prefixWord ++ tailWord_6605918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605918).length < 2 ^ (prefixWord ++ tailWord_6605918).sum := by decide
  have hdescent : baseEnd_6605918 < baseStart_6605918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605923 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 1, 6, 2]
def baseStart_6605923 : Nat := 118140960795 + 6605923 * 2 ^ 59
def prefixEnd_6605923 : Nat := 4983230072969 + 3 ^ 40 * 6605923 * 2
def baseEnd_6605923 : Nat := 3392013665590863029582419

theorem tailTrace_6605923 : CollatzResearch.WordTrace tailWord_6605923 prefixEnd_6605923 3392013665590863029582419 := by
  unfold tailWord_6605923
  simp only [CollatzResearch.WordTrace]
  refine ⟨240937805646876647672774423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160625203764584431781849615 240937805646876647672774423)
  ·
    refine ⟨361406708470314971509161635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240937805646876647672774423 361406708470314971509161635)
    ·
      refine ⟨542110062705472457263742453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361406708470314971509161635 542110062705472457263742453)
      ·
        refine ⟨50822818378638042868475855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 542110062705472457263742453 50822818378638042868475855)
        ·
          refine ⟨76234227567957064302713783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50822818378638042868475855 76234227567957064302713783)
          ·
            refine ⟨114351341351935596454070675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76234227567957064302713783 114351341351935596454070675)
            ·
              refine ⟨171527012027903394681106013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114351341351935596454070675 171527012027903394681106013)
              ·
                refine ⟨64322629510463773005414755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171527012027903394681106013 64322629510463773005414755)
                ·
                  refine ⟨96483944265695659508122133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64322629510463773005414755 96483944265695659508122133)
                  ·
                    refine ⟨4522684887454484039443225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 96483944265695659508122133 4522684887454484039443225)
                    ·
                      refine ⟨3392013665590863029582419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522684887454484039443225 3392013665590863029582419)
                      ·
                        rfl

theorem cell23_6605923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_6605923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605923 prefixEnd_6605923 := by exact prefixLift 6605923
  have htrace : WordTrace (prefixWord ++ tailWord_6605923) baseStart_6605923 baseEnd_6605923 := by
    simpa [prefixWord, tailWord_6605923, baseEnd_6605923] using wordTrace_append hprefix tailTrace_6605923
  have hstable : (prefixWord ++ tailWord_6605923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605923).length < 2 ^ (prefixWord ++ tailWord_6605923).sum := by decide
  have hdescent : baseEnd_6605923 < baseStart_6605923 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6605994 : List Nat := [3, 1, 5, 1, 1, 3, 1, 1, 2, 2, 3]
def baseStart_6605994 : Nat := 118140960795 + 6605994 * 2 ^ 59
def prefixEnd_6605994 : Nat := 4983230072969 + 3 ^ 40 * 6605994 * 2
def baseEnd_6605994 : Nat := 3392050122717332251794593

theorem tailTrace_6605994 : CollatzResearch.WordTrace tailWord_6605994 prefixEnd_6605994 3392050122717332251794593 := by
  unfold tailWord_6605994
  simp only [CollatzResearch.WordTrace]
  refine ⟨60235098807404856699652259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160626930153079617865739357 60235098807404856699652259)
  ·
    refine ⟨90352648211107285049478389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60235098807404856699652259 90352648211107285049478389)
    ·
      refine ⟨8470560769791307973388599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90352648211107285049478389 8470560769791307973388599)
      ·
        refine ⟨12705841154686961960082899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8470560769791307973388599 12705841154686961960082899)
        ·
          refine ⟨19058761732030442940124349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12705841154686961960082899 19058761732030442940124349)
          ·
            refine ⟨7147035649511416102546631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19058761732030442940124349 7147035649511416102546631)
            ·
              refine ⟨10720553474267124153819947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7147035649511416102546631 10720553474267124153819947)
              ·
                refine ⟨16080830211400686230729921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10720553474267124153819947 16080830211400686230729921)
                ·
                  refine ⟨12060622658550514673047441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16080830211400686230729921 12060622658550514673047441)
                  ·
                    refine ⟨9045466993912886004785581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12060622658550514673047441 9045466993912886004785581)
                    ·
                      refine ⟨3392050122717332251794593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9045466993912886004785581 3392050122717332251794593)
                      ·
                        rfl

theorem cell23_6605994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_6605994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6605994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6605994 prefixEnd_6605994 := by exact prefixLift 6605994
  have htrace : WordTrace (prefixWord ++ tailWord_6605994) baseStart_6605994 baseEnd_6605994 := by
    simpa [prefixWord, tailWord_6605994, baseEnd_6605994] using wordTrace_append hprefix tailTrace_6605994
  have hstable : (prefixWord ++ tailWord_6605994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6605994).length < 2 ^ (prefixWord ++ tailWord_6605994).sum := by decide
  have hdescent : baseEnd_6605994 < baseStart_6605994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6605994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606047 : List Nat := [1, 1, 2, 3, 2, 1, 4, 2, 3, 2, 2]
def baseStart_6606047 : Nat := 118140960795 + 6606047 * 2 ^ 59
def prefixEnd_6606047 : Nat := 4983230072969 + 3 ^ 40 * 6606047 * 2
def baseEnd_6606047 : Nat := 3392077337192020544431849

theorem tailTrace_6606047 : CollatzResearch.WordTrace tailWord_6606047 prefixEnd_6606047 3392077337192020544431849 := by
  unfold tailWord_6606047
  simp only [CollatzResearch.WordTrace]
  refine ⟨240942328298427416850288395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160628218865618277900192263 240942328298427416850288395)
  ·
    refine ⟨361413492447641125275432593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240942328298427416850288395 361413492447641125275432593)
    ·
      refine ⟨271060119335730843956574445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361413492447641125275432593 271060119335730843956574445)
      ·
        refine ⟨101647544750899066483715417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271060119335730843956574445 101647544750899066483715417)
        ·
          refine ⟨76235658563174299862786563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101647544750899066483715417 76235658563174299862786563)
          ·
            refine ⟨114353487844761449794179845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76235658563174299862786563 114353487844761449794179845)
            ·
              refine ⟨21441278970892771836408721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114353487844761449794179845 21441278970892771836408721)
              ·
                refine ⟨16080959228169578877306541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21441278970892771836408721 16080959228169578877306541)
                ·
                  refine ⟨6030359710563592078989953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16080959228169578877306541 6030359710563592078989953)
                  ·
                    refine ⟨4522769782922694059242465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6030359710563592078989953 4522769782922694059242465)
                    ·
                      refine ⟨3392077337192020544431849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522769782922694059242465 3392077337192020544431849)
                      ·
                        rfl

theorem cell23_6606047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_6606047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606047 prefixEnd_6606047 := by exact prefixLift 6606047
  have htrace : WordTrace (prefixWord ++ tailWord_6606047) baseStart_6606047 baseEnd_6606047 := by
    simpa [prefixWord, tailWord_6606047, baseEnd_6606047] using wordTrace_append hprefix tailTrace_6606047
  have hstable : (prefixWord ++ tailWord_6606047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606047).length < 2 ^ (prefixWord ++ tailWord_6606047).sum := by decide
  have hdescent : baseEnd_6606047 < baseStart_6606047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606068 : List Nat := [2, 6, 1, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6606068 : Nat := 118140960795 + 6606068 * 2 ^ 59
def prefixEnd_6606068 : Nat := 4983230072969 + 3 ^ 40 * 6606068 * 2
def baseEnd_6606068 : Nat := 3392088120285764962269253

theorem tailTrace_6606068 : CollatzResearch.WordTrace tailWord_6606068 prefixEnd_6606068 3392088120285764962269253 := by
  unfold tailWord_6606068
  simp only [CollatzResearch.WordTrace]
  refine ⟨120471547115675668718401429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160628729487567558291201905 120471547115675668718401429)
  ·
    refine ⟨5647103771047296971175067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 120471547115675668718401429 5647103771047296971175067)
    ·
      refine ⟨8470655656570945456762601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5647103771047296971175067 8470655656570945456762601)
      ·
        refine ⟨6352991742428209092571951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8470655656570945456762601 6352991742428209092571951)
        ·
          refine ⟨9529487613642313638857927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6352991742428209092571951 9529487613642313638857927)
          ·
            refine ⟨14294231420463470458286891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9529487613642313638857927 14294231420463470458286891)
            ·
              refine ⟨21441347130695205687430337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14294231420463470458286891 21441347130695205687430337)
              ·
                refine ⟨16081010348021404265572753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21441347130695205687430337 16081010348021404265572753)
                ·
                  refine ⟨12060757761016053199179565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16081010348021404265572753 12060757761016053199179565)
                  ·
                    refine ⟨4522784160381019949692337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12060757761016053199179565 4522784160381019949692337)
                    ·
                      refine ⟨3392088120285764962269253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522784160381019949692337 3392088120285764962269253)
                      ·
                        rfl

theorem cell23_6606068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6606068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606068 prefixEnd_6606068 := by exact prefixLift 6606068
  have htrace : WordTrace (prefixWord ++ tailWord_6606068) baseStart_6606068 baseEnd_6606068 := by
    simpa [prefixWord, tailWord_6606068, baseEnd_6606068] using wordTrace_append hprefix tailTrace_6606068
  have hstable : (prefixWord ++ tailWord_6606068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606068).length < 2 ^ (prefixWord ++ tailWord_6606068).sum := by decide
  have hdescent : baseEnd_6606068 < baseStart_6606068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606090 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2]
def baseStart_6606090 : Nat := 118140960795 + 6606090 * 2 ^ 59
def prefixEnd_6606090 : Nat := 4983230072969 + 3 ^ 40 * 6606090 * 2
def baseEnd_6606090 : Nat := 3392099416860163876194151

theorem tailTrace_6606090 : CollatzResearch.WordTrace tailWord_6606090 prefixEnd_6606090 3392099416860163876194151 := by
  unfold tailWord_6606090
  simp only [CollatzResearch.WordTrace]
  refine ⟨60235974159317908798525931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160629264424847756796069149 60235974159317908798525931)
  ·
    refine ⟨90353961238976863197788897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60235974159317908798525931 90353961238976863197788897)
    ·
      refine ⟨67765470929232647398341673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90353961238976863197788897 67765470929232647398341673)
      ·
        refine ⟨50824103196924485548756255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67765470929232647398341673 50824103196924485548756255)
        ·
          refine ⟨76236154795386728323134383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50824103196924485548756255 76236154795386728323134383)
          ·
            refine ⟨114354232193080092484701575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76236154795386728323134383 114354232193080092484701575)
            ·
              refine ⟨171531348289620138727052363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114354232193080092484701575 171531348289620138727052363)
              ·
                refine ⟨257297022434430208090578545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171531348289620138727052363 257297022434430208090578545)
                ·
                  refine ⟨192972766825822656067933909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257297022434430208090578545 192972766825822656067933909)
                  ·
                    refine ⟨4522799222480218501592201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 192972766825822656067933909 4522799222480218501592201)
                    ·
                      refine ⟨3392099416860163876194151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522799222480218501592201 3392099416860163876194151)
                      ·
                        rfl

theorem cell23_6606090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_6606090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606090 prefixEnd_6606090 := by exact prefixLift 6606090
  have htrace : WordTrace (prefixWord ++ tailWord_6606090) baseStart_6606090 baseEnd_6606090 := by
    simpa [prefixWord, tailWord_6606090, baseEnd_6606090] using wordTrace_append hprefix tailTrace_6606090
  have hstable : (prefixWord ++ tailWord_6606090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606090).length < 2 ^ (prefixWord ++ tailWord_6606090).sum := by decide
  have hdescent : baseEnd_6606090 < baseStart_6606090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606097 : List Nat := [1, 2, 2, 1, 1, 4, 3, 3, 2, 1, 3]
def baseStart_6606097 : Nat := 118140960795 + 6606097 * 2 ^ 59
def prefixEnd_6606097 : Nat := 4983230072969 + 3 ^ 40 * 6606097 * 2
def baseEnd_6606097 : Nat := 3392103011224745348806619

theorem tailTrace_6606097 : CollatzResearch.WordTrace tailWord_6606097 prefixEnd_6606097 3392103011224745348806619 := by
  unfold tailWord_6606097
  simp only [CollatzResearch.WordTrace]
  refine ⟨240944151948246275389608545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160629434632164183593072363 240944151948246275389608545)
  ·
    refine ⟨180708113961184706542206409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240944151948246275389608545 180708113961184706542206409)
    ·
      refine ⟨135531085470888529906654807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180708113961184706542206409 135531085470888529906654807)
      ·
        refine ⟨203296628206332794859982211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135531085470888529906654807 203296628206332794859982211)
        ·
          refine ⟨304944942309499192289973317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203296628206332794859982211 304944942309499192289973317)
          ·
            refine ⟨57177176683031098554369997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304944942309499192289973317 57177176683031098554369997)
            ·
              refine ⟨21441441256136661957888749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57177176683031098554369997 21441441256136661957888749)
              ·
                refine ⟨8040540471051248234208281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21441441256136661957888749 8040540471051248234208281)
                ·
                  refine ⟨6030405353288436175656211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8040540471051248234208281 6030405353288436175656211)
                  ·
                    refine ⟨9045608029932654263484317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6030405353288436175656211 9045608029932654263484317)
                    ·
                      refine ⟨3392103011224745348806619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9045608029932654263484317 3392103011224745348806619)
                      ·
                        rfl

theorem cell23_6606097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2, 1, 3].length) (baseStart_6606097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606097 prefixEnd_6606097 := by exact prefixLift 6606097
  have htrace : WordTrace (prefixWord ++ tailWord_6606097) baseStart_6606097 baseEnd_6606097 := by
    simpa [prefixWord, tailWord_6606097, baseEnd_6606097] using wordTrace_append hprefix tailTrace_6606097
  have hstable : (prefixWord ++ tailWord_6606097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606097).length < 2 ^ (prefixWord ++ tailWord_6606097).sum := by decide
  have hdescent : baseEnd_6606097 < baseStart_6606097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606098 : List Nat := [3, 2, 4, 2, 2, 1, 1, 2, 1, 1, 4]
def baseStart_6606098 : Nat := 118140960795 + 6606098 * 2 ^ 59
def prefixEnd_6606098 : Nat := 4983230072969 + 3 ^ 40 * 6606098 * 2
def baseEnd_6606098 : Nat := 3392103524705399844894115

theorem tailTrace_6606098 : CollatzResearch.WordTrace tailWord_6606098 prefixEnd_6606098 3392103524705399844894115 := by
  unfold tailWord_6606098
  simp only [CollatzResearch.WordTrace]
  refine ⟨60236047105310663140098737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160629458947495101706929965 60236047105310663140098737)
  ·
    refine ⟨45177035328982997355074053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60236047105310663140098737 45177035328982997355074053)
    ·
      refine ⟨8470694124184312004076385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45177035328982997355074053 8470694124184312004076385)
      ·
        refine ⟨6353020593138234003057289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8470694124184312004076385 6353020593138234003057289)
        ·
          refine ⟨4764765444853675502292967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6353020593138234003057289 4764765444853675502292967)
          ·
            refine ⟨7147148167280513253439451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4764765444853675502292967 7147148167280513253439451)
            ·
              refine ⟨10720722250920769880159177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7147148167280513253439451 10720722250920769880159177)
              ·
                refine ⟨8040541688190577410119383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10720722250920769880159177 8040541688190577410119383)
                ·
                  refine ⟨12060812532285866115179075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8040541688190577410119383 12060812532285866115179075)
                  ·
                    refine ⟨18091218798428799172768613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12060812532285866115179075 18091218798428799172768613)
                    ·
                      refine ⟨3392103524705399844894115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18091218798428799172768613 3392103524705399844894115)
                      ·
                        rfl

theorem cell23_6606098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_6606098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606098 prefixEnd_6606098 := by exact prefixLift 6606098
  have htrace : WordTrace (prefixWord ++ tailWord_6606098) baseStart_6606098 baseEnd_6606098 := by
    simpa [prefixWord, tailWord_6606098, baseEnd_6606098] using wordTrace_append hprefix tailTrace_6606098
  have hstable : (prefixWord ++ tailWord_6606098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606098).length < 2 ^ (prefixWord ++ tailWord_6606098).sum := by decide
  have hdescent : baseEnd_6606098 < baseStart_6606098 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606113 : List Nat := [1, 2, 3, 2, 1, 1, 1, 2, 4, 6]
def baseStart_6606113 : Nat := 118140960795 + 6606113 * 2 ^ 59
def prefixEnd_6606113 : Nat := 4983230072969 + 3 ^ 40 * 6606113 * 2
def baseEnd_6606113 : Nat := 1130703742305072428735515

theorem tailTrace_6606113 : CollatzResearch.WordTrace tailWord_6606113 prefixEnd_6606113 1130703742305072428735515 := by
  unfold tailWord_6606113
  simp only [CollatzResearch.WordTrace]
  refine ⟨240944735516188310122190993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160629823677458873414793995 240944735516188310122190993)
  ·
    refine ⟨180708551637141232591643245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240944735516188310122190993 180708551637141232591643245)
    ·
      refine ⟨67765706863927962221866217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180708551637141232591643245 67765706863927962221866217)
      ·
        refine ⟨50824280147945971666399663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67765706863927962221866217 50824280147945971666399663)
        ·
          refine ⟨76236420221918957499599495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50824280147945971666399663 76236420221918957499599495)
          ·
            refine ⟨114354630332878436249399243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76236420221918957499599495 114354630332878436249399243)
            ·
              refine ⟨171531945499317654374098865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114354630332878436249399243 171531945499317654374098865)
              ·
                refine ⟨128648959124488240780574149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171531945499317654374098865 128648959124488240780574149)
                ·
                  refine ⟨24121679835841545146357653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128648959124488240780574149 24121679835841545146357653)
                  ·
                    refine ⟨1130703742305072428735515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24121679835841545146357653 1130703742305072428735515)
                    ·
                      rfl

theorem cell23_6606113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_6606113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606113 prefixEnd_6606113 := by exact prefixLift 6606113
  have htrace : WordTrace (prefixWord ++ tailWord_6606113) baseStart_6606113 baseEnd_6606113 := by
    simpa [prefixWord, tailWord_6606113, baseEnd_6606113] using wordTrace_append hprefix tailTrace_6606113
  have hstable : (prefixWord ++ tailWord_6606113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606113).length < 2 ^ (prefixWord ++ tailWord_6606113).sum := by decide
  have hdescent : baseEnd_6606113 < baseStart_6606113 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606140 : List Nat := [2, 2, 2, 2, 1, 3, 1, 1, 2, 4, 3]
def baseStart_6606140 : Nat := 118140960795 + 6606140 * 2 ^ 59
def prefixEnd_6606140 : Nat := 4983230072969 + 3 ^ 40 * 6606140 * 2
def baseEnd_6606140 : Nat := 3392125090892888680568921

theorem tailTrace_6606140 : CollatzResearch.WordTrace tailWord_6606140 prefixEnd_6606140 3392125090892888680568921 := by
  unfold tailWord_6606140
  simp only [CollatzResearch.WordTrace]
  refine ⟨120472860143545246866711937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160630480191393662488949249 120472860143545246866711937)
  ·
    refine ⟨90354645107658935150033953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120472860143545246866711937 90354645107658935150033953)
    ·
      refine ⟨67765983830744201362525465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90354645107658935150033953 67765983830744201362525465)
      ·
        refine ⟨50824487873058151021894099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67765983830744201362525465 50824487873058151021894099)
        ·
          refine ⟨76236731809587226532841149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50824487873058151021894099 76236731809587226532841149)
          ·
            refine ⟨28588774428595209949815431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76236731809587226532841149 28588774428595209949815431)
            ·
              refine ⟨42883161642892814924723147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28588774428595209949815431 42883161642892814924723147)
              ·
                refine ⟨64324742464339222387084721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42883161642892814924723147 64324742464339222387084721)
                ·
                  refine ⟨48243556848254416790313541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64324742464339222387084721 48243556848254416790313541)
                  ·
                    refine ⟨9045666909047703148183789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48243556848254416790313541 9045666909047703148183789)
                    ·
                      refine ⟨3392125090892888680568921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9045666909047703148183789 3392125090892888680568921)
                      ·
                        rfl

theorem cell23_6606140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_6606140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606140 prefixEnd_6606140 := by exact prefixLift 6606140
  have htrace : WordTrace (prefixWord ++ tailWord_6606140) baseStart_6606140 baseEnd_6606140 := by
    simpa [prefixWord, tailWord_6606140, baseEnd_6606140] using wordTrace_append hprefix tailTrace_6606140
  have hstable : (prefixWord ++ tailWord_6606140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606140).length < 2 ^ (prefixWord ++ tailWord_6606140).sum := by decide
  have hdescent : baseEnd_6606140 < baseStart_6606140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606287 : List Nat := [1, 1, 2, 1, 1, 4, 2, 3, 1, 5, 2]
def baseStart_6606287 : Nat := 118140960795 + 6606287 * 2 ^ 59
def prefixEnd_6606287 : Nat := 4983230072969 + 3 ^ 40 * 6606287 * 2
def baseEnd_6606287 : Nat := 3392200572549099605430745

theorem tailTrace_6606287 : CollatzResearch.WordTrace tailWord_6606287 prefixEnd_6606287 3392200572549099605430745 := by
  unfold tailWord_6606287
  simp only [CollatzResearch.WordTrace]
  refine ⟨240951081817557937839025115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160634054545038625226016743 240951081817557937839025115)
  ·
    refine ⟨361426622726336906758537673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240951081817557937839025115 361426622726336906758537673)
    ·
      refine ⟨271069967044752680068903255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361426622726336906758537673 271069967044752680068903255)
      ·
        refine ⟨406604950567129020103354883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271069967044752680068903255 406604950567129020103354883)
        ·
          refine ⟨609907425850693530155032325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406604950567129020103354883 609907425850693530155032325)
          ·
            refine ⟨114357642347005036904068561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 609907425850693530155032325 114357642347005036904068561)
            ·
              refine ⟨85768231760253777678051421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114357642347005036904068561 85768231760253777678051421)
              ·
                refine ⟨32163086910095166629269283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85768231760253777678051421 32163086910095166629269283)
                ·
                  refine ⟨48244630365142749943903925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32163086910095166629269283 48244630365142749943903925)
                  ·
                    refine ⟨4522934096732132807240993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48244630365142749943903925 4522934096732132807240993)
                    ·
                      refine ⟨3392200572549099605430745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522934096732132807240993 3392200572549099605430745)
                      ·
                        rfl

theorem cell23_6606287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 5, 2].length) (baseStart_6606287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606287 prefixEnd_6606287 := by exact prefixLift 6606287
  have htrace : WordTrace (prefixWord ++ tailWord_6606287) baseStart_6606287 baseEnd_6606287 := by
    simpa [prefixWord, tailWord_6606287, baseEnd_6606287] using wordTrace_append hprefix tailTrace_6606287
  have hstable : (prefixWord ++ tailWord_6606287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606287).length < 2 ^ (prefixWord ++ tailWord_6606287).sum := by decide
  have hdescent : baseEnd_6606287 < baseStart_6606287 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606338 : List Nat := [3, 4, 1, 2, 1, 1, 3, 1, 2, 3, 2]
def baseStart_6606338 : Nat := 118140960795 + 6606338 * 2 ^ 59
def prefixEnd_6606338 : Nat := 4983230072969 + 3 ^ 40 * 6606338 * 2
def baseEnd_6606338 : Nat := 3392226760062478905893011

theorem tailTrace_6606338 : CollatzResearch.WordTrace tailWord_6606338 prefixEnd_6606338 3392226760062478905893011 := by
  unfold tailWord_6606338
  simp only [CollatzResearch.WordTrace]
  refine ⟨60238235485093293387282917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160635294626915449032754445 60238235485093293387282917)
  ·
    refine ⟨11294669153454992510115547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60238235485093293387282917 11294669153454992510115547)
    ·
      refine ⟨16942003730182488765173321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11294669153454992510115547 16942003730182488765173321)
      ·
        refine ⟨12706502797636866573879991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16942003730182488765173321 12706502797636866573879991)
        ·
          refine ⟨19059754196455299860819987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12706502797636866573879991 19059754196455299860819987)
          ·
            refine ⟨28589631294682949791229981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19059754196455299860819987 28589631294682949791229981)
            ·
              refine ⟨10721111735506106171711243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28589631294682949791229981 10721111735506106171711243)
              ·
                refine ⟨16081667603259159257566865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10721111735506106171711243 16081667603259159257566865)
                ·
                  refine ⟨12061250702444369443175149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16081667603259159257566865 12061250702444369443175149)
                  ·
                    refine ⟨4522969013416638541190681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12061250702444369443175149 4522969013416638541190681)
                    ·
                      refine ⟨3392226760062478905893011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522969013416638541190681 3392226760062478905893011)
                      ·
                        rfl

theorem cell23_6606338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_6606338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606338 prefixEnd_6606338 := by exact prefixLift 6606338
  have htrace : WordTrace (prefixWord ++ tailWord_6606338) baseStart_6606338 baseEnd_6606338 := by
    simpa [prefixWord, tailWord_6606338, baseEnd_6606338] using wordTrace_append hprefix tailTrace_6606338
  have hstable : (prefixWord ++ tailWord_6606338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606338).length < 2 ^ (prefixWord ++ tailWord_6606338).sum := by decide
  have hdescent : baseEnd_6606338 < baseStart_6606338 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606348 : List Nat := [2, 2, 1, 2, 6, 1, 2, 1, 1, 5]
def baseStart_6606348 : Nat := 118140960795 + 6606348 * 2 ^ 59
def prefixEnd_6606348 : Nat := 4983230072969 + 3 ^ 40 * 6606348 * 2
def baseEnd_6606348 : Nat := 1130743964956341288922655

theorem tailTrace_6606348 : CollatzResearch.WordTrace tailWord_6606348 prefixEnd_6606348 1130743964956341288922655 := by
  unfold tailWord_6606348
  simp only [CollatzResearch.WordTrace]
  refine ⟨120476653335168472628497849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160635537780224630171330465 120476653335168472628497849)
  ·
    refine ⟨90357490001376354471373387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120476653335168472628497849 90357490001376354471373387)
    ·
      refine ⟨135536235002064531707060081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90357490001376354471373387 135536235002064531707060081)
      ·
        refine ⟨101652176251548398780295061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135536235002064531707060081 101652176251548398780295061)
        ·
          refine ⟨4764945761791331192826331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 101652176251548398780295061 4764945761791331192826331)
          ·
            refine ⟨7147418642686996789239497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4764945761791331192826331 7147418642686996789239497)
            ·
              refine ⟨5360563982015247591929623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7147418642686996789239497 5360563982015247591929623)
              ·
                refine ⟨8040845973022871387894435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5360563982015247591929623 8040845973022871387894435)
                ·
                  refine ⟨12061268959534307081841653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8040845973022871387894435 12061268959534307081841653)
                  ·
                    refine ⟨1130743964956341288922655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12061268959534307081841653 1130743964956341288922655)
                    ·
                      rfl

theorem cell23_6606348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 2, 1, 1, 5].length) (baseStart_6606348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606348 prefixEnd_6606348 := by exact prefixLift 6606348
  have htrace : WordTrace (prefixWord ++ tailWord_6606348) baseStart_6606348 baseEnd_6606348 := by
    simpa [prefixWord, tailWord_6606348, baseEnd_6606348] using wordTrace_append hprefix tailTrace_6606348
  have hstable : (prefixWord ++ tailWord_6606348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606348).length < 2 ^ (prefixWord ++ tailWord_6606348).sum := by decide
  have hdescent : baseEnd_6606348 < baseStart_6606348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606367 : List Nat := [1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 3]
def baseStart_6606367 : Nat := 118140960795 + 6606367 * 2 ^ 59
def prefixEnd_6606367 : Nat := 4983230072969 + 3 ^ 40 * 6606367 * 2
def baseEnd_6606367 : Nat := 3392241651001459292430377

theorem tailTrace_6606367 : CollatzResearch.WordTrace tailWord_6606367 prefixEnd_6606367 3392241651001459292430377 := by
  unfold tailWord_6606367
  simp only [CollatzResearch.WordTrace]
  refine ⟨240953999657268111501937355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160635999771512074334624903 240953999657268111501937355)
  ·
    refine ⟨361430999485902167252906033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240953999657268111501937355 361430999485902167252906033)
    ·
      refine ⟨271073249614426625439679525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361430999485902167252906033 271073249614426625439679525)
      ·
        refine ⟨50826234302704992269939911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271073249614426625439679525 50826234302704992269939911)
        ·
          refine ⟨76239351454057488404909867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50826234302704992269939911 76239351454057488404909867)
          ·
            refine ⟨114359027181086232607364801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76239351454057488404909867 114359027181086232607364801)
            ·
              refine ⟨85769270385814674455523601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114359027181086232607364801 85769270385814674455523601)
              ·
                refine ⟨64326952789361005841642701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85769270385814674455523601 64326952789361005841642701)
                ·
                  refine ⟨24122607296010377190616013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64326952789361005841642701 24122607296010377190616013)
                  ·
                    refine ⟨9045977736003891446481005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24122607296010377190616013 9045977736003891446481005)
                    ·
                      refine ⟨3392241651001459292430377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9045977736003891446481005 3392241651001459292430377)
                      ·
                        rfl

theorem cell23_6606367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_6606367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606367 prefixEnd_6606367 := by exact prefixLift 6606367
  have htrace : WordTrace (prefixWord ++ tailWord_6606367) baseStart_6606367 baseEnd_6606367 := by
    simpa [prefixWord, tailWord_6606367, baseEnd_6606367] using wordTrace_append hprefix tailTrace_6606367
  have hstable : (prefixWord ++ tailWord_6606367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606367).length < 2 ^ (prefixWord ++ tailWord_6606367).sum := by decide
  have hdescent : baseEnd_6606367 < baseStart_6606367 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606368 : List Nat := [2, 1, 1, 6, 1, 2, 2, 1, 3, 2, 2]
def baseStart_6606368 : Nat := 118140960795 + 6606368 * 2 ^ 59
def prefixEnd_6606368 : Nat := 4983230072969 + 3 ^ 40 * 6606368 * 2
def baseEnd_6606368 : Nat := 3392242164482113788517873

theorem tailTrace_6606368 : CollatzResearch.WordTrace tailWord_6606368 prefixEnd_6606368 3392242164482113788517873 := by
  unfold tailWord_6606368
  simp only [CollatzResearch.WordTrace]
  refine ⟨120477018065132244336361879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160636024086842992448482505 120477018065132244336361879)
  ·
    refine ⟨180715527097698366504542819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120477018065132244336361879 180715527097698366504542819)
    ·
      refine ⟨271073290646547549756814229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180715527097698366504542819 271073290646547549756814229)
      ·
        refine ⟨12706560499056916394850667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 271073290646547549756814229 12706560499056916394850667)
        ·
          refine ⟨19059840748585374592276001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12706560499056916394850667 19059840748585374592276001)
          ·
            refine ⟨14294880561439030944207001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19059840748585374592276001 14294880561439030944207001)
            ·
              refine ⟨10721160421079273208155251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14294880561439030944207001 10721160421079273208155251)
              ·
                refine ⟨16081740631618909812232877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10721160421079273208155251 16081740631618909812232877)
                ·
                  refine ⟨6030652736857091179587329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16081740631618909812232877 6030652736857091179587329)
                  ·
                    refine ⟨4522989552642818384690497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6030652736857091179587329 4522989552642818384690497)
                    ·
                      refine ⟨3392242164482113788517873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4522989552642818384690497 3392242164482113788517873)
                      ·
                        rfl

theorem cell23_6606368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_6606368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606368 prefixEnd_6606368 := by exact prefixLift 6606368
  have htrace : WordTrace (prefixWord ++ tailWord_6606368) baseStart_6606368 baseEnd_6606368 := by
    simpa [prefixWord, tailWord_6606368, baseEnd_6606368] using wordTrace_append hprefix tailTrace_6606368
  have hstable : (prefixWord ++ tailWord_6606368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606368).length < 2 ^ (prefixWord ++ tailWord_6606368).sum := by decide
  have hdescent : baseEnd_6606368 < baseStart_6606368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606445 : List Nat := [1, 5, 1, 1, 4, 2, 1, 2, 1, 3, 2]
def baseStart_6606445 : Nat := 118140960795 + 6606445 * 2 ^ 59
def prefixEnd_6606445 : Nat := 4983230072969 + 3 ^ 40 * 6606445 * 2
def baseEnd_6606445 : Nat := 3392281702492509987255019

theorem tailTrace_6606445 : CollatzResearch.WordTrace tailWord_6606445 prefixEnd_6606445 3392281702492509987255019 := by
  unfold tailWord_6606445
  simp only [CollatzResearch.WordTrace]
  refine ⟨240956844550985530823276789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160637896367323687215517859 240956844550985530823276789)
  ·
    refine ⟨22589704176654893514682199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 240956844550985530823276789 22589704176654893514682199)
    ·
      refine ⟨33884556264982340272023299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22589704176654893514682199 33884556264982340272023299)
      ·
        refine ⟨50826834397473510408034949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33884556264982340272023299 50826834397473510408034949)
        ·
          refine ⟨9530031449526283201506553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50826834397473510408034949 9530031449526283201506553)
          ·
            refine ⟨7147523587144712401129915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9530031449526283201506553 7147523587144712401129915)
            ·
              refine ⟨10721285380717068601694873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7147523587144712401129915 10721285380717068601694873)
              ·
                refine ⟨8040964035537801451271155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10721285380717068601694873 8040964035537801451271155)
                ·
                  refine ⟨12061446053306702176906733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8040964035537801451271155 12061446053306702176906733)
                  ·
                    refine ⟨4523042269990013316340025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12061446053306702176906733 4523042269990013316340025)
                    ·
                      refine ⟨3392281702492509987255019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4523042269990013316340025 3392281702492509987255019)
                      ·
                        rfl

theorem cell23_6606445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 3, 2].length) (baseStart_6606445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606445 prefixEnd_6606445 := by exact prefixLift 6606445
  have htrace : WordTrace (prefixWord ++ tailWord_6606445) baseStart_6606445 baseEnd_6606445 := by
    simpa [prefixWord, tailWord_6606445, baseEnd_6606445] using wordTrace_append hprefix tailTrace_6606445
  have hstable : (prefixWord ++ tailWord_6606445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606445).length < 2 ^ (prefixWord ++ tailWord_6606445).sum := by decide
  have hdescent : baseEnd_6606445 < baseStart_6606445 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606464 : List Nat := [2, 1, 1, 2, 1, 4, 2, 5, 5]
def baseStart_6606464 : Nat := 118140960795 + 6606464 * 2 ^ 59
def prefixEnd_6606464 : Nat := 4983230072969 + 3 ^ 40 * 6606464 * 2
def baseEnd_6606464 : Nat := 376921273180549490324159

theorem tailTrace_6606464 : CollatzResearch.WordTrace tailWord_6606464 prefixEnd_6606464 376921273180549490324159 := by
  unfold tailWord_6606464
  simp only [CollatzResearch.WordTrace]
  refine ⟨120478768768958348534109223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160638358358611131378812297 120478768768958348534109223)
  ·
    refine ⟨180718153153437522801163835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120478768768958348534109223 180718153153437522801163835)
    ·
      refine ⟨271077229730156284201745753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180718153153437522801163835 271077229730156284201745753)
      ·
        refine ⟨203307922297617213151309315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271077229730156284201745753 203307922297617213151309315)
        ·
          refine ⟨304961883446425819726963973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203307922297617213151309315 304961883446425819726963973)
          ·
            refine ⟨57180353146204841198805745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 304961883446425819726963973 57180353146204841198805745)
            ·
              refine ⟨42885264859653630899104309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57180353146204841198805745 42885264859653630899104309)
              ·
                refine ⟨4020493580592527896791029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42885264859653630899104309 4020493580592527896791029)
                ·
                  refine ⟨376921273180549490324159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4020493580592527896791029 376921273180549490324159)
                  ·
                    rfl

theorem cell23_6606464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 5, 5].length) (baseStart_6606464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606464 prefixEnd_6606464 := by exact prefixLift 6606464
  have htrace : WordTrace (prefixWord ++ tailWord_6606464) baseStart_6606464 baseEnd_6606464 := by
    simpa [prefixWord, tailWord_6606464, baseEnd_6606464] using wordTrace_append hprefix tailTrace_6606464
  have hstable : (prefixWord ++ tailWord_6606464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606464).length < 2 ^ (prefixWord ++ tailWord_6606464).sum := by decide
  have hdescent : baseEnd_6606464 < baseStart_6606464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606527 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 6]
def baseStart_6606527 : Nat := 118140960795 + 6606527 * 2 ^ 59
def prefixEnd_6606527 : Nat := 4983230072969 + 3 ^ 40 * 6606527 * 2
def baseEnd_6606527 : Nat := 3392323807906178666429641

theorem tailTrace_6606527 : CollatzResearch.WordTrace tailWord_6606527 prefixEnd_6606527 3392323807906178666429641 := by
  unfold tailWord_6606527
  simp only [CollatzResearch.WordTrace]
  refine ⟨240959835336688458827761835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160639890224458972551841223 240959835336688458827761835)
  ·
    refine ⟨361439753005032688241642753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240959835336688458827761835 361439753005032688241642753)
    ·
      refine ⟨271079814753774516181232065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361439753005032688241642753 271079814753774516181232065)
      ·
        refine ⟨203309861065330887135924049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271079814753774516181232065 203309861065330887135924049)
        ·
          refine ⟨152482395798998165351943037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203309861065330887135924049 152482395798998165351943037)
          ·
            refine ⟨57180898424624312006978639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152482395798998165351943037 57180898424624312006978639)
            ·
              refine ⟨85771347636936468010467959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57180898424624312006978639 85771347636936468010467959)
              ·
                refine ⟨128657021455404702015701939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85771347636936468010467959 128657021455404702015701939)
                ·
                  refine ⟨192985532183107053023552909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128657021455404702015701939 192985532183107053023552909)
                  ·
                    refine ⟨72369574568665144883832341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 192985532183107053023552909 72369574568665144883832341)
                    ·
                      refine ⟨3392323807906178666429641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72369574568665144883832341 3392323807906178666429641)
                      ·
                        rfl

theorem cell23_6606527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_6606527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606527 prefixEnd_6606527 := by exact prefixLift 6606527
  have htrace : WordTrace (prefixWord ++ tailWord_6606527) baseStart_6606527 baseEnd_6606527 := by
    simpa [prefixWord, tailWord_6606527, baseEnd_6606527] using wordTrace_append hprefix tailTrace_6606527
  have hstable : (prefixWord ++ tailWord_6606527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606527).length < 2 ^ (prefixWord ++ tailWord_6606527).sum := by decide
  have hdescent : baseEnd_6606527 < baseStart_6606527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606548 : List Nat := [2, 4, 1, 3, 1, 1, 2, 1, 2, 4, 2]
def baseStart_6606548 : Nat := 118140960795 + 6606548 * 2 ^ 59
def prefixEnd_6606548 : Nat := 4983230072969 + 3 ^ 40 * 6606548 * 2
def baseEnd_6606548 : Nat := 3392334590999923084267045

theorem tailTrace_6606548 : CollatzResearch.WordTrace tailWord_6606548 prefixEnd_6606548 3392334590999923084267045 := by
  unfold tailWord_6606548
  simp only [CollatzResearch.WordTrace]
  refine ⟨120480300634806189707138149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160640400846408252942850865 120480300634806189707138149)
  ·
    refine ⟨22590056369026160570088403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120480300634806189707138149 22590056369026160570088403)
    ·
      refine ⟨33885084553539240855132605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22590056369026160570088403 33885084553539240855132605)
      ·
        refine ⟨12706906707577215320674727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33885084553539240855132605 12706906707577215320674727)
        ·
          refine ⟨19060360061365822981012091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12706906707577215320674727 19060360061365822981012091)
          ·
            refine ⟨28590540092048734471518137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19060360061365822981012091 28590540092048734471518137)
            ·
              refine ⟨21442905069036550853638603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28590540092048734471518137 21442905069036550853638603)
              ·
                refine ⟨32164357603554826280457905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21442905069036550853638603 32164357603554826280457905)
                ·
                  refine ⟨24123268202666119710343429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32164357603554826280457905 24123268202666119710343429)
                  ·
                    refine ⟨4523112787999897445689393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24123268202666119710343429 4523112787999897445689393)
                    ·
                      refine ⟨3392334590999923084267045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4523112787999897445689393 3392334590999923084267045)
                      ·
                        rfl

theorem cell23_6606548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_6606548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606548 prefixEnd_6606548 := by exact prefixLift 6606548
  have htrace : WordTrace (prefixWord ++ tailWord_6606548) baseStart_6606548 baseEnd_6606548 := by
    simpa [prefixWord, tailWord_6606548, baseEnd_6606548] using wordTrace_append hprefix tailTrace_6606548
  have hstable : (prefixWord ++ tailWord_6606548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606548).length < 2 ^ (prefixWord ++ tailWord_6606548).sum := by decide
  have hdescent : baseEnd_6606548 < baseStart_6606548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606564 : List Nat := [2, 3, 1, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_6606564 : Nat := 118140960795 + 6606564 * 2 ^ 59
def prefixEnd_6606564 : Nat := 4983230072969 + 3 ^ 40 * 6606564 * 2
def baseEnd_6606564 : Nat := 3392342806690395021666971

theorem tailTrace_6606564 : CollatzResearch.WordTrace tailWord_6606564 prefixEnd_6606564 3392342806690395021666971 := by
  unfold tailWord_6606564
  simp only [CollatzResearch.WordTrace]
  refine ⟨120480592418777207073429373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160640789891702942764572497 120480592418777207073429373)
  ·
    refine ⟨45180222157041452652536015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120480592418777207073429373 45180222157041452652536015)
    ·
      refine ⟨67770333235562178978804023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45180222157041452652536015 67770333235562178978804023)
      ·
        refine ⟨101655499853343268468206035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67770333235562178978804023 101655499853343268468206035)
        ·
          refine ⟨152483249780014902702309053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101655499853343268468206035 152483249780014902702309053)
          ·
            refine ⟨57181218667505588513365895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 152483249780014902702309053 57181218667505588513365895)
            ·
              refine ⟨85771828001258382770048843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57181218667505588513365895 85771828001258382770048843)
              ·
                refine ⟨128657742001887574155073265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85771828001258382770048843 128657742001887574155073265)
                ·
                  refine ⟨96493306501415680616304949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 128657742001887574155073265 96493306501415680616304949)
                  ·
                    refine ⟨9046247484507720057778589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 96493306501415680616304949 9046247484507720057778589)
                    ·
                      refine ⟨3392342806690395021666971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9046247484507720057778589 3392342806690395021666971)
                      ·
                        rfl

theorem cell23_6606564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_6606564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606564 prefixEnd_6606564 := by exact prefixLift 6606564
  have htrace : WordTrace (prefixWord ++ tailWord_6606564) baseStart_6606564 baseEnd_6606564 := by
    simpa [prefixWord, tailWord_6606564, baseEnd_6606564] using wordTrace_append hprefix tailTrace_6606564
  have hstable : (prefixWord ++ tailWord_6606564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606564).length < 2 ^ (prefixWord ++ tailWord_6606564).sum := by decide
  have hdescent : baseEnd_6606564 < baseStart_6606564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606591 : List Nat := [1, 1, 2, 2, 1, 3, 3, 1, 4, 3, 2]
def baseStart_6606591 : Nat := 118140960795 + 6606591 * 2 ^ 59
def prefixEnd_6606591 : Nat := 4983230072969 + 3 ^ 40 * 6606591 * 2
def baseEnd_6606591 : Nat := 3392356670668066416029347

theorem tailTrace_6606591 : CollatzResearch.WordTrace tailWord_6606591 prefixEnd_6606591 3392356670668066416029347 := by
  unfold tailWord_6606591
  simp only [CollatzResearch.WordTrace]
  refine ⟨240962169608456597758091627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160641446405637731838727751 240962169608456597758091627)
  ·
    refine ⟨361443254412684896637137441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240962169608456597758091627 361443254412684896637137441)
    ·
      refine ⟨271082440809513672477853081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361443254412684896637137441 271082440809513672477853081)
      ·
        refine ⟨203311830607135254358389811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271082440809513672477853081 203311830607135254358389811)
        ·
          refine ⟨304967745910702881537584717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203311830607135254358389811 304967745910702881537584717)
          ·
            refine ⟨114362904716513580576594269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 304967745910702881537584717 114362904716513580576594269)
            ·
              refine ⟨42886089268692592716222851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114362904716513580576594269 42886089268692592716222851)
              ·
                refine ⟨64329133903038889074334277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42886089268692592716222851 64329133903038889074334277)
                ·
                  refine ⟨12061712606819791701437677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64329133903038889074334277 12061712606819791701437677)
                  ·
                    refine ⟨4523142227557421888039129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12061712606819791701437677 4523142227557421888039129)
                    ·
                      refine ⟨3392356670668066416029347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4523142227557421888039129 3392356670668066416029347)
                      ·
                        rfl

theorem cell23_6606591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 3, 2].length) (baseStart_6606591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606591 prefixEnd_6606591 := by exact prefixLift 6606591
  have htrace : WordTrace (prefixWord ++ tailWord_6606591) baseStart_6606591 baseEnd_6606591 := by
    simpa [prefixWord, tailWord_6606591, baseEnd_6606591] using wordTrace_append hprefix tailTrace_6606591
  have hstable : (prefixWord ++ tailWord_6606591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606591).length < 2 ^ (prefixWord ++ tailWord_6606591).sum := by decide
  have hdescent : baseEnd_6606591 < baseStart_6606591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606618 : List Nat := [3, 1, 1, 3, 2, 4, 1, 2, 1, 5]
def baseStart_6606618 : Nat := 118140960795 + 6606618 * 2 ^ 59
def prefixEnd_6606618 : Nat := 4983230072969 + 3 ^ 40 * 6606618 * 2
def baseEnd_6606618 : Nat := 1130790178215245936797241

theorem tailTrace_6606618 : CollatzResearch.WordTrace tailWord_6606618 prefixEnd_6606618 1130790178215245936797241 := by
  unfold tailWord_6606618
  simp only [CollatzResearch.WordTrace]
  refine ⟨60240788594839695342331127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160642102919572520912883005 60240788594839695342331127)
  ·
    refine ⟨90361182892259543013496691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60240788594839695342331127 90361182892259543013496691)
    ·
      refine ⟨135541774338389314520245037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90361182892259543013496691 135541774338389314520245037)
      ·
        refine ⟨50828165376895992945091889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135541774338389314520245037 50828165376895992945091889)
        ·
          refine ⟨38121124032671994708818917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50828165376895992945091889 38121124032671994708818917)
          ·
            refine ⟨7147710756125999007903547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38121124032671994708818917 7147710756125999007903547)
            ·
              refine ⟨10721566134188998511855321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7147710756125999007903547 10721566134188998511855321)
              ·
                refine ⟨8041174600641748883891491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10721566134188998511855321 8041174600641748883891491)
                ·
                  refine ⟨12061761900962623325837237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8041174600641748883891491 12061761900962623325837237)
                  ·
                    refine ⟨1130790178215245936797241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12061761900962623325837237 1130790178215245936797241)
                    ·
                      rfl

theorem cell23_6606618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 1, 2, 1, 5].length) (baseStart_6606618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606618 prefixEnd_6606618 := by exact prefixLift 6606618
  have htrace : WordTrace (prefixWord ++ tailWord_6606618) baseStart_6606618 baseEnd_6606618 := by
    simpa [prefixWord, tailWord_6606618, baseEnd_6606618] using wordTrace_append hprefix tailTrace_6606618
  have hstable : (prefixWord ++ tailWord_6606618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606618).length < 2 ^ (prefixWord ++ tailWord_6606618).sum := by decide
  have hdescent : baseEnd_6606618 < baseStart_6606618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606641 : List Nat := [1, 2, 2, 3, 2, 2, 3, 1, 1, 1, 5]
def baseStart_6606641 : Nat := 118140960795 + 6606641 * 2 ^ 59
def prefixEnd_6606641 : Nat := 4983230072969 + 3 ^ 40 * 6606641 * 2
def baseEnd_6606641 : Nat := 3392382344700791220404117

theorem tailTrace_6606641 : CollatzResearch.WordTrace tailWord_6606641 prefixEnd_6606641 3392382344700791220404117 := by
  unfold tailWord_6606641
  simp only [CollatzResearch.WordTrace]
  refine ⟨240963993258275456297411777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160642662172183637531607851 240963993258275456297411777)
  ·
    refine ⟨180722994943706592223058833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240963993258275456297411777 180722994943706592223058833)
    ·
      refine ⟨135542246207779944167294125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180722994943706592223058833 135542246207779944167294125)
      ·
        refine ⟨50828342327917479062735297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135542246207779944167294125 50828342327917479062735297)
        ·
          refine ⟨38121256745938109297051473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50828342327917479062735297 38121256745938109297051473)
          ·
            refine ⟨28590942559453581972788605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38121256745938109297051473 28590942559453581972788605)
            ·
              refine ⟨10721603459795093239795727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28590942559453581972788605 10721603459795093239795727)
              ·
                refine ⟨16082405189692639859693591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10721603459795093239795727 16082405189692639859693591)
                ·
                  refine ⟨24123607784538959789540387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16082405189692639859693591 24123607784538959789540387)
                  ·
                    refine ⟨36185411676808439684310581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24123607784538959789540387 36185411676808439684310581)
                    ·
                      refine ⟨3392382344700791220404117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36185411676808439684310581 3392382344700791220404117)
                      ·
                        rfl

theorem cell23_6606641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_6606641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606641 prefixEnd_6606641 := by exact prefixLift 6606641
  have htrace : WordTrace (prefixWord ++ tailWord_6606641) baseStart_6606641 baseEnd_6606641 := by
    simpa [prefixWord, tailWord_6606641, baseEnd_6606641] using wordTrace_append hprefix tailTrace_6606641
  have hstable : (prefixWord ++ tailWord_6606641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606641).length < 2 ^ (prefixWord ++ tailWord_6606641).sum := by decide
  have hdescent : baseEnd_6606641 < baseStart_6606641 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606648 : List Nat := [2, 1, 2, 1, 3, 4, 2, 2, 2, 4]
def baseStart_6606648 : Nat := 118140960795 + 6606648 * 2 ^ 59
def prefixEnd_6606648 : Nat := 4983230072969 + 3 ^ 40 * 6606648 * 2
def baseEnd_6606648 : Nat := 1130795313021790897672195

theorem tailTrace_6606648 : CollatzResearch.WordTrace tailWord_6606648 prefixEnd_6606648 1130795313021790897672195 := by
  unfold tailWord_6606648
  simp only [CollatzResearch.WordTrace]
  refine ⟨120482124284625048246458299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160642832379500064328611065 120482124284625048246458299)
  ·
    refine ⟨180723186426937572369687449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120482124284625048246458299 180723186426937572369687449)
    ·
      refine ⟨135542389820203179277265587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180723186426937572369687449 135542389820203179277265587)
      ·
        refine ⟨203313584730304768915898381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135542389820203179277265587 203313584730304768915898381)
        ·
          refine ⟨76242594273864288343461893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203313584730304768915898381 76242594273864288343461893)
          ·
            refine ⟨14295486426349554064399105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76242594273864288343461893 14295486426349554064399105)
            ·
              refine ⟨10721614819762165548299329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14295486426349554064399105 10721614819762165548299329)
              ·
                refine ⟨8041211114821624161224497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10721614819762165548299329 8041211114821624161224497)
                ·
                  refine ⟨6030908336116218120918373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8041211114821624161224497 6030908336116218120918373)
                  ·
                    refine ⟨1130795313021790897672195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6030908336116218120918373 1130795313021790897672195)
                    ·
                      rfl

theorem cell23_6606648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_6606648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606648 prefixEnd_6606648 := by exact prefixLift 6606648
  have htrace : WordTrace (prefixWord ++ tailWord_6606648) baseStart_6606648 baseEnd_6606648 := by
    simpa [prefixWord, tailWord_6606648, baseEnd_6606648] using wordTrace_append hprefix tailTrace_6606648
  have hstable : (prefixWord ++ tailWord_6606648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606648).length < 2 ^ (prefixWord ++ tailWord_6606648).sum := by decide
  have hdescent : baseEnd_6606648 < baseStart_6606648 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606668 : List Nat := [2, 2, 1, 3, 4, 1, 2, 1, 1, 2, 4]
def baseStart_6606668 : Nat := 118140960795 + 6606668 * 2 ^ 59
def prefixEnd_6606668 : Nat := 4983230072969 + 3 ^ 40 * 6606668 * 2
def baseEnd_6606668 : Nat := 3392396208678462614766493

theorem tailTrace_6606668 : CollatzResearch.WordTrace tailWord_6606668 prefixEnd_6606668 3392396208678462614766493 := by
  unfold tailWord_6606668
  simp only [CollatzResearch.WordTrace]
  refine ⟨120482489014588819954322329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160643318686118426605763105 120482489014588819954322329)
  ·
    refine ⟨90361866760941614965741747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120482489014588819954322329 90361866760941614965741747)
    ·
      refine ⟨135542800141412422448612621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90361866760941614965741747 135542800141412422448612621)
      ·
        refine ⟨50828550053029658418229733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135542800141412422448612621 50828550053029658418229733)
        ·
          refine ⟨9530353134943060953418075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50828550053029658418229733 9530353134943060953418075)
          ·
            refine ⟨14295529702414591430127113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9530353134943060953418075 14295529702414591430127113)
            ·
              refine ⟨10721647276810943572595335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14295529702414591430127113 10721647276810943572595335)
              ·
                refine ⟨16082470915216415358893003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10721647276810943572595335 16082470915216415358893003)
                ·
                  refine ⟨24123706372824623038339505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16082470915216415358893003 24123706372824623038339505)
                  ·
                    refine ⟨18092779779618467278754629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24123706372824623038339505 18092779779618467278754629)
                    ·
                      refine ⟨3392396208678462614766493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18092779779618467278754629 3392396208678462614766493)
                      ·
                        rfl

theorem cell23_6606668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 1, 1, 2, 4].length) (baseStart_6606668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606668 prefixEnd_6606668 := by exact prefixLift 6606668
  have htrace : WordTrace (prefixWord ++ tailWord_6606668) baseStart_6606668 baseEnd_6606668 := by
    simpa [prefixWord, tailWord_6606668, baseEnd_6606668] using wordTrace_append hprefix tailTrace_6606668
  have hstable : (prefixWord ++ tailWord_6606668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606668).length < 2 ^ (prefixWord ++ tailWord_6606668).sum := by decide
  have hdescent : baseEnd_6606668 < baseStart_6606668 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606692 : List Nat := [2, 3, 1, 1, 5, 2, 2, 1, 1, 2, 3]
def baseStart_6606692 : Nat := 118140960795 + 6606692 * 2 ^ 59
def prefixEnd_6606692 : Nat := 4983230072969 + 3 ^ 40 * 6606692 * 2
def baseEnd_6606692 : Nat := 3392408532214170520866383

theorem tailTrace_6606692 : CollatzResearch.WordTrace tailWord_6606692 prefixEnd_6606692 3392408532214170520866383 := by
  unfold tailWord_6606692
  simp only [CollatzResearch.WordTrace]
  refine ⟨120482926690545346003759165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160643902254060461338345553 120482926690545346003759165)
  ·
    refine ⟨45181097508954504751409687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120482926690545346003759165 45181097508954504751409687)
    ·
      refine ⟨67771646263431757127114531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45181097508954504751409687 67771646263431757127114531)
      ·
        refine ⟨101657469395147635690671797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67771646263431757127114531 101657469395147635690671797)
        ·
          refine ⟨9530387755795090846000481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101657469395147635690671797 9530387755795090846000481)
          ·
            refine ⟨7147790816846318134500361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9530387755795090846000481 7147790816846318134500361)
            ·
              refine ⟨5360843112634738600875271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7147790816846318134500361 5360843112634738600875271)
              ·
                refine ⟨8041264668952107901312907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5360843112634738600875271 8041264668952107901312907)
                ·
                  refine ⟨12061897003428161851969361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8041264668952107901312907 12061897003428161851969361)
                  ·
                    refine ⟨9046422752571121388977021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12061897003428161851969361 9046422752571121388977021)
                    ·
                      refine ⟨3392408532214170520866383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9046422752571121388977021 3392408532214170520866383)
                      ·
                        rfl

theorem cell23_6606692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 2, 1, 1, 2, 3].length) (baseStart_6606692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606692 prefixEnd_6606692 := by exact prefixLift 6606692
  have htrace : WordTrace (prefixWord ++ tailWord_6606692) baseStart_6606692 baseEnd_6606692 := by
    simpa [prefixWord, tailWord_6606692, baseEnd_6606692] using wordTrace_append hprefix tailTrace_6606692
  have hstable : (prefixWord ++ tailWord_6606692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606692).length < 2 ^ (prefixWord ++ tailWord_6606692).sum := by decide
  have hdescent : baseEnd_6606692 < baseStart_6606692 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606711 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 2, 8, 2]
def baseStart_6606711 : Nat := 118140960795 + 6606711 * 2 ^ 59
def prefixEnd_6606711 : Nat := 4983230072969 + 3 ^ 40 * 6606711 * 2
def baseEnd_6606711 : Nat := 3392418288346605946528795

theorem tailTrace_6606711 : CollatzResearch.WordTrace tailWord_6606711 prefixEnd_6606711 3392418288346605946528795 := by
  unfold tailWord_6606711
  simp only [CollatzResearch.WordTrace]
  refine ⟨240966546368021858252459987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160644364245347905501639991 240966546368021858252459987)
  ·
    refine ⟨361449819552032787378689981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240966546368021858252459987 361449819552032787378689981)
    ·
      refine ⟨135543682332012295267008743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361449819552032787378689981 135543682332012295267008743)
      ·
        refine ⟨203315523498018442900513115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135543682332012295267008743 203315523498018442900513115)
        ·
          refine ⟨304973285247027664350769673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203315523498018442900513115 304973285247027664350769673)
          ·
            refine ⟨228729963935270748263077255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 304973285247027664350769673 228729963935270748263077255)
            ·
              refine ⟨343094945902906122394615883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228729963935270748263077255 343094945902906122394615883)
              ·
                refine ⟨514642418854359183591923825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343094945902906122394615883 514642418854359183591923825)
                ·
                  refine ⟨385981814140769387693942869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 514642418854359183591923825 385981814140769387693942869)
                  ·
                    refine ⟨4523224384462141262038393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 385981814140769387693942869 4523224384462141262038393)
                    ·
                      refine ⟨3392418288346605946528795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4523224384462141262038393 3392418288346605946528795)
                      ·
                        rfl

theorem cell23_6606711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 8, 2].length) (baseStart_6606711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606711 prefixEnd_6606711 := by exact prefixLift 6606711
  have htrace : WordTrace (prefixWord ++ tailWord_6606711) baseStart_6606711 baseEnd_6606711 := by
    simpa [prefixWord, tailWord_6606711, baseEnd_6606711] using wordTrace_append hprefix tailTrace_6606711
  have hstable : (prefixWord ++ tailWord_6606711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606711).length < 2 ^ (prefixWord ++ tailWord_6606711).sum := by decide
  have hdescent : baseEnd_6606711 < baseStart_6606711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606748 : List Nat := [2, 2, 3, 3, 1, 2, 1, 1, 2, 1, 5]
def baseStart_6606748 : Nat := 118140960795 + 6606748 * 2 ^ 59
def prefixEnd_6606748 : Nat := 4983230072969 + 3 ^ 40 * 6606748 * 2
def baseEnd_6606748 : Nat := 3392437287130822301766125

theorem tailTrace_6606748 : CollatzResearch.WordTrace tailWord_6606748 prefixEnd_6606748 3392437287130822301766125 := by
  unfold tailWord_6606748
  simp only [CollatzResearch.WordTrace]
  refine ⟨120483947934443906785778449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160645263912591875714371265 120483947934443906785778449)
  ·
    refine ⟨90362960950832930089333837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120483947934443906785778449 90362960950832930089333837)
    ·
      refine ⟨33886110356562348783500189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90362960950832930089333837 33886110356562348783500189)
      ·
        refine ⟨12707291383710880793812571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33886110356562348783500189 12707291383710880793812571)
        ·
          refine ⟨19060937075566321190718857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12707291383710880793812571 19060937075566321190718857)
          ·
            refine ⟨14295702806674740893039143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19060937075566321190718857 14295702806674740893039143)
            ·
              refine ⟨21443554210012111339558715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14295702806674740893039143 21443554210012111339558715)
              ·
                refine ⟨32165331315018167009338073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21443554210012111339558715 32165331315018167009338073)
                ·
                  refine ⟨24123998486263625257003555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32165331315018167009338073 24123998486263625257003555)
                  ·
                    refine ⟨36185997729395437885505333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24123998486263625257003555 36185997729395437885505333)
                    ·
                      refine ⟨3392437287130822301766125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36185997729395437885505333 3392437287130822301766125)
                      ·
                        rfl

theorem cell23_6606748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_6606748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606748 prefixEnd_6606748 := by exact prefixLift 6606748
  have htrace : WordTrace (prefixWord ++ tailWord_6606748) baseStart_6606748 baseEnd_6606748 := by
    simpa [prefixWord, tailWord_6606748, baseEnd_6606748] using wordTrace_append hprefix tailTrace_6606748
  have hstable : (prefixWord ++ tailWord_6606748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606748).length < 2 ^ (prefixWord ++ tailWord_6606748).sum := by decide
  have hdescent : baseEnd_6606748 < baseStart_6606748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606761 : List Nat := [1, 2, 1, 1, 1, 1, 4, 4, 2, 3, 3]
def baseStart_6606761 : Nat := 118140960795 + 6606761 * 2 ^ 59
def prefixEnd_6606761 : Nat := 4983230072969 + 3 ^ 40 * 6606761 * 2
def baseEnd_6606761 : Nat := 3392443962379330750903565

theorem tailTrace_6606761 : CollatzResearch.WordTrace tailWord_6606761 prefixEnd_6606761 3392443962379330750903565 := by
  unfold tailWord_6606761
  simp only [CollatzResearch.WordTrace]
  refine ⟨240968370017840716791780137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160645580011893811194520091 240968370017840716791780137)
  ·
    refine ⟨180726277513380537593835103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240968370017840716791780137 180726277513380537593835103)
    ·
      refine ⟨271089416270070806390752655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180726277513380537593835103 271089416270070806390752655)
      ·
        refine ⟨406634124405106209586128983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271089416270070806390752655 406634124405106209586128983)
        ·
          refine ⟨609951186607659314379193475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406634124405106209586128983 609951186607659314379193475)
          ·
            refine ⟨914926779911488971568790213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609951186607659314379193475 914926779911488971568790213)
            ·
              refine ⟨171548771233404182169148165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 914926779911488971568790213 171548771233404182169148165)
              ·
                refine ⟨32165394606263284156715281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171548771233404182169148165 32165394606263284156715281)
                ·
                  refine ⟨24124045954697463117536461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32165394606263284156715281 24124045954697463117536461)
                  ·
                    refine ⟨9046517233011548669076173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24124045954697463117536461 9046517233011548669076173)
                    ·
                      refine ⟨3392443962379330750903565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9046517233011548669076173 3392443962379330750903565)
                      ·
                        rfl

theorem cell23_6606761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 3, 3].length) (baseStart_6606761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606761 prefixEnd_6606761 := by exact prefixLift 6606761
  have htrace : WordTrace (prefixWord ++ tailWord_6606761) baseStart_6606761 baseEnd_6606761 := by
    simpa [prefixWord, tailWord_6606761, baseEnd_6606761] using wordTrace_append hprefix tailTrace_6606761
  have hstable : (prefixWord ++ tailWord_6606761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606761).length < 2 ^ (prefixWord ++ tailWord_6606761).sum := by decide
  have hdescent : baseEnd_6606761 < baseStart_6606761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606798 : List Nat := [4, 1, 1, 1, 2, 2, 4, 1, 2, 5]
def baseStart_6606798 : Nat := 118140960795 + 6606798 * 2 ^ 59
def prefixEnd_6606798 : Nat := 4983230072969 + 3 ^ 40 * 6606798 * 2
def baseEnd_6606798 : Nat := 1130820987054515702046965

theorem tailTrace_6606798 : CollatzResearch.WordTrace tailWord_6606798 prefixEnd_6606798 1130820987054515702046965 := by
  unfold tailWord_6606798
  simp only [CollatzResearch.WordTrace]
  refine ⟨30121214939838334013859631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160646479679137781407251365 30121214939838334013859631)
  ·
    refine ⟨45181822409757501020789447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30121214939838334013859631 45181822409757501020789447)
    ·
      refine ⟨67772733614636251531184171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45181822409757501020789447 67772733614636251531184171)
      ·
        refine ⟨101659100421954377296776257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67772733614636251531184171 101659100421954377296776257)
        ·
          refine ⟨76244325316465782972582193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101659100421954377296776257 76244325316465782972582193)
          ·
            refine ⟨57183243987349337229436645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76244325316465782972582193 57183243987349337229436645)
            ·
              refine ⟨10721858247628000730519371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57183243987349337229436645 10721858247628000730519371)
              ·
                refine ⟨16082787371442001095779057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10721858247628000730519371 16082787371442001095779057)
                ·
                  refine ⟨12062090528581500821834293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16082787371442001095779057 12062090528581500821834293)
                  ·
                    refine ⟨1130820987054515702046965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12062090528581500821834293 1130820987054515702046965)
                    ·
                      rfl

theorem cell23_6606798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 4, 1, 2, 5].length) (baseStart_6606798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606798 prefixEnd_6606798 := by exact prefixLift 6606798
  have htrace : WordTrace (prefixWord ++ tailWord_6606798) baseStart_6606798 baseEnd_6606798 := by
    simpa [prefixWord, tailWord_6606798, baseEnd_6606798] using wordTrace_append hprefix tailTrace_6606798
  have hstable : (prefixWord ++ tailWord_6606798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606798).length < 2 ^ (prefixWord ++ tailWord_6606798).sum := by decide
  have hdescent : baseEnd_6606798 < baseStart_6606798 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606855 : List Nat := [1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 3]
def baseStart_6606855 : Nat := 118140960795 + 6606855 * 2 ^ 59
def prefixEnd_6606855 : Nat := 4983230072969 + 3 ^ 40 * 6606855 * 2
def baseEnd_6606855 : Nat := 3392492229560853383128133

theorem tailTrace_6606855 : CollatzResearch.WordTrace tailWord_6606855 prefixEnd_6606855 3392492229560853383128133 := by
  unfold tailWord_6606855
  simp only [CollatzResearch.WordTrace]
  refine ⟨240971798479500170845702019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160647865653000113897134679 240971798479500170845702019)
  ·
    refine ⟨361457697719250256268553029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240971798479500170845702019 361457697719250256268553029)
    ·
      refine ⟨67773318322359423050353693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361457697719250256268553029 67773318322359423050353693)
      ·
        refine ⟨25414994370884783643882635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67773318322359423050353693 25414994370884783643882635)
        ·
          refine ⟨38122491556327175465823953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25414994370884783643882635 38122491556327175465823953)
          ·
            refine ⟨28591868667245381599367965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38122491556327175465823953 28591868667245381599367965)
            ·
              refine ⟨10721950750217018099762987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28591868667245381599367965 10721950750217018099762987)
              ·
                refine ⟨16082926125325527149644481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10721950750217018099762987 16082926125325527149644481)
                ·
                  refine ⟨12062194593994145362233361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16082926125325527149644481 12062194593994145362233361)
                  ·
                    refine ⟨9046645945495609021675021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12062194593994145362233361 9046645945495609021675021)
                    ·
                      refine ⟨3392492229560853383128133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9046645945495609021675021 3392492229560853383128133)
                      ·
                        rfl

theorem cell23_6606855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_6606855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606855 prefixEnd_6606855 := by exact prefixLift 6606855
  have htrace : WordTrace (prefixWord ++ tailWord_6606855) baseStart_6606855 baseEnd_6606855 := by
    simpa [prefixWord, tailWord_6606855, baseEnd_6606855] using wordTrace_append hprefix tailTrace_6606855
  have hstable : (prefixWord ++ tailWord_6606855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606855).length < 2 ^ (prefixWord ++ tailWord_6606855).sum := by decide
  have hdescent : baseEnd_6606855 < baseStart_6606855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606862 : List Nat := [4, 1, 1, 2, 2, 1, 4, 3, 1, 4]
def baseStart_6606862 : Nat := 118140960795 + 6606862 * 2 ^ 59
def prefixEnd_6606862 : Nat := 4983230072969 + 3 ^ 40 * 6606862 * 2
def baseEnd_6606862 : Nat := 1130831941308478285246867

theorem tailTrace_6606862 : CollatzResearch.WordTrace tailWord_6606862 prefixEnd_6606862 1130831941308478285246867 := by
  unfold tailWord_6606862
  simp only [CollatzResearch.WordTrace]
  refine ⟨30121506723809351380150855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160648035860316540694137893 30121506723809351380150855)
  ·
    refine ⟨45182260085714027070226283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30121506723809351380150855 45182260085714027070226283)
    ·
      refine ⟨67773390128571040605339425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45182260085714027070226283 67773390128571040605339425)
      ·
        refine ⟨50830042596428280454004569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67773390128571040605339425 50830042596428280454004569)
        ·
          refine ⟨38122531947321210340503427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50830042596428280454004569 38122531947321210340503427)
          ·
            refine ⟨57183797920981815510755141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38122531947321210340503427 57183797920981815510755141)
            ·
              refine ⟨10721962110184090408266589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57183797920981815510755141 10721962110184090408266589)
              ·
                refine ⟨4020735791319033903099971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10721962110184090408266589 4020735791319033903099971)
                ·
                  refine ⟨6031103686978550854649957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4020735791319033903099971 6031103686978550854649957)
                  ·
                    refine ⟨1130831941308478285246867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6031103686978550854649957 1130831941308478285246867)
                    ·
                      rfl

theorem cell23_6606862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 3, 1, 4].length) (baseStart_6606862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606862 prefixEnd_6606862 := by exact prefixLift 6606862
  have htrace : WordTrace (prefixWord ++ tailWord_6606862) baseStart_6606862 baseEnd_6606862 := by
    simpa [prefixWord, tailWord_6606862, baseEnd_6606862] using wordTrace_append hprefix tailTrace_6606862
  have hstable : (prefixWord ++ tailWord_6606862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606862).length < 2 ^ (prefixWord ++ tailWord_6606862).sum := by decide
  have hdescent : baseEnd_6606862 < baseStart_6606862 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606885 : List Nat := [1, 3, 1, 2, 2, 3, 1, 3, 3, 1, 3]
def baseStart_6606885 : Nat := 118140960795 + 6606885 * 2 ^ 59
def prefixEnd_6606885 : Nat := 4983230072969 + 3 ^ 40 * 6606885 * 2
def baseEnd_6606885 : Nat := 3392507633980488265752995

theorem tailTrace_6606885 : CollatzResearch.WordTrace tailWord_6606885 prefixEnd_6606885 3392507633980488265752995 := by
  unfold tailWord_6606885
  simp only [CollatzResearch.WordTrace]
  refine ⟨240972892669391485969294109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160648595112927657312862739 240972892669391485969294109)
  ·
    refine ⟨90364834751021807238485291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240972892669391485969294109 90364834751021807238485291)
    ·
      refine ⟨135547252126532710857727937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90364834751021807238485291 135547252126532710857727937)
      ·
        refine ⟨101660439094899533143295953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135547252126532710857727937 101660439094899533143295953)
        ·
          refine ⟨76245329321174649857471965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101660439094899533143295953 76245329321174649857471965)
          ·
            refine ⟨28591998495440493696551987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76245329321174649857471965 28591998495440493696551987)
            ·
              refine ⟨42887997743160740544827981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28591998495440493696551987 42887997743160740544827981)
              ·
                refine ⟨16082999153685277704310493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42887997743160740544827981 16082999153685277704310493)
                ·
                  refine ⟨6031124682631979139116435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16082999153685277704310493 6031124682631979139116435)
                  ·
                    refine ⟨9046687023947968708674653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6031124682631979139116435 9046687023947968708674653)
                    ·
                      refine ⟨3392507633980488265752995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9046687023947968708674653 3392507633980488265752995)
                      ·
                        rfl

theorem cell23_6606885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_6606885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606885 prefixEnd_6606885 := by exact prefixLift 6606885
  have htrace : WordTrace (prefixWord ++ tailWord_6606885) baseStart_6606885 baseEnd_6606885 := by
    simpa [prefixWord, tailWord_6606885, baseEnd_6606885] using wordTrace_append hprefix tailTrace_6606885
  have hstable : (prefixWord ++ tailWord_6606885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606885).length < 2 ^ (prefixWord ++ tailWord_6606885).sum := by decide
  have hdescent : baseEnd_6606885 < baseStart_6606885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606891 : List Nat := [1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 4]
def baseStart_6606891 : Nat := 118140960795 + 6606891 * 2 ^ 59
def prefixEnd_6606891 : Nat := 4983230072969 + 3 ^ 40 * 6606891 * 2
def baseEnd_6606891 : Nat := 3392510714864415242277967

theorem tailTrace_6606891 : CollatzResearch.WordTrace tailWord_6606891 prefixEnd_6606891 3392510714864415242277967 := by
  unfold tailWord_6606891
  simp only [CollatzResearch.WordTrace]
  refine ⟨240973111507369748994012527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160648741004913165996008351 240973111507369748994012527)
  ·
    refine ⟨361459667261054623491018791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240973111507369748994012527 361459667261054623491018791)
    ·
      refine ⟨542189500891581935236528187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361459667261054623491018791 542189500891581935236528187)
      ·
        refine ⟨813284251337372902854792281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542189500891581935236528187 813284251337372902854792281)
        ·
          refine ⟨609963188503029677141094211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 813284251337372902854792281 609963188503029677141094211)
          ·
            refine ⟨914944782754544515711641317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609963188503029677141094211 914944782754544515711641317)
            ·
              refine ⟨171552146766477096695932747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 914944782754544515711641317 171552146766477096695932747)
              ·
                refine ⟨257328220149715645043899121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171552146766477096695932747 257328220149715645043899121)
                ·
                  refine ⟨192996165112286733782924341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 257328220149715645043899121 192996165112286733782924341)
                  ·
                    refine ⟨18093390479276881292149157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 192996165112286733782924341 18093390479276881292149157)
                    ·
                      refine ⟨3392510714864415242277967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18093390479276881292149157 3392510714864415242277967)
                      ·
                        rfl

theorem cell23_6606891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 4].length) (baseStart_6606891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606891 prefixEnd_6606891 := by exact prefixLift 6606891
  have htrace : WordTrace (prefixWord ++ tailWord_6606891) baseStart_6606891 baseEnd_6606891 := by
    simpa [prefixWord, tailWord_6606891, baseEnd_6606891] using wordTrace_append hprefix tailTrace_6606891
  have hstable : (prefixWord ++ tailWord_6606891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606891).length < 2 ^ (prefixWord ++ tailWord_6606891).sum := by decide
  have hdescent : baseEnd_6606891 < baseStart_6606891 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606902 : List Nat := [5, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3]
def baseStart_6606902 : Nat := 118140960795 + 6606902 * 2 ^ 59
def prefixEnd_6606902 : Nat := 4983230072969 + 3 ^ 40 * 6606902 * 2
def baseEnd_6606902 : Nat := 3392516363151614699240417

theorem tailTrace_6606902 : CollatzResearch.WordTrace tailWord_6606902 prefixEnd_6606902 3392516363151614699240417 := by
  unfold tailWord_6606902
  simp only [CollatzResearch.WordTrace]
  refine ⟨15060844544395618617041435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160649008473553265248441973 15060844544395618617041435)
  ·
    refine ⟨22591266816593427925562153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15060844544395618617041435 22591266816593427925562153)
    ·
      refine ⟨16943450112445070944171615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22591266816593427925562153 16943450112445070944171615)
      ·
        refine ⟨25415175168667606416257423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16943450112445070944171615 25415175168667606416257423)
        ·
          refine ⟨38122762753001409624386135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25415175168667606416257423 38122762753001409624386135)
          ·
            refine ⟨57184144129502114436579203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38122762753001409624386135 57184144129502114436579203)
            ·
              refine ⟨85776216194253171654868805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57184144129502114436579203 85776216194253171654868805)
              ·
                refine ⟨16083040536422469685287901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85776216194253171654868805 16083040536422469685287901)
                ·
                  refine ⟨6031140201158426131982963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16083040536422469685287901 6031140201158426131982963)
                  ·
                    refine ⟨9046710301737639197974445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6031140201158426131982963 9046710301737639197974445)
                    ·
                      refine ⟨3392516363151614699240417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9046710301737639197974445 3392516363151614699240417)
                      ·
                        rfl

theorem cell23_6606902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_6606902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606902 prefixEnd_6606902 := by exact prefixLift 6606902
  have htrace : WordTrace (prefixWord ++ tailWord_6606902) baseStart_6606902 baseEnd_6606902 := by
    simpa [prefixWord, tailWord_6606902, baseEnd_6606902] using wordTrace_append hprefix tailTrace_6606902
  have hstable : (prefixWord ++ tailWord_6606902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606902).length < 2 ^ (prefixWord ++ tailWord_6606902).sum := by decide
  have hdescent : baseEnd_6606902 < baseStart_6606902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606928 : List Nat := [2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 3]
def baseStart_6606928 : Nat := 118140960795 + 6606928 * 2 ^ 59
def prefixEnd_6606928 : Nat := 4983230072969 + 3 ^ 40 * 6606928 * 2
def baseEnd_6606928 : Nat := 3392529713648631597515297

theorem tailTrace_6606928 : CollatzResearch.WordTrace tailWord_6606928 prefixEnd_6606928 3392529713648631597515297 := by
  unfold tailWord_6606928
  simp only [CollatzResearch.WordTrace]
  refine ⟨120487230504117852156554719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160649640672157136208739625 120487230504117852156554719)
  ·
    refine ⟨180730845756176778234832079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120487230504117852156554719 180730845756176778234832079)
    ·
      refine ⟨271096268634265167352248119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180730845756176778234832079 271096268634265167352248119)
      ·
        refine ⟨406644402951397751028372179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271096268634265167352248119 406644402951397751028372179)
        ·
          refine ⟨609966604427096626542558269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406644402951397751028372179 609966604427096626542558269)
          ·
            refine ⟨228737476660161234953459351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 609966604427096626542558269 228737476660161234953459351)
            ·
              refine ⟨343106214990241852430189027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228737476660161234953459351 343106214990241852430189027)
              ·
                refine ⟨514659322485362778645283541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343106214990241852430189027 514659322485362778645283541)
                ·
                  refine ⟨12062327870750690124498833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 514659322485362778645283541 12062327870750690124498833)
                  ·
                    refine ⟨9046745903063017593374125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12062327870750690124498833 9046745903063017593374125)
                    ·
                      refine ⟨3392529713648631597515297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9046745903063017593374125 3392529713648631597515297)
                      ·
                        rfl

theorem cell23_6606928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 7, 2, 3].length) (baseStart_6606928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606928 prefixEnd_6606928 := by exact prefixLift 6606928
  have htrace : WordTrace (prefixWord ++ tailWord_6606928) baseStart_6606928 baseEnd_6606928 := by
    simpa [prefixWord, tailWord_6606928, baseEnd_6606928] using wordTrace_append hprefix tailTrace_6606928
  have hstable : (prefixWord ++ tailWord_6606928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606928).length < 2 ^ (prefixWord ++ tailWord_6606928).sum := by decide
  have hdescent : baseEnd_6606928 < baseStart_6606928 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606962 : List Nat := [3, 2, 1, 2, 2, 2, 3, 2, 1, 2, 3]
def baseStart_6606962 : Nat := 118140960795 + 6606962 * 2 ^ 59
def prefixEnd_6606962 : Nat := 4983230072969 + 3 ^ 40 * 6606962 * 2
def baseEnd_6606962 : Nat := 3392547171990884464490141

theorem tailTrace_6606962 : CollatzResearch.WordTrace tailWord_6606962 prefixEnd_6606962 3392547171990884464490141 := by
  unfold tailWord_6606962
  simp only [CollatzResearch.WordTrace]
  refine ⟨60243925272528132029961785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160650467393408352079898093 60243925272528132029961785)
  ·
    refine ⟨45182943954396099022471339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60243925272528132029961785 45182943954396099022471339)
    ·
      refine ⟨67774415931594148533707009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45182943954396099022471339 67774415931594148533707009)
      ·
        refine ⟨50830811948695611400280257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67774415931594148533707009 50830811948695611400280257)
        ·
          refine ⟨38123108961521708550210193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50830811948695611400280257 38123108961521708550210193)
          ·
            refine ⟨28592331721141281412657645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38123108961521708550210193 28592331721141281412657645)
            ·
              refine ⟨10722124395427980529746617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28592331721141281412657645 10722124395427980529746617)
              ·
                refine ⟨8041593296570985397309963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10722124395427980529746617 8041593296570985397309963)
                ·
                  refine ⟨12062389944856478095964945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8041593296570985397309963 12062389944856478095964945)
                  ·
                    refine ⟨9046792458642358571973709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12062389944856478095964945 9046792458642358571973709)
                    ·
                      refine ⟨3392547171990884464490141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9046792458642358571973709 3392547171990884464490141)
                      ·
                        rfl

theorem cell23_6606962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_6606962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606962 prefixEnd_6606962 := by exact prefixLift 6606962
  have htrace : WordTrace (prefixWord ++ tailWord_6606962) baseStart_6606962 baseEnd_6606962 := by
    simpa [prefixWord, tailWord_6606962, baseEnd_6606962] using wordTrace_append hprefix tailTrace_6606962
  have hstable : (prefixWord ++ tailWord_6606962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606962).length < 2 ^ (prefixWord ++ tailWord_6606962).sum := by decide
  have hdescent : baseEnd_6606962 < baseStart_6606962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6606992 : List Nat := [2, 1, 1, 1, 1, 1, 8, 2, 2, 1, 3]
def baseStart_6606992 : Nat := 118140960795 + 6606992 * 2 ^ 59
def prefixEnd_6606992 : Nat := 4983230072969 + 3 ^ 40 * 6606992 * 2
def baseEnd_6606992 : Nat := 3392562576410519347115003

theorem tailTrace_6606992 : CollatzResearch.WordTrace tailWord_6606992 prefixEnd_6606992 3392562576410519347115003 := by
  unfold tailWord_6606992
  simp only [CollatzResearch.WordTrace]
  refine ⟨120488397640001921621719615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160651196853335895495626153 120488397640001921621719615)
  ·
    refine ⟨180732596460002882432579423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120488397640001921621719615 180732596460002882432579423)
    ·
      refine ⟨271098894690004323648869135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180732596460002882432579423 271098894690004323648869135)
      ·
        refine ⟨406648342035006485473303703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271098894690004323648869135 406648342035006485473303703)
        ·
          refine ⟨609972513052509728209955555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406648342035006485473303703 609972513052509728209955555)
          ·
            refine ⟨914958769578764592314933333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609972513052509728209955555 914958769578764592314933333)
            ·
              refine ⟨10722173081001147566190625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 914958769578764592314933333 10722173081001147566190625)
              ·
                refine ⟨8041629810750860674642969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10722173081001147566190625 8041629810750860674642969)
                ·
                  refine ⟨6031222358063145505982227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8041629810750860674642969 6031222358063145505982227)
                  ·
                    refine ⟨9046833537094718258973341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6031222358063145505982227 9046833537094718258973341)
                    ·
                      refine ⟨3392562576410519347115003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9046833537094718258973341 3392562576410519347115003)
                      ·
                        rfl

theorem cell23_6606992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 2, 2, 1, 3].length) (baseStart_6606992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6606992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6606992 prefixEnd_6606992 := by exact prefixLift 6606992
  have htrace : WordTrace (prefixWord ++ tailWord_6606992) baseStart_6606992 baseEnd_6606992 := by
    simpa [prefixWord, tailWord_6606992, baseEnd_6606992] using wordTrace_append hprefix tailTrace_6606992
  have hstable : (prefixWord ++ tailWord_6606992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6606992).length < 2 ^ (prefixWord ++ tailWord_6606992).sum := by decide
  have hdescent : baseEnd_6606992 < baseStart_6606992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6606992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607008 : List Nat := [2, 1, 1, 4, 2, 2, 1, 1, 1, 8]
def baseStart_6607008 : Nat := 118140960795 + 6607008 * 2 ^ 59
def prefixEnd_6607008 : Nat := 4983230072969 + 3 ^ 40 * 6607008 * 2
def baseEnd_6607008 : Nat := 1130856930700330428171643

theorem tailTrace_6607008 : CollatzResearch.WordTrace tailWord_6607008 prefixEnd_6607008 1130856930700330428171643 := by
  unfold tailWord_6607008
  simp only [CollatzResearch.WordTrace]
  refine ⟨120488689423972938988010839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160651585898630585317347785 120488689423972938988010839)
  ·
    refine ⟨180733034135959408482016259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120488689423972938988010839 180733034135959408482016259)
    ·
      refine ⟨271099551203939112723024389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180733034135959408482016259 271099551203939112723024389)
      ·
        refine ⟨50831165850738583635567073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271099551203939112723024389 50831165850738583635567073)
        ·
          refine ⟨38123374388053937726675305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50831165850738583635567073 38123374388053937726675305)
          ·
            refine ⟨28592530791040453295006479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38123374388053937726675305 28592530791040453295006479)
            ·
              refine ⟨42888796186560679942509719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28592530791040453295006479 42888796186560679942509719)
              ·
                refine ⟨64333194279841019913764579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42888796186560679942509719 64333194279841019913764579)
                ·
                  refine ⟨96499791419761529870646869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64333194279841019913764579 96499791419761529870646869)
                  ·
                    refine ⟨1130856930700330428171643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96499791419761529870646869 1130856930700330428171643)
                    ·
                      rfl

theorem cell23_6607008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 1, 1, 8].length) (baseStart_6607008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607008 prefixEnd_6607008 := by exact prefixLift 6607008
  have htrace : WordTrace (prefixWord ++ tailWord_6607008) baseStart_6607008 baseEnd_6607008 := by
    simpa [prefixWord, tailWord_6607008, baseEnd_6607008] using wordTrace_append hprefix tailTrace_6607008
  have hstable : (prefixWord ++ tailWord_6607008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607008).length < 2 ^ (prefixWord ++ tailWord_6607008).sum := by decide
  have hdescent : baseEnd_6607008 < baseStart_6607008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607032 : List Nat := [2, 1, 2, 1, 2, 1, 4, 2, 4, 2, 2]
def baseStart_6607032 : Nat := 118140960795 + 6607032 * 2 ^ 59
def prefixEnd_6607032 : Nat := 4983230072969 + 3 ^ 40 * 6607032 * 2
def baseEnd_6607032 : Nat := 3392583115636699190614819

theorem tailTrace_6607032 : CollatzResearch.WordTrace tailWord_6607032 prefixEnd_6607032 3392583115636699190614819 := by
  unfold tailWord_6607032
  simp only [CollatzResearch.WordTrace]
  refine ⟨120489127099929465037447675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160652169466572620049930233 120489127099929465037447675)
  ·
    refine ⟨180733690649894197556171513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120489127099929465037447675 180733690649894197556171513)
    ·
      refine ⟨135550267987420648167128635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180733690649894197556171513 135550267987420648167128635)
      ·
        refine ⟨203325401981130972250692953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135550267987420648167128635 203325401981130972250692953)
        ·
          refine ⟨152494051485848229188019715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203325401981130972250692953 152494051485848229188019715)
          ·
            refine ⟨228741077228772343782029573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152494051485848229188019715 228741077228772343782029573)
            ·
              refine ⟨42888951980394814459130545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 228741077228772343782029573 42888951980394814459130545)
              ·
                refine ⟨32166713985296110844347909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42888951980394814459130545 32166713985296110844347909)
                ·
                  refine ⟨6031258872243020783315233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32166713985296110844347909 6031258872243020783315233)
                  ·
                    refine ⟨4523444154182265587486425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6031258872243020783315233 4523444154182265587486425)
                    ·
                      refine ⟨3392583115636699190614819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4523444154182265587486425 3392583115636699190614819)
                      ·
                        rfl

theorem cell23_6607032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 2, 4, 2, 2].length) (baseStart_6607032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607032 prefixEnd_6607032 := by exact prefixLift 6607032
  have htrace : WordTrace (prefixWord ++ tailWord_6607032) baseStart_6607032 baseEnd_6607032 := by
    simpa [prefixWord, tailWord_6607032, baseEnd_6607032] using wordTrace_append hprefix tailTrace_6607032
  have hstable : (prefixWord ++ tailWord_6607032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607032).length < 2 ^ (prefixWord ++ tailWord_6607032).sum := by decide
  have hdescent : baseEnd_6607032 < baseStart_6607032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607055 : List Nat := [1, 1, 2, 1, 1, 3, 3, 6, 5]
def baseStart_6607055 : Nat := 118140960795 + 6607055 * 2 ^ 59
def prefixEnd_6607055 : Nat := 4983230072969 + 3 ^ 40 * 6607055 * 2
def baseEnd_6607055 : Nat := 376954991743528066736357

theorem tailTrace_6607055 : CollatzResearch.WordTrace tailWord_6607055 prefixEnd_6607055 376954991743528066736357 := by
  unfold tailWord_6607055
  simp only [CollatzResearch.WordTrace]
  refine ⟨240979093078775605002982619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160652728719183736668655079 240979093078775605002982619)
  ·
    refine ⟨361468639618163407504473929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240979093078775605002982619 361468639618163407504473929)
    ·
      refine ⟨271101479713622555628355447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361468639618163407504473929 271101479713622555628355447)
      ·
        refine ⟨406652219570433833442533171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271101479713622555628355447 406652219570433833442533171)
        ·
          refine ⟨609978329355650750163799757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406652219570433833442533171 609978329355650750163799757)
          ·
            refine ⟨228741873508369031311424909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 609978329355650750163799757 228741873508369031311424909)
            ·
              refine ⟨85778202565638386741784341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228741873508369031311424909 85778202565638386741784341)
              ·
                refine ⟨4020853245264299378521141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 85778202565638386741784341 4020853245264299378521141)
                ·
                  refine ⟨376954991743528066736357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4020853245264299378521141 376954991743528066736357)
                  ·
                    rfl

theorem cell23_6607055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 6, 5].length) (baseStart_6607055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607055 prefixEnd_6607055 := by exact prefixLift 6607055
  have htrace : WordTrace (prefixWord ++ tailWord_6607055) baseStart_6607055 baseEnd_6607055 := by
    simpa [prefixWord, tailWord_6607055, baseEnd_6607055] using wordTrace_append hprefix tailTrace_6607055
  have hstable : (prefixWord ++ tailWord_6607055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607055).length < 2 ^ (prefixWord ++ tailWord_6607055).sum := by decide
  have hdescent : baseEnd_6607055 < baseStart_6607055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607065 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 2, 3, 3]
def baseStart_6607065 : Nat := 118140960795 + 6607065 * 2 ^ 59
def prefixEnd_6607065 : Nat := 4983230072969 + 3 ^ 40 * 6607065 * 2
def baseEnd_6607065 : Nat := 3392600060498297561502167

theorem tailTrace_6607065 : CollatzResearch.WordTrace tailWord_6607065 prefixEnd_6607065 3392600060498297561502167 := by
  unfold tailWord_6607065
  simp only [CollatzResearch.WordTrace]
  refine ⟨240979457808739376710846649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160652971872492917807231099 240979457808739376710846649)
  ·
    refine ⟨180734593356554532533134987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240979457808739376710846649 180734593356554532533134987)
    ·
      refine ⟨271101890034831798799702481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180734593356554532533134987 271101890034831798799702481)
      ·
        refine ⟨203326417526123849099776861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271101890034831798799702481 203326417526123849099776861)
        ·
          refine ⟨76247406572296443412416323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 203326417526123849099776861 76247406572296443412416323)
          ·
            refine ⟨114371109858444665118624485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76247406572296443412416323 114371109858444665118624485)
            ·
              refine ⟨21444583098458374709742091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114371109858444665118624485 21444583098458374709742091)
              ·
                refine ⟨32166874647687562064613137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21444583098458374709742091 32166874647687562064613137)
                ·
                  refine ⟨24125155985765671548459853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32166874647687562064613137 24125155985765671548459853)
                  ·
                    refine ⟨9046933494662126830672445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24125155985765671548459853 9046933494662126830672445)
                    ·
                      refine ⟨3392600060498297561502167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9046933494662126830672445 3392600060498297561502167)
                      ·
                        rfl

theorem cell23_6607065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 2, 3, 3].length) (baseStart_6607065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607065 prefixEnd_6607065 := by exact prefixLift 6607065
  have htrace : WordTrace (prefixWord ++ tailWord_6607065) baseStart_6607065 baseEnd_6607065 := by
    simpa [prefixWord, tailWord_6607065, baseEnd_6607065] using wordTrace_append hprefix tailTrace_6607065
  have hstable : (prefixWord ++ tailWord_6607065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607065).length < 2 ^ (prefixWord ++ tailWord_6607065).sum := by decide
  have hdescent : baseEnd_6607065 < baseStart_6607065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607102 : List Nat := [4, 2, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_6607102 : Nat := 118140960795 + 6607102 * 2 ^ 59
def prefixEnd_6607102 : Nat := 4983230072969 + 3 ^ 40 * 6607102 * 2
def baseEnd_6607102 : Nat := 1130873019760837972246499

theorem tailTrace_6607102 : CollatzResearch.WordTrace tailWord_6607102 prefixEnd_6607102 1130873019760837972246499 := by
  unfold tailWord_6607102
  simp only [CollatzResearch.WordTrace]
  refine ⟨30122600913700666503742945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160653871539736888019962373 30122600913700666503742945)
  ·
    refine ⟨22591950685275499877807209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30122600913700666503742945 22591950685275499877807209)
    ·
      refine ⟨16943963013956624908355407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22591950685275499877807209 16943963013956624908355407)
      ·
        refine ⟨25415944520934937362533111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16943963013956624908355407 25415944520934937362533111)
        ·
          refine ⟨38123916781402406043799667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25415944520934937362533111 38123916781402406043799667)
          ·
            refine ⟨57185875172103609065699501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38123916781402406043799667 57185875172103609065699501)
            ·
              refine ⟨21444703189538853399637313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57185875172103609065699501 21444703189538853399637313)
              ·
                refine ⟨16083527392154140049727985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21444703189538853399637313 16083527392154140049727985)
                ·
                  refine ⟨12062645544115605037295989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16083527392154140049727985 12062645544115605037295989)
                  ·
                    refine ⟨1130873019760837972246499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12062645544115605037295989 1130873019760837972246499)
                    ·
                      rfl

theorem cell23_6607102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_6607102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607102 prefixEnd_6607102 := by exact prefixLift 6607102
  have htrace : WordTrace (prefixWord ++ tailWord_6607102) baseStart_6607102 baseEnd_6607102 := by
    simpa [prefixWord, tailWord_6607102, baseEnd_6607102] using wordTrace_append hprefix tailTrace_6607102
  have hstable : (prefixWord ++ tailWord_6607102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607102).length < 2 ^ (prefixWord ++ tailWord_6607102).sum := by decide
  have hdescent : baseEnd_6607102 < baseStart_6607102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607106 : List Nat := [3, 4, 1, 1, 2, 2, 3, 2, 5]
def baseStart_6607106 : Nat := 118140960795 + 6607106 * 2 ^ 59
def prefixEnd_6607106 : Nat := 4983230072969 + 3 ^ 40 * 6607106 * 2
def baseEnd_6607106 : Nat := 376957901467236877898831

theorem tailTrace_6607106 : CollatzResearch.WordTrace tailWord_6607106 prefixEnd_6607106 376957901467236877898831 := by
  unfold tailWord_6607106
  simp only [CollatzResearch.WordTrace]
  refine ⟨60245238300397710178272293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160653968801060560475392781 60245238300397710178272293)
  ·
    refine ⟨11295982181324570658426055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60245238300397710178272293 11295982181324570658426055)
    ·
      refine ⟨16943973271986855987639083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11295982181324570658426055 16943973271986855987639083)
      ·
        refine ⟨25415959907980283981458625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16943973271986855987639083 25415959907980283981458625)
        ·
          refine ⟨19061969930985212986093969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25415959907980283981458625 19061969930985212986093969)
          ·
            refine ⟨14296477448238909739570477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19061969930985212986093969 14296477448238909739570477)
            ·
              refine ⟨5361179043089591152338929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14296477448238909739570477 5361179043089591152338929)
              ·
                refine ⟨4020884282317193364254197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5361179043089591152338929 4020884282317193364254197)
                ·
                  refine ⟨376957901467236877898831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4020884282317193364254197 376957901467236877898831)
                  ·
                    rfl

theorem cell23_6607106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_6607106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607106 prefixEnd_6607106 := by exact prefixLift 6607106
  have htrace : WordTrace (prefixWord ++ tailWord_6607106) baseStart_6607106 baseEnd_6607106 := by
    simpa [prefixWord, tailWord_6607106, baseEnd_6607106] using wordTrace_append hprefix tailTrace_6607106
  have hstable : (prefixWord ++ tailWord_6607106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607106).length < 2 ^ (prefixWord ++ tailWord_6607106).sum := by decide
  have hdescent : baseEnd_6607106 < baseStart_6607106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607125 : List Nat := [1, 3, 2, 1, 2, 1, 2, 1, 3, 4, 3]
def baseStart_6607125 : Nat := 118140960795 + 6607125 * 2 ^ 59
def prefixEnd_6607125 : Nat := 4983230072969 + 3 ^ 40 * 6607125 * 2
def baseEnd_6607125 : Nat := 3392630869337567326751891

theorem tailTrace_6607125 : CollatzResearch.WordTrace tailWord_6607125 prefixEnd_6607125 3392630869337567326751891 := by
  unfold tailWord_6607125
  simp only [CollatzResearch.WordTrace]
  refine ⟨240981646188522006958030829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160654430792348004638687219 240981646188522006958030829)
  ·
    refine ⟨90368117320695752609261561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240981646188522006958030829 90368117320695752609261561)
    ·
      refine ⟨67776087990521814456946171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90368117320695752609261561 67776087990521814456946171)
      ·
        refine ⟨101664131985782721685419257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67776087990521814456946171 101664131985782721685419257)
        ·
          refine ⟨76248098989337041264064443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101664131985782721685419257 76248098989337041264064443)
          ·
            refine ⟨114372148484005561896096665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76248098989337041264064443 114372148484005561896096665)
            ·
              refine ⟨85779111363004171422072499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114372148484005561896096665 85779111363004171422072499)
              ·
                refine ⟨128668667044506257133108749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85779111363004171422072499 128668667044506257133108749)
                ·
                  refine ⟨48250750141689846424915781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128668667044506257133108749 48250750141689846424915781)
                  ·
                    refine ⟨9047015651566846204671709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48250750141689846424915781 9047015651566846204671709)
                    ·
                      refine ⟨3392630869337567326751891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9047015651566846204671709 3392630869337567326751891)
                      ·
                        rfl

theorem cell23_6607125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 3, 4, 3].length) (baseStart_6607125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607125 prefixEnd_6607125 := by exact prefixLift 6607125
  have htrace : WordTrace (prefixWord ++ tailWord_6607125) baseStart_6607125 baseEnd_6607125 := by
    simpa [prefixWord, tailWord_6607125, baseEnd_6607125] using wordTrace_append hprefix tailTrace_6607125
  have hstable : (prefixWord ++ tailWord_6607125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607125).length < 2 ^ (prefixWord ++ tailWord_6607125).sum := by decide
  have hdescent : baseEnd_6607125 < baseStart_6607125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607162 : List Nat := [3, 1, 1, 1, 4, 3, 2, 2, 6]
def baseStart_6607162 : Nat := 118140960795 + 6607162 * 2 ^ 59
def prefixEnd_6607162 : Nat := 4983230072969 + 3 ^ 40 * 6607162 * 2
def baseEnd_6607162 : Nat := 376961096457975964665469

theorem tailTrace_6607162 : CollatzResearch.WordTrace tailWord_6607162 prefixEnd_6607162 376961096457975964665469 := by
  unfold tailWord_6607162
  simp only [CollatzResearch.WordTrace]
  refine ⟨60245748922346990569281935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160655330459591974851418493 60245748922346990569281935)
  ·
    refine ⟨90368623383520485853922903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60245748922346990569281935 90368623383520485853922903)
    ·
      refine ⟨135552935075280728780884355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90368623383520485853922903 135552935075280728780884355)
      ·
        refine ⟨203329402612921093171326533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135552935075280728780884355 203329402612921093171326533)
        ·
          refine ⟨38124262989922704969623725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203329402612921093171326533 38124262989922704969623725)
          ·
            refine ⟨14296598621221014363608897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38124262989922704969623725 14296598621221014363608897)
            ·
              refine ⟨10722448965915760772706673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14296598621221014363608897 10722448965915760772706673)
              ·
                refine ⟨8041836724436820579530005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10722448965915760772706673 8041836724436820579530005)
                ·
                  refine ⟨376961096457975964665469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8041836724436820579530005 376961096457975964665469)
                  ·
                    rfl

theorem cell23_6607162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 6].length) (baseStart_6607162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607162 prefixEnd_6607162 := by exact prefixLift 6607162
  have htrace : WordTrace (prefixWord ++ tailWord_6607162) baseStart_6607162 baseEnd_6607162 := by
    simpa [prefixWord, tailWord_6607162, baseEnd_6607162] using wordTrace_append hprefix tailTrace_6607162
  have hstable : (prefixWord ++ tailWord_6607162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607162).length < 2 ^ (prefixWord ++ tailWord_6607162).sum := by decide
  have hdescent : baseEnd_6607162 < baseStart_6607162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607166 : List Nat := [4, 2, 1, 2, 1, 3, 1, 4, 1, 4]
def baseStart_6607166 : Nat := 118140960795 + 6607166 * 2 ^ 59
def prefixEnd_6607166 : Nat := 4983230072969 + 3 ^ 40 * 6607166 * 2
def baseEnd_6607166 : Nat := 1130883974014800555446401

theorem tailTrace_6607166 : CollatzResearch.WordTrace tailWord_6607166 prefixEnd_6607166 1130883974014800555446401 := by
  unfold tailWord_6607166
  simp only [CollatzResearch.WordTrace]
  refine ⟨30122892697671683870034169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160655427720915647306848901 30122892697671683870034169)
  ·
    refine ⟨22592169523253762902525627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30122892697671683870034169 22592169523253762902525627)
    ·
      refine ⟨33888254284880644353788441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22592169523253762902525627 33888254284880644353788441)
      ·
        refine ⟨25416190713660483265341331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33888254284880644353788441 25416190713660483265341331)
        ·
          refine ⟨38124286070490724898011997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25416190713660483265341331 38124286070490724898011997)
          ·
            refine ⟨14296607276434021836754499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38124286070490724898011997 14296607276434021836754499)
            ·
              refine ⟨21444910914651032755131749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14296607276434021836754499 21444910914651032755131749)
              ·
                refine ⟨4020920796497068641587203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21444910914651032755131749 4020920796497068641587203)
                ·
                  refine ⟨6031381194745602962380805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4020920796497068641587203 6031381194745602962380805)
                  ·
                    refine ⟨1130883974014800555446401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6031381194745602962380805 1130883974014800555446401)
                    ·
                      rfl

theorem cell23_6607166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_6607166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607166 prefixEnd_6607166 := by exact prefixLift 6607166
  have htrace : WordTrace (prefixWord ++ tailWord_6607166) baseStart_6607166 baseEnd_6607166 := by
    simpa [prefixWord, tailWord_6607166, baseEnd_6607166] using wordTrace_append hprefix tailTrace_6607166
  have hstable : (prefixWord ++ tailWord_6607166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607166).length < 2 ^ (prefixWord ++ tailWord_6607166).sum := by decide
  have hdescent : baseEnd_6607166 < baseStart_6607166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607175 : List Nat := [1, 1, 4, 1, 2, 2, 1, 1, 5, 5]
def baseStart_6607175 : Nat := 118140960795 + 6607175 * 2 ^ 59
def prefixEnd_6607175 : Nat := 4983230072969 + 3 ^ 40 * 6607175 * 2
def baseEnd_6607175 : Nat := 1130885514456764043708887

theorem tailTrace_6607175 : CollatzResearch.WordTrace tailWord_6607175 prefixEnd_6607175 1130885514456764043708887 := by
  unfold tailWord_6607175
  simp only [CollatzResearch.WordTrace]
  refine ⟨240983469838340865497350979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160655646558893910331567319 240983469838340865497350979)
  ·
    refine ⟨361475204757511298246026469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240983469838340865497350979 361475204757511298246026469)
    ·
      refine ⟨67776600892033368421129963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361475204757511298246026469 67776600892033368421129963)
      ·
        refine ⟨101664901338050052631694945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67776600892033368421129963 101664901338050052631694945)
        ·
          refine ⟨76248676003537539473771209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101664901338050052631694945 76248676003537539473771209)
          ·
            refine ⟨57186507002653154605328407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76248676003537539473771209 57186507002653154605328407)
            ·
              refine ⟨85779760503979731907992611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57186507002653154605328407 85779760503979731907992611)
              ·
                refine ⟨128669640755969597861988917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85779760503979731907992611 128669640755969597861988917)
                ·
                  refine ⟨12062778820872149799561461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 128669640755969597861988917 12062778820872149799561461)
                  ·
                    refine ⟨1130885514456764043708887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12062778820872149799561461 1130885514456764043708887)
                    ·
                      rfl

theorem cell23_6607175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_6607175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607175 prefixEnd_6607175 := by exact prefixLift 6607175
  have htrace : WordTrace (prefixWord ++ tailWord_6607175) baseStart_6607175 baseEnd_6607175 := by
    simpa [prefixWord, tailWord_6607175, baseEnd_6607175] using wordTrace_append hprefix tailTrace_6607175
  have hstable : (prefixWord ++ tailWord_6607175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607175).length < 2 ^ (prefixWord ++ tailWord_6607175).sum := by decide
  have hdescent : baseEnd_6607175 < baseStart_6607175 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607199 : List Nat := [1, 1, 2, 3, 1, 2, 5, 1, 2, 3, 2]
def baseStart_6607199 : Nat := 118140960795 + 6607199 * 2 ^ 59
def prefixEnd_6607199 : Nat := 4983230072969 + 3 ^ 40 * 6607199 * 2
def baseEnd_6607199 : Nat := 3392668866906000037226551

theorem tailTrace_6607199 : CollatzResearch.WordTrace tailWord_6607199 prefixEnd_6607199 3392668866906000037226551 := by
  unfold tailWord_6607199
  simp only [CollatzResearch.WordTrace]
  refine ⟨240984345190253917596224651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160656230126835945064149767 240984345190253917596224651)
  ·
    refine ⟨361476517785380876394336977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240984345190253917596224651 361476517785380876394336977)
    ·
      refine ⟨271107388339035657295752733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361476517785380876394336977 271107388339035657295752733)
      ·
        refine ⟨101665270627138371485907275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271107388339035657295752733 101665270627138371485907275)
        ·
          refine ⟨152497905940707557228860913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101665270627138371485907275 152497905940707557228860913)
          ·
            refine ⟨114373429455530667921645685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152497905940707557228860913 114373429455530667921645685)
            ·
              refine ⟨10722509011456000117654283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 114373429455530667921645685 10722509011456000117654283)
              ·
                refine ⟨16083763517184000176481425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10722509011456000117654283 16083763517184000176481425)
                ·
                  refine ⟨12062822637888000132361069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16083763517184000176481425 12062822637888000132361069)
                  ·
                    refine ⟨4523558489208000049635401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12062822637888000132361069 4523558489208000049635401)
                    ·
                      refine ⟨3392668866906000037226551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4523558489208000049635401 3392668866906000037226551)
                      ·
                        rfl

theorem cell23_6607199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 3, 2].length) (baseStart_6607199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607199 prefixEnd_6607199 := by exact prefixLift 6607199
  have htrace : WordTrace (prefixWord ++ tailWord_6607199) baseStart_6607199 baseEnd_6607199 := by
    simpa [prefixWord, tailWord_6607199, baseEnd_6607199] using wordTrace_append hprefix tailTrace_6607199
  have hstable : (prefixWord ++ tailWord_6607199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607199).length < 2 ^ (prefixWord ++ tailWord_6607199).sum := by decide
  have hdescent : baseEnd_6607199 < baseStart_6607199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607225 : List Nat := [1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 6]
def baseStart_6607225 : Nat := 118140960795 + 6607225 * 2 ^ 59
def prefixEnd_6607225 : Nat := 4983230072969 + 3 ^ 40 * 6607225 * 2
def baseEnd_6607225 : Nat := 3392682217403016935501431

theorem tailTrace_6607225 : CollatzResearch.WordTrace tailWord_6607225 prefixEnd_6607225 3392682217403016935501431 := by
  unfold tailWord_6607225
  simp only [CollatzResearch.WordTrace]
  refine ⟨240985293488159724036671129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160656862325439816024447419 240985293488159724036671129)
  ·
    refine ⟨180738970116119793027503347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240985293488159724036671129 180738970116119793027503347)
    ·
      refine ⟨271108455174179689541255021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180738970116119793027503347 271108455174179689541255021)
      ·
        refine ⟨101665670690317383577970633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271108455174179689541255021 101665670690317383577970633)
        ·
          refine ⟨76249253017738037683477975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101665670690317383577970633 76249253017738037683477975)
          ·
            refine ⟨114373879526607056525216963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76249253017738037683477975 114373879526607056525216963)
            ·
              refine ⟨171560819289910584787825445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114373879526607056525216963 171560819289910584787825445)
              ·
                refine ⟨32167653616858234647717271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 171560819289910584787825445 32167653616858234647717271)
                ·
                  refine ⟨48251480425287351971575907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32167653616858234647717271 48251480425287351971575907)
                  ·
                    refine ⟨72377220637931027957363861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48251480425287351971575907 72377220637931027957363861)
                    ·
                      refine ⟨3392682217403016935501431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72377220637931027957363861 3392682217403016935501431)
                      ·
                        rfl

theorem cell23_6607225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_6607225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607225 prefixEnd_6607225 := by exact prefixLift 6607225
  have htrace : WordTrace (prefixWord ++ tailWord_6607225) baseStart_6607225 baseEnd_6607225 := by
    simpa [prefixWord, tailWord_6607225, baseEnd_6607225] using wordTrace_append hprefix tailTrace_6607225
  have hstable : (prefixWord ++ tailWord_6607225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607225).length < 2 ^ (prefixWord ++ tailWord_6607225).sum := by decide
  have hdescent : baseEnd_6607225 < baseStart_6607225 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607246 : List Nat := [4, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4]
def baseStart_6607246 : Nat := 118140960795 + 6607246 * 2 ^ 59
def prefixEnd_6607246 : Nat := 4983230072969 + 3 ^ 40 * 6607246 * 2
def baseEnd_6607246 : Nat := 3392693000496761353338835

theorem tailTrace_6607246 : CollatzResearch.WordTrace tailWord_6607246 prefixEnd_6607246 3392693000496761353338835 := by
  unfold tailWord_6607246
  simp only [CollatzResearch.WordTrace]
  refine ⟨30123257427635455577898199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160657372947389096415457061 30123257427635455577898199)
  ·
    refine ⟨45184886141453183366847299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30123257427635455577898199 45184886141453183366847299)
    ·
      refine ⟨67777329212179775050270949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45184886141453183366847299 67777329212179775050270949)
      ·
        refine ⟨12708249227283707821925803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67777329212179775050270949 12708249227283707821925803)
        ·
          refine ⟨19062373840925561732888705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12708249227283707821925803 19062373840925561732888705)
          ·
            refine ⟨14296780380694171299666529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19062373840925561732888705 14296780380694171299666529)
            ·
              refine ⟨10722585285520628474749897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14296780380694171299666529 10722585285520628474749897)
              ·
                refine ⟨8041938964140471356062423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10722585285520628474749897 8041938964140471356062423)
                ·
                  refine ⟨12062908446210707034093635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8041938964140471356062423 12062908446210707034093635)
                  ·
                    refine ⟨18094362669316060551140453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12062908446210707034093635 18094362669316060551140453)
                    ·
                      refine ⟨3392693000496761353338835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18094362669316060551140453 3392693000496761353338835)
                      ·
                        rfl

theorem cell23_6607246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_6607246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607246 prefixEnd_6607246 := by exact prefixLift 6607246
  have htrace : WordTrace (prefixWord ++ tailWord_6607246) baseStart_6607246 baseEnd_6607246 := by
    simpa [prefixWord, tailWord_6607246, baseEnd_6607246] using wordTrace_append hprefix tailTrace_6607246
  have hstable : (prefixWord ++ tailWord_6607246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607246).length < 2 ^ (prefixWord ++ tailWord_6607246).sum := by decide
  have hdescent : baseEnd_6607246 < baseStart_6607246 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607274 : List Nat := [3, 1, 6, 1, 1, 1, 3, 2, 1, 1, 3]
def baseStart_6607274 : Nat := 118140960795 + 6607274 * 2 ^ 59
def prefixEnd_6607274 : Nat := 4983230072969 + 3 ^ 40 * 6607274 * 2
def baseEnd_6607274 : Nat := 3392707377955087243788707

theorem tailTrace_6607274 : CollatzResearch.WordTrace tailWord_6607274 prefixEnd_6607274 3392707377955087243788707 := by
  unfold tailWord_6607274
  simp only [CollatzResearch.WordTrace]
  refine ⟨60246770166245551351301219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160658053776654803603469917 60246770166245551351301219)
  ·
    refine ⟨90370155249368327026951829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60246770166245551351301219 90370155249368327026951829)
    ·
      refine ⟨4236101027314140329388367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90370155249368327026951829 4236101027314140329388367)
      ·
        refine ⟨6354151540971210494082551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4236101027314140329388367 6354151540971210494082551)
        ·
          refine ⟨9531227311456815741123827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6354151540971210494082551 9531227311456815741123827)
          ·
            refine ⟨14296840967185223611685741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9531227311456815741123827 14296840967185223611685741)
            ·
              refine ⟨5361315362694458854382153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14296840967185223611685741 5361315362694458854382153)
              ·
                refine ⟨4020986522020844140786615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5361315362694458854382153 4020986522020844140786615)
                ·
                  refine ⟨6031479783031266211179923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4020986522020844140786615 6031479783031266211179923)
                  ·
                    refine ⟨9047219674546899316769885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6031479783031266211179923 9047219674546899316769885)
                    ·
                      refine ⟨3392707377955087243788707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9047219674546899316769885 3392707377955087243788707)
                      ·
                        rfl

theorem cell23_6607274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_6607274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607274 prefixEnd_6607274 := by exact prefixLift 6607274
  have htrace : WordTrace (prefixWord ++ tailWord_6607274) baseStart_6607274 baseEnd_6607274 := by
    simpa [prefixWord, tailWord_6607274, baseEnd_6607274] using wordTrace_append hprefix tailTrace_6607274
  have hstable : (prefixWord ++ tailWord_6607274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607274).length < 2 ^ (prefixWord ++ tailWord_6607274).sum := by decide
  have hdescent : baseEnd_6607274 < baseStart_6607274 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607297 : List Nat := [1, 2, 7, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_6607297 : Nat := 118140960795 + 6607297 * 2 ^ 59
def prefixEnd_6607297 : Nat := 4983230072969 + 3 ^ 40 * 6607297 * 2
def baseEnd_6607297 : Nat := 3392719188010140653801101

theorem tailTrace_6607297 : CollatzResearch.WordTrace tailWord_6607297 prefixEnd_6607297 3392719188010140653801101 := by
  unfold tailWord_6607297
  simp only [CollatzResearch.WordTrace]
  refine ⟨240987919543898880333292145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160658613029265920222194763 240987919543898880333292145)
  ·
    refine ⟨180740939657924160249969109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240987919543898880333292145 180740939657924160249969109)
    ·
      refine ⟨4236115773232597505858651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 180740939657924160249969109 4236115773232597505858651)
      ·
        refine ⟨6354173659848896258787977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4236115773232597505858651 6354173659848896258787977)
        ·
          refine ⟨4765630244886672194090983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6354173659848896258787977 4765630244886672194090983)
          ·
            refine ⟨7148445367330008291136475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4765630244886672194090983 7148445367330008291136475)
            ·
              refine ⟨10722668050995012436704713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7148445367330008291136475 10722668050995012436704713)
              ·
                refine ⟨8042001038246259327528535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10722668050995012436704713 8042001038246259327528535)
                ·
                  refine ⟨12063001557369388991292803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8042001038246259327528535 12063001557369388991292803)
                  ·
                    refine ⟨18094502336054083486939205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12063001557369388991292803 18094502336054083486939205)
                    ·
                      refine ⟨3392719188010140653801101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18094502336054083486939205 3392719188010140653801101)
                      ·
                        rfl

theorem cell23_6607297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_6607297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607297 prefixEnd_6607297 := by exact prefixLift 6607297
  have htrace : WordTrace (prefixWord ++ tailWord_6607297) baseStart_6607297 baseEnd_6607297 := by
    simpa [prefixWord, tailWord_6607297, baseEnd_6607297] using wordTrace_append hprefix tailTrace_6607297
  have hstable : (prefixWord ++ tailWord_6607297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607297).length < 2 ^ (prefixWord ++ tailWord_6607297).sum := by decide
  have hdescent : baseEnd_6607297 < baseStart_6607297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607300 : List Nat := [2, 3, 3, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_6607300 : Nat := 118140960795 + 6607300 * 2 ^ 59
def prefixEnd_6607300 : Nat := 4983230072969 + 3 ^ 40 * 6607300 * 2
def baseEnd_6607300 : Nat := 3392720728452104142063587

theorem tailTrace_6607300 : CollatzResearch.WordTrace tailWord_6607300 prefixEnd_6607300 3392720728452104142063587 := by
  unfold tailWord_6607300
  simp only [CollatzResearch.WordTrace]
  refine ⟨120494014481444005922825677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160658685975258674563767569 120494014481444005922825677)
  ·
    refine ⟨45185255430541502221059629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120494014481444005922825677 45185255430541502221059629)
    ·
      refine ⟨16944470786453063332897361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45185255430541502221059629 16944470786453063332897361)
      ·
        refine ⟨12708353089839797499673021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16944470786453063332897361 12708353089839797499673021)
        ·
          refine ⟨4765632408689924062377383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12708353089839797499673021 4765632408689924062377383)
          ·
            refine ⟨7148448613034886093566075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4765632408689924062377383 7148448613034886093566075)
            ·
              refine ⟨10722672919552329140349113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7148448613034886093566075 10722672919552329140349113)
              ·
                refine ⟨8042004689664246855261835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10722672919552329140349113 8042004689664246855261835)
                ·
                  refine ⟨12063007034496370282892753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8042004689664246855261835 12063007034496370282892753)
                  ·
                    refine ⟨9047255275872277712169565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12063007034496370282892753 9047255275872277712169565)
                    ·
                      refine ⟨3392720728452104142063587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9047255275872277712169565 3392720728452104142063587)
                      ·
                        rfl

theorem cell23_6607300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_6607300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607300 prefixEnd_6607300 := by exact prefixLift 6607300
  have htrace : WordTrace (prefixWord ++ tailWord_6607300) baseStart_6607300 baseEnd_6607300 := by
    simpa [prefixWord, tailWord_6607300, baseEnd_6607300] using wordTrace_append hprefix tailTrace_6607300
  have hstable : (prefixWord ++ tailWord_6607300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607300).length < 2 ^ (prefixWord ++ tailWord_6607300).sum := by decide
  have hdescent : baseEnd_6607300 < baseStart_6607300 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607315 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 6]
def baseStart_6607315 : Nat := 118140960795 + 6607315 * 2 ^ 59
def prefixEnd_6607315 : Nat := 4983230072969 + 3 ^ 40 * 6607315 * 2
def baseEnd_6607315 : Nat := 3392728430661921583376017

theorem tailTrace_6607315 : CollatzResearch.WordTrace tailWord_6607315 prefixEnd_6607315 3392728430661921583376017 := by
  unfold tailWord_6607315
  simp only [CollatzResearch.WordTrace]
  refine ⟨240988576057833669407447399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160659050705222446271631599 240988576057833669407447399)
  ·
    refine ⟨361482864086750504111171099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240988576057833669407447399 361482864086750504111171099)
    ·
      refine ⟨542224296130125756166756649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361482864086750504111171099 542224296130125756166756649)
      ·
        refine ⟨406668222097594317125067487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542224296130125756166756649 406668222097594317125067487)
        ·
          refine ⟨610002333146391475687601231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406668222097594317125067487 610002333146391475687601231)
          ·
            refine ⟨915003499719587213531401847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610002333146391475687601231 915003499719587213531401847)
            ·
              refine ⟨1372505249579380820297102771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 915003499719587213531401847 1372505249579380820297102771)
              ·
                refine ⟨2058757874369071230445654157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372505249579380820297102771 2058757874369071230445654157)
                ·
                  refine ⟨772034202888401711417120309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2058757874369071230445654157 772034202888401711417120309)
                  ·
                    refine ⟨72378206520787660445355029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 772034202888401711417120309 72378206520787660445355029)
                    ·
                      refine ⟨3392728430661921583376017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72378206520787660445355029 3392728430661921583376017)
                      ·
                        rfl

theorem cell23_6607315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_6607315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607315 prefixEnd_6607315 := by exact prefixLift 6607315
  have htrace : WordTrace (prefixWord ++ tailWord_6607315) baseStart_6607315 baseEnd_6607315 := by
    simpa [prefixWord, tailWord_6607315, baseEnd_6607315] using wordTrace_append hprefix tailTrace_6607315
  have hstable : (prefixWord ++ tailWord_6607315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607315).length < 2 ^ (prefixWord ++ tailWord_6607315).sum := by decide
  have hdescent : baseEnd_6607315 < baseStart_6607315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607322 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5]
def baseStart_6607322 : Nat := 118140960795 + 6607322 * 2 ^ 59
def prefixEnd_6607322 : Nat := 4983230072969 + 3 ^ 40 * 6607322 * 2
def baseEnd_6607322 : Nat := 3392732025026503055988485

theorem tailTrace_6607322 : CollatzResearch.WordTrace tailWord_6607322 prefixEnd_6607322 3392732025026503055988485 := by
  unfold tailWord_6607322
  simp only [CollatzResearch.WordTrace]
  refine ⟨60247207842202077400738055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160659220912538873068634813 60247207842202077400738055)
  ·
    refine ⟨90370811763303116101107083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60247207842202077400738055 90370811763303116101107083)
    ·
      refine ⟨135556217644954674151660625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90370811763303116101107083 135556217644954674151660625)
      ·
        refine ⟨101667163233716005613745469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135556217644954674151660625 101667163233716005613745469)
        ·
          refine ⟨38125186212643502105154551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101667163233716005613745469 38125186212643502105154551)
          ·
            refine ⟨57187779318965253157731827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38125186212643502105154551 57187779318965253157731827)
            ·
              refine ⟨85781668978447879736597741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57187779318965253157731827 85781668978447879736597741)
              ·
                refine ⟨32168125866917954901224153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85781668978447879736597741 32168125866917954901224153)
                ·
                  refine ⟨24126094400188466175918115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32168125866917954901224153 24126094400188466175918115)
                  ·
                    refine ⟨36189141600282699263877173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24126094400188466175918115 36189141600282699263877173)
                    ·
                      refine ⟨3392732025026503055988485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36189141600282699263877173 3392732025026503055988485)
                      ·
                        rfl

theorem cell23_6607322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_6607322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607322 prefixEnd_6607322 := by exact prefixLift 6607322
  have htrace : WordTrace (prefixWord ++ tailWord_6607322) baseStart_6607322 baseEnd_6607322 := by
    simpa [prefixWord, tailWord_6607322, baseEnd_6607322] using wordTrace_append hprefix tailTrace_6607322
  have hstable : (prefixWord ++ tailWord_6607322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607322).length < 2 ^ (prefixWord ++ tailWord_6607322).sum := by decide
  have hdescent : baseEnd_6607322 < baseStart_6607322 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607429 : List Nat := [1, 3, 1, 1, 1, 5, 2, 1, 1, 4, 3]
def baseStart_6607429 : Nat := 118140960795 + 6607429 * 2 ^ 59
def prefixEnd_6607429 : Nat := 4983230072969 + 3 ^ 40 * 6607429 * 2
def baseEnd_6607429 : Nat := 3392786967456534137350493

theorem tailTrace_6607429 : CollatzResearch.WordTrace tailWord_6607429 prefixEnd_6607429 3392786967456534137350493 := by
  unfold tailWord_6607429
  simp only [CollatzResearch.WordTrace]
  refine ⟨240992733979420666877097341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160661822652947111251398227 240992733979420666877097341)
  ·
    refine ⟨90372275242282750078911503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 240992733979420666877097341 90372275242282750078911503)
    ·
      refine ⟨135558412863424125118367255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90372275242282750078911503 135558412863424125118367255)
      ·
        refine ⟨203337619295136187677550883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135558412863424125118367255 203337619295136187677550883)
        ·
          refine ⟨305006428942704281516326325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203337619295136187677550883 305006428942704281516326325)
          ·
            refine ⟨28594352713378526392155593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 305006428942704281516326325 28594352713378526392155593)
            ·
              refine ⟨21445764535033894794116695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28594352713378526392155593 21445764535033894794116695)
              ·
                refine ⟨32168646802550842191175043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21445764535033894794116695 32168646802550842191175043)
                ·
                  refine ⟨48252970203826263286762565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32168646802550842191175043 48252970203826263286762565)
                  ·
                    refine ⟨9047431913217424366267981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48252970203826263286762565 9047431913217424366267981)
                    ·
                      refine ⟨3392786967456534137350493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9047431913217424366267981 3392786967456534137350493)
                      ·
                        rfl

theorem cell23_6607429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 4, 3].length) (baseStart_6607429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607429 prefixEnd_6607429 := by exact prefixLift 6607429
  have htrace : WordTrace (prefixWord ++ tailWord_6607429) baseStart_6607429 baseEnd_6607429 := by
    simpa [prefixWord, tailWord_6607429, baseEnd_6607429] using wordTrace_append hprefix tailTrace_6607429
  have hstable : (prefixWord ++ tailWord_6607429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607429).length < 2 ^ (prefixWord ++ tailWord_6607429).sum := by decide
  have hdescent : baseEnd_6607429 < baseStart_6607429 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607516 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 3, 1, 4]
def baseStart_6607516 : Nat := 118140960795 + 6607516 * 2 ^ 59
def prefixEnd_6607516 : Nat := 4983230072969 + 3 ^ 40 * 6607516 * 2
def baseEnd_6607516 : Nat := 3392831640273475296962593

theorem tailTrace_6607516 : CollatzResearch.WordTrace tailWord_6607516 prefixEnd_6607516 3392831640273475296962593 := by
  unfold tailWord_6607516
  simp only [CollatzResearch.WordTrace]
  refine ⟨120497953565052740367757201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160663938086736987157009601 120497953565052740367757201)
  ·
    refine ⟨90373465173789555275817901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120497953565052740367757201 90373465173789555275817901)
    ·
      refine ⟨33890049440171083228431713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90373465173789555275817901 33890049440171083228431713)
      ·
        refine ⟨25417537080128312421323785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33890049440171083228431713 25417537080128312421323785)
        ·
          refine ⟨19063152810096234315992839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25417537080128312421323785 19063152810096234315992839)
          ·
            refine ⟨28594729215144351473989259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19063152810096234315992839 28594729215144351473989259)
            ·
              refine ⟨42892093822716527210983889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28594729215144351473989259 42892093822716527210983889)
              ·
                refine ⟨32169070367037395408237917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42892093822716527210983889 32169070367037395408237917)
                ·
                  refine ⟨12063401387639023278089219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32169070367037395408237917 12063401387639023278089219)
                  ·
                    refine ⟨18095102081458534917133829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12063401387639023278089219 18095102081458534917133829)
                    ·
                      refine ⟨3392831640273475296962593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18095102081458534917133829 3392831640273475296962593)
                      ·
                        rfl

theorem cell23_6607516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_6607516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607516 prefixEnd_6607516 := by exact prefixLift 6607516
  have htrace : WordTrace (prefixWord ++ tailWord_6607516) baseStart_6607516 baseEnd_6607516 := by
    simpa [prefixWord, tailWord_6607516, baseEnd_6607516] using wordTrace_append hprefix tailTrace_6607516
  have hstable : (prefixWord ++ tailWord_6607516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607516).length < 2 ^ (prefixWord ++ tailWord_6607516).sum := by decide
  have hdescent : baseEnd_6607516 < baseStart_6607516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607529 : List Nat := [1, 2, 1, 1, 1, 1, 2, 7, 1, 2, 4]
def baseStart_6607529 : Nat := 118140960795 + 6607529 * 2 ^ 59
def prefixEnd_6607529 : Nat := 4983230072969 + 3 ^ 40 * 6607529 * 2
def baseEnd_6607529 : Nat := 3392838315521983746100033

theorem tailTrace_6607529 : CollatzResearch.WordTrace tailWord_6607529 prefixEnd_6607529 3392838315521983746100033 := by
  unfold tailWord_6607529
  simp only [CollatzResearch.WordTrace]
  refine ⟨240996381279058383955737641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160664254186038922637158427 240996381279058383955737641)
  ·
    refine ⟨180747285959293787966803231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240996381279058383955737641 180747285959293787966803231)
    ·
      refine ⟨271120928938940681950204847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180747285959293787966803231 271120928938940681950204847)
      ·
        refine ⟨406681393408411022925307271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271120928938940681950204847 406681393408411022925307271)
        ·
          refine ⟨610022090112616534387960907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406681393408411022925307271 610022090112616534387960907)
          ·
            refine ⟨915033135168924801581941361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610022090112616534387960907 915033135168924801581941361)
            ·
              refine ⟨686274851376693601186456021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 915033135168924801581941361 686274851376693601186456021)
              ·
                refine ⟨16084566829141256277807563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 686274851376693601186456021 16084566829141256277807563)
                ·
                  refine ⟨24126850243711884416711345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16084566829141256277807563 24126850243711884416711345)
                  ·
                    refine ⟨18095137682783913312533509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24126850243711884416711345 18095137682783913312533509)
                    ·
                      refine ⟨3392838315521983746100033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18095137682783913312533509 3392838315521983746100033)
                      ·
                        rfl

theorem cell23_6607529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 2, 4].length) (baseStart_6607529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607529 prefixEnd_6607529 := by exact prefixLift 6607529
  have htrace : WordTrace (prefixWord ++ tailWord_6607529) baseStart_6607529 baseEnd_6607529 := by
    simpa [prefixWord, tailWord_6607529, baseEnd_6607529] using wordTrace_append hprefix tailTrace_6607529
  have hstable : (prefixWord ++ tailWord_6607529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607529).length < 2 ^ (prefixWord ++ tailWord_6607529).sum := by decide
  have hdescent : baseEnd_6607529 < baseStart_6607529 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607536 : List Nat := [2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 3]
def baseStart_6607536 : Nat := 118140960795 + 6607536 * 2 ^ 59
def prefixEnd_6607536 : Nat := 4983230072969 + 3 ^ 40 * 6607536 * 2
def baseEnd_6607536 : Nat := 3392841909886565218712501

theorem tailTrace_6607536 : CollatzResearch.WordTrace tailWord_6607536 prefixEnd_6607536 3392841909886565218712501 := by
  unfold tailWord_6607536
  simp only [CollatzResearch.WordTrace]
  refine ⟨120498318295016512075621231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160664424393355349434161641 120498318295016512075621231)
  ·
    refine ⟨180747477442524768113431847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120498318295016512075621231 180747477442524768113431847)
    ·
      refine ⟨271121216163787152170147771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180747477442524768113431847 271121216163787152170147771)
      ·
        refine ⟨406681824245680728255221657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271121216163787152170147771 406681824245680728255221657)
        ·
          refine ⟨305011368184260546191416243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406681824245680728255221657 305011368184260546191416243)
          ·
            refine ⟨457517052276390819287124365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305011368184260546191416243 457517052276390819287124365)
            ·
              refine ⟨171568894603646557232671637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 457517052276390819287124365 171568894603646557232671637)
              ·
                refine ⟨8042291934545932370281483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171568894603646557232671637 8042291934545932370281483)
                ·
                  refine ⟨12063437901818898555422225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8042291934545932370281483 12063437901818898555422225)
                  ·
                    refine ⟨9047578426364173916566669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12063437901818898555422225 9047578426364173916566669)
                    ·
                      refine ⟨3392841909886565218712501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9047578426364173916566669 3392841909886565218712501)
                      ·
                        rfl

theorem cell23_6607536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 3].length) (baseStart_6607536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607536 prefixEnd_6607536 := by exact prefixLift 6607536
  have htrace : WordTrace (prefixWord ++ tailWord_6607536) baseStart_6607536 baseEnd_6607536 := by
    simpa [prefixWord, tailWord_6607536, baseEnd_6607536] using wordTrace_append hprefix tailTrace_6607536
  have hstable : (prefixWord ++ tailWord_6607536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607536).length < 2 ^ (prefixWord ++ tailWord_6607536).sum := by decide
  have hdescent : baseEnd_6607536 < baseStart_6607536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607537 : List Nat := [1, 2, 2, 6, 1, 2, 1, 1, 2, 3, 2]
def baseStart_6607537 : Nat := 118140960795 + 6607537 * 2 ^ 59
def prefixEnd_6607537 : Nat := 4983230072969 + 3 ^ 40 * 6607537 * 2
def baseEnd_6607537 : Nat := 3392842423367219714799997

theorem tailTrace_6607537 : CollatzResearch.WordTrace tailWord_6607537 prefixEnd_6607537 3392842423367219714799997 := by
  unfold tailWord_6607537
  simp only [CollatzResearch.WordTrace]
  refine ⟨240996673063029401322028865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160664448708686267548019243 240996673063029401322028865)
  ·
    refine ⟨180747504797272050991521649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240996673063029401322028865 180747504797272050991521649)
    ·
      refine ⟨135560628597954038243641237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180747504797272050991521649 135560628597954038243641237)
      ·
        refine ⟨6354404465529095542670683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 135560628597954038243641237 6354404465529095542670683)
        ·
          refine ⟨9531606698293643314006025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6354404465529095542670683 9531606698293643314006025)
          ·
            refine ⟨7148705023720232485504519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9531606698293643314006025 7148705023720232485504519)
            ·
              refine ⟨10723057535580348728256779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7148705023720232485504519 10723057535580348728256779)
              ·
                refine ⟨16084586303370523092385169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10723057535580348728256779 16084586303370523092385169)
                ·
                  refine ⟨12063439727527892319288877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16084586303370523092385169 12063439727527892319288877)
                  ·
                    refine ⟨4523789897822959619733329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12063439727527892319288877 4523789897822959619733329)
                    ·
                      refine ⟨3392842423367219714799997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4523789897822959619733329 3392842423367219714799997)
                      ·
                        rfl

theorem cell23_6607537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_6607537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607537 prefixEnd_6607537 := by exact prefixLift 6607537
  have htrace : WordTrace (prefixWord ++ tailWord_6607537) baseStart_6607537 baseEnd_6607537 := by
    simpa [prefixWord, tailWord_6607537, baseEnd_6607537] using wordTrace_append hprefix tailTrace_6607537
  have hstable : (prefixWord ++ tailWord_6607537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607537).length < 2 ^ (prefixWord ++ tailWord_6607537).sum := by decide
  have hdescent : baseEnd_6607537 < baseStart_6607537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607580 : List Nat := [2, 2, 5, 1, 1, 3, 1, 1, 1, 2, 4]
def baseStart_6607580 : Nat := 118140960795 + 6607580 * 2 ^ 59
def prefixEnd_6607580 : Nat := 4983230072969 + 3 ^ 40 * 6607580 * 2
def baseEnd_6607580 : Nat := 3392864503035363046562299

theorem tailTrace_6607580 : CollatzResearch.WordTrace tailWord_6607580 prefixEnd_6607580 3392864503035363046562299 := by
  unfold tailWord_6607580
  simp only [CollatzResearch.WordTrace]
  refine ⟨120499120700936809832922097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160665494267915746443896129 120499120700936809832922097)
  ·
    refine ⟨90374340525702607374691573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120499120700936809832922097 90374340525702607374691573)
    ·
      refine ⟨8472594424284619441377335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90374340525702607374691573 8472594424284619441377335)
      ·
        refine ⟨12708891636426929162066003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8472594424284619441377335 12708891636426929162066003)
        ·
          refine ⟨19063337454640393743099005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12708891636426929162066003 19063337454640393743099005)
          ·
            refine ⟨7148751545490147653662127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19063337454640393743099005 7148751545490147653662127)
            ·
              refine ⟨10723127318235221480493191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7148751545490147653662127 10723127318235221480493191)
              ·
                refine ⟨16084690977352832220739787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10723127318235221480493191 16084690977352832220739787)
                ·
                  refine ⟨24127036466029248331109681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16084690977352832220739787 24127036466029248331109681)
                  ·
                    refine ⟨18095277349521936248332261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24127036466029248331109681 18095277349521936248332261)
                    ·
                      refine ⟨3392864503035363046562299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18095277349521936248332261 3392864503035363046562299)
                      ·
                        rfl

theorem cell23_6607580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_6607580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607580 prefixEnd_6607580 := by exact prefixLift 6607580
  have htrace : WordTrace (prefixWord ++ tailWord_6607580) baseStart_6607580 baseEnd_6607580 := by
    simpa [prefixWord, tailWord_6607580, baseEnd_6607580] using wordTrace_append hprefix tailTrace_6607580
  have hstable : (prefixWord ++ tailWord_6607580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607580).length < 2 ^ (prefixWord ++ tailWord_6607580).sum := by decide
  have hdescent : baseEnd_6607580 < baseStart_6607580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607583 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 1, 3, 3]
def baseStart_6607583 : Nat := 118140960795 + 6607583 * 2 ^ 59
def prefixEnd_6607583 : Nat := 4983230072969 + 3 ^ 40 * 6607583 * 2
def baseEnd_6607583 : Nat := 3392866043477326534824785

theorem tailTrace_6607583 : CollatzResearch.WordTrace tailWord_6607583 prefixEnd_6607583 3392866043477326534824785 := by
  unfold tailWord_6607583
  simp only [CollatzResearch.WordTrace]
  refine ⟨240998350820862751178203403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160665567213908500785468935 240998350820862751178203403)
  ·
    refine ⟨361497526231294126767305105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 240998350820862751178203403 361497526231294126767305105)
    ·
      refine ⟨271123144673470595075478829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361497526231294126767305105 271123144673470595075478829)
      ·
        refine ⟨101671179252551473153304561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271123144673470595075478829 101671179252551473153304561)
        ·
          refine ⟨76253384439413604864978421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101671179252551473153304561 76253384439413604864978421)
          ·
            refine ⟨7148754791195025456091727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76253384439413604864978421 7148754791195025456091727)
            ·
              refine ⟨10723132186792538184137591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7148754791195025456091727 10723132186792538184137591)
              ·
                refine ⟨16084698280188807276206387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10723132186792538184137591 16084698280188807276206387)
                ·
                  refine ⟨24127047420283210914309581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16084698280188807276206387 24127047420283210914309581)
                  ·
                    refine ⟨9047642782606204092866093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24127047420283210914309581 9047642782606204092866093)
                    ·
                      refine ⟨3392866043477326534824785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9047642782606204092866093 3392866043477326534824785)
                      ·
                        rfl

theorem cell23_6607583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 3, 3].length) (baseStart_6607583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607583 prefixEnd_6607583 := by exact prefixLift 6607583
  have htrace : WordTrace (prefixWord ++ tailWord_6607583) baseStart_6607583 baseEnd_6607583 := by
    simpa [prefixWord, tailWord_6607583, baseEnd_6607583] using wordTrace_append hprefix tailTrace_6607583
  have hstable : (prefixWord ++ tailWord_6607583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607583).length < 2 ^ (prefixWord ++ tailWord_6607583).sum := by decide
  have hdescent : baseEnd_6607583 < baseStart_6607583 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607593 : List Nat := [1, 2, 1, 1, 1, 2, 5, 4, 1, 3, 2]
def baseStart_6607593 : Nat := 118140960795 + 6607593 * 2 ^ 59
def prefixEnd_6607593 : Nat := 4983230072969 + 3 ^ 40 * 6607593 * 2
def baseEnd_6607593 : Nat := 3392871178283871495699739

theorem tailTrace_6607593 : CollatzResearch.WordTrace tailWord_6607593 prefixEnd_6607593 3392871178283871495699739 := by
  unfold tailWord_6607593
  simp only [CollatzResearch.WordTrace]
  refine ⟨240998715550826522886067433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160665810367217681924044955 240998715550826522886067433)
  ·
    refine ⟨180749036663119892164550575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 240998715550826522886067433 180749036663119892164550575)
    ·
      refine ⟨271123554994679838246825863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180749036663119892164550575 271123554994679838246825863)
      ·
        refine ⟨406685332492019757370238795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271123554994679838246825863 406685332492019757370238795)
        ·
          refine ⟨610027998738029636055358193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406685332492019757370238795 610027998738029636055358193)
          ·
            refine ⟨457520999053522227041518645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610027998738029636055358193 457520999053522227041518645)
            ·
              refine ⟨42892593661267708785142373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 457520999053522227041518645 42892593661267708785142373)
              ·
                refine ⟨8042361311487695397214195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42892593661267708785142373 8042361311487695397214195)
                ·
                  refine ⟨12063541967231543095821293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8042361311487695397214195 12063541967231543095821293)
                  ·
                    refine ⟨4523828237711828660932985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12063541967231543095821293 4523828237711828660932985)
                    ·
                      refine ⟨3392871178283871495699739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4523828237711828660932985 3392871178283871495699739)
                      ·
                        rfl

theorem cell23_6607593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 3, 2].length) (baseStart_6607593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607593 prefixEnd_6607593 := by exact prefixLift 6607593
  have htrace : WordTrace (prefixWord ++ tailWord_6607593) baseStart_6607593 baseEnd_6607593 := by
    simpa [prefixWord, tailWord_6607593, baseEnd_6607593] using wordTrace_append hprefix tailTrace_6607593
  have hstable : (prefixWord ++ tailWord_6607593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607593).length < 2 ^ (prefixWord ++ tailWord_6607593).sum := by decide
  have hdescent : baseEnd_6607593 < baseStart_6607593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607626 : List Nat := [3, 1, 2, 2, 1, 2, 2, 1, 2, 4, 3]
def baseStart_6607626 : Nat := 118140960795 + 6607626 * 2 ^ 59
def prefixEnd_6607626 : Nat := 4983230072969 + 3 ^ 40 * 6607626 * 2
def baseEnd_6607626 : Nat := 3392888123145469866587087

theorem tailTrace_6607626 : CollatzResearch.WordTrace tailWord_6607626 prefixEnd_6607626 3392888123145469866587087 := by
  unfold tailWord_6607626
  simp only [CollatzResearch.WordTrace]
  refine ⟨60249979789926742380504683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160666612773137979681345821 60249979789926742380504683)
  ·
    refine ⟨90374969684890113570757025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60249979789926742380504683 90374969684890113570757025)
    ·
      refine ⟨67781227263667585178067769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90374969684890113570757025 67781227263667585178067769)
      ·
        refine ⟨50835920447750688883550827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67781227263667585178067769 50835920447750688883550827)
        ·
          refine ⟨76253880671626033325326241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50835920447750688883550827 76253880671626033325326241)
          ·
            refine ⟨57190410503719524993994681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76253880671626033325326241 57190410503719524993994681)
            ·
              refine ⟨42892807877789643745496011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57190410503719524993994681 42892807877789643745496011)
              ·
                refine ⟨64339211816684465618244017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42892807877789643745496011 64339211816684465618244017)
                ·
                  refine ⟨48254408862513349213683013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64339211816684465618244017 48254408862513349213683013)
                  ·
                    refine ⟨9047701661721252977565565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48254408862513349213683013 9047701661721252977565565)
                    ·
                      refine ⟨3392888123145469866587087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9047701661721252977565565 3392888123145469866587087)
                      ·
                        rfl

theorem cell23_6607626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_6607626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607626 prefixEnd_6607626 := by exact prefixLift 6607626
  have htrace : WordTrace (prefixWord ++ tailWord_6607626) baseStart_6607626 baseEnd_6607626 := by
    simpa [prefixWord, tailWord_6607626, baseEnd_6607626] using wordTrace_append hprefix tailTrace_6607626
  have hstable : (prefixWord ++ tailWord_6607626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607626).length < 2 ^ (prefixWord ++ tailWord_6607626).sum := by decide
  have hdescent : baseEnd_6607626 < baseStart_6607626 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607661 : List Nat := [1, 5, 3, 2, 1, 1, 3, 1, 1, 3, 2]
def baseStart_6607661 : Nat := 118140960795 + 6607661 * 2 ^ 59
def prefixEnd_6607661 : Nat := 4983230072969 + 3 ^ 40 * 6607661 * 2
def baseEnd_6607661 : Nat := 3392906094968377229649427

theorem tailTrace_6607661 : CollatzResearch.WordTrace tailWord_6607661 prefixEnd_6607661 3392906094968377229649427 := by
  unfold tailWord_6607661
  simp only [CollatzResearch.WordTrace]
  refine ⟨241001195714580170499542837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160667463809720113666361891 241001195714580170499542837)
  ·
    refine ⟨22593862098241890984332141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241001195714580170499542837 22593862098241890984332141)
    ·
      refine ⟨8472698286840709119124553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22593862098241890984332141 8472698286840709119124553)
      ·
        refine ⟨6354523715130531839343415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8472698286840709119124553 6354523715130531839343415)
        ·
          refine ⟨9531785572695797759015123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6354523715130531839343415 9531785572695797759015123)
          ·
            refine ⟨14297678359043696638522685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9531785572695797759015123 14297678359043696638522685)
            ·
              refine ⟨5361629384641386239446007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14297678359043696638522685 5361629384641386239446007)
              ·
                refine ⟨8042444076962079359169011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5361629384641386239446007 8042444076962079359169011)
                ·
                  refine ⟨12063666115443119038753517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8042444076962079359169011 12063666115443119038753517)
                  ·
                    refine ⟨4523874793291169639532569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12063666115443119038753517 4523874793291169639532569)
                    ·
                      refine ⟨3392906094968377229649427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4523874793291169639532569 3392906094968377229649427)
                      ·
                        rfl

theorem cell23_6607661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_6607661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607661 prefixEnd_6607661 := by exact prefixLift 6607661
  have htrace : WordTrace (prefixWord ++ tailWord_6607661) baseStart_6607661 baseEnd_6607661 := by
    simpa [prefixWord, tailWord_6607661, baseEnd_6607661] using wordTrace_append hprefix tailTrace_6607661
  have hstable : (prefixWord ++ tailWord_6607661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607661).length < 2 ^ (prefixWord ++ tailWord_6607661).sum := by decide
  have hdescent : baseEnd_6607661 < baseStart_6607661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607696 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 4]
def baseStart_6607696 : Nat := 118140960795 + 6607696 * 2 ^ 59
def prefixEnd_6607696 : Nat := 4983230072969 + 3 ^ 40 * 6607696 * 2
def baseEnd_6607696 : Nat := 3392924066791284592711765

theorem tailTrace_6607696 : CollatzResearch.WordTrace tailWord_6607696 prefixEnd_6607696 3392924066791284592711765 := by
  unfold tailWord_6607696
  simp only [CollatzResearch.WordTrace]
  refine ⟨120501236134726685738533471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160668314846302247651377961 120501236134726685738533471)
  ·
    refine ⟨180751854202090028607800207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120501236134726685738533471 180751854202090028607800207)
    ·
      refine ⟨271127781303135042911700311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180751854202090028607800207 271127781303135042911700311)
      ·
        refine ⟨406691671954702564367550467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271127781303135042911700311 406691671954702564367550467)
        ·
          refine ⟨610037507932053846551325701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406691671954702564367550467 610037507932053846551325701)
          ·
            refine ⟨114382032737260096228373569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 610037507932053846551325701 114382032737260096228373569)
            ·
              refine ⟨85786524552945072171280177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114382032737260096228373569 85786524552945072171280177)
              ·
                refine ⟨64339893414708804128460133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85786524552945072171280177 64339893414708804128460133)
                ·
                  refine ⟨12063730015257900774086275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64339893414708804128460133 12063730015257900774086275)
                  ·
                    refine ⟨18095595022886851161129413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12063730015257900774086275 18095595022886851161129413)
                    ·
                      refine ⟨3392924066791284592711765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18095595022886851161129413 3392924066791284592711765)
                      ·
                        rfl

theorem cell23_6607696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 4].length) (baseStart_6607696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607696 prefixEnd_6607696 := by exact prefixLift 6607696
  have htrace : WordTrace (prefixWord ++ tailWord_6607696) baseStart_6607696 baseEnd_6607696 := by
    simpa [prefixWord, tailWord_6607696, baseEnd_6607696] using wordTrace_append hprefix tailTrace_6607696
  have hstable : (prefixWord ++ tailWord_6607696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607696).length < 2 ^ (prefixWord ++ tailWord_6607696).sum := by decide
  have hdescent : baseEnd_6607696 < baseStart_6607696 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607736 : List Nat := [2, 1, 2, 1, 1, 1, 1, 8, 6]
def baseStart_6607736 : Nat := 118140960795 + 6607736 * 2 ^ 59
def prefixEnd_6607736 : Nat := 4983230072969 + 3 ^ 40 * 6607736 * 2
def baseEnd_6607736 : Nat := 376993845113051604023509

theorem tailTrace_6607736 : CollatzResearch.WordTrace tailWord_6607736 prefixEnd_6607736 376993845113051604023509 := by
  unfold tailWord_6607736
  simp only [CollatzResearch.WordTrace]
  refine ⟨120501965594654229154261531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160669287459538972205682041 120501965594654229154261531)
  ·
    refine ⟨180752948391981343731392297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120501965594654229154261531 180752948391981343731392297)
    ·
      refine ⟨135564711293986007798544223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180752948391981343731392297 135564711293986007798544223)
      ·
        refine ⟨203347066940979011697816335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135564711293986007798544223 203347066940979011697816335)
        ·
          refine ⟨305020600411468517546724503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203347066940979011697816335 305020600411468517546724503)
          ·
            refine ⟨457530900617202776320086755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305020600411468517546724503 457530900617202776320086755)
            ·
              refine ⟨686296350925804164480130133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457530900617202776320086755 686296350925804164480130133)
              ·
                refine ⟨8042535362411767552501525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 686296350925804164480130133 8042535362411767552501525)
                ·
                  refine ⟨376993845113051604023509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8042535362411767552501525 376993845113051604023509)
                  ·
                    rfl

theorem cell23_6607736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 6].length) (baseStart_6607736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607736 prefixEnd_6607736 := by exact prefixLift 6607736
  have htrace : WordTrace (prefixWord ++ tailWord_6607736) baseStart_6607736 baseEnd_6607736 := by
    simpa [prefixWord, tailWord_6607736, baseEnd_6607736] using wordTrace_append hprefix tailTrace_6607736
  have hstable : (prefixWord ++ tailWord_6607736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607736).length < 2 ^ (prefixWord ++ tailWord_6607736).sum := by decide
  have hdescent : baseEnd_6607736 < baseStart_6607736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607763 : List Nat := [1, 1, 1, 2, 1, 2, 1, 5, 5, 1, 3]
def baseStart_6607763 : Nat := 118140960795 + 6607763 * 2 ^ 59
def prefixEnd_6607763 : Nat := 4983230072969 + 3 ^ 40 * 6607763 * 2
def baseEnd_6607763 : Nat := 3392958469995135830573957

theorem tailTrace_6607763 : CollatzResearch.WordTrace tailWord_6607763 prefixEnd_6607763 3392958469995135830573957 := by
  unfold tailWord_6607763
  simp only [CollatzResearch.WordTrace]
  refine ⟨241004915960210641919755943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160669943973473761279837295 241004915960210641919755943)
  ·
    refine ⟨361507373940315962879633915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241004915960210641919755943 361507373940315962879633915)
    ·
      refine ⟨542261060910473944319450873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361507373940315962879633915 542261060910473944319450873)
      ·
        refine ⟨406695795682855458239588155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542261060910473944319450873 406695795682855458239588155)
        ·
          refine ⟨610043693524283187359382233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406695795682855458239588155 610043693524283187359382233)
          ·
            refine ⟨457532770143212390519536675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610043693524283187359382233 457532770143212390519536675)
            ·
              refine ⟨686299155214818585779305013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457532770143212390519536675 686299155214818585779305013)
              ·
                refine ⟨64340545801389242416809845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 686299155214818585779305013 64340545801389242416809845)
                ·
                  refine ⟨6031926168880241476575923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64340545801389242416809845 6031926168880241476575923)
                  ·
                    refine ⟨9047889253320362214863885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6031926168880241476575923 9047889253320362214863885)
                    ·
                      refine ⟨3392958469995135830573957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9047889253320362214863885 3392958469995135830573957)
                      ·
                        rfl

theorem cell23_6607763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 5, 5, 1, 3].length) (baseStart_6607763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607763 prefixEnd_6607763 := by exact prefixLift 6607763
  have htrace : WordTrace (prefixWord ++ tailWord_6607763) baseStart_6607763 baseEnd_6607763 := by
    simpa [prefixWord, tailWord_6607763, baseEnd_6607763] using wordTrace_append hprefix tailTrace_6607763
  have hstable : (prefixWord ++ tailWord_6607763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607763).length < 2 ^ (prefixWord ++ tailWord_6607763).sum := by decide
  have hdescent : baseEnd_6607763 < baseStart_6607763 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607830 : List Nat := [5, 2, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_6607830 : Nat := 118140960795 + 6607830 * 2 ^ 59
def prefixEnd_6607830 : Nat := 4983230072969 + 3 ^ 40 * 6607830 * 2
def baseEnd_6607830 : Nat := 1130997624399662356145383

theorem tailTrace_6607830 : CollatzResearch.WordTrace tailWord_6607830 prefixEnd_6607830 1130997624399662356145383 := by
  unfold tailWord_6607830
  simp only [CollatzResearch.WordTrace]
  refine ⟨15062959978185494522652809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160671573100645274908296629 15062959978185494522652809)
  ·
    refine ⟨11297219983639120891989607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15062959978185494522652809 11297219983639120891989607)
    ·
      refine ⟨16945829975458681337984411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11297219983639120891989607 16945829975458681337984411)
      ·
        refine ⟨25418744963188022006976617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16945829975458681337984411 25418744963188022006976617)
        ·
          refine ⟨19064058722391016505232463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25418744963188022006976617 19064058722391016505232463)
          ·
            refine ⟨28596088083586524757848695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19064058722391016505232463 28596088083586524757848695)
            ·
              refine ⟨42894132125379787136773043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28596088083586524757848695 42894132125379787136773043)
              ·
                refine ⟨64341198188069680705159565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42894132125379787136773043 64341198188069680705159565)
                ·
                  refine ⟨24127949320526130264434837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64341198188069680705159565 24127949320526130264434837)
                  ·
                    refine ⟨1130997624399662356145383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24127949320526130264434837 1130997624399662356145383)
                    ·
                      rfl

theorem cell23_6607830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_6607830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607830 prefixEnd_6607830 := by exact prefixLift 6607830
  have htrace : WordTrace (prefixWord ++ tailWord_6607830) baseStart_6607830 baseEnd_6607830 := by
    simpa [prefixWord, tailWord_6607830, baseEnd_6607830] using wordTrace_append hprefix tailTrace_6607830
  have hstable : (prefixWord ++ tailWord_6607830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607830).length < 2 ^ (prefixWord ++ tailWord_6607830).sum := by decide
  have hdescent : baseEnd_6607830 < baseStart_6607830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607833 : List Nat := [1, 2, 1, 2, 5, 1, 1, 1, 3, 2, 4]
def baseStart_6607833 : Nat := 118140960795 + 6607833 * 2 ^ 59
def prefixEnd_6607833 : Nat := 4983230072969 + 3 ^ 40 * 6607833 * 2
def baseEnd_6607833 : Nat := 3392994413640950556698635

theorem tailTrace_6607833 : CollatzResearch.WordTrace tailWord_6607833 prefixEnd_6607833 3392994413640950556698635 := by
  unfold tailWord_6607833
  simp only [CollatzResearch.WordTrace]
  refine ⟨241007469069957043874804153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160671646046638029249869435 241007469069957043874804153)
  ·
    refine ⟨180755601802467782906103115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241007469069957043874804153 180755601802467782906103115)
    ·
      refine ⟨271133402703701674359154673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180755601802467782906103115 271133402703701674359154673)
      ·
        refine ⟨203350052027776255769366005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271133402703701674359154673 203350052027776255769366005)
        ·
          refine ⟨19064067377604023978378063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 203350052027776255769366005 19064067377604023978378063)
          ·
            refine ⟨28596101066406035967567095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19064067377604023978378063 28596101066406035967567095)
            ·
              refine ⟨42894151599609053951350643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28596101066406035967567095 42894151599609053951350643)
              ·
                refine ⟨64341227399413580927025965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42894151599609053951350643 64341227399413580927025965)
                ·
                  refine ⟨24127960274780092847634737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64341227399413580927025965 24127960274780092847634737)
                  ·
                    refine ⟨18095970206085069635726053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24127960274780092847634737 18095970206085069635726053)
                    ·
                      refine ⟨3392994413640950556698635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18095970206085069635726053 3392994413640950556698635)
                      ·
                        rfl

theorem cell23_6607833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 2, 4].length) (baseStart_6607833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607833 prefixEnd_6607833 := by exact prefixLift 6607833
  have htrace : WordTrace (prefixWord ++ tailWord_6607833) baseStart_6607833 baseEnd_6607833 := by
    simpa [prefixWord, tailWord_6607833, baseEnd_6607833] using wordTrace_append hprefix tailTrace_6607833
  have hstable : (prefixWord ++ tailWord_6607833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607833).length < 2 ^ (prefixWord ++ tailWord_6607833).sum := by decide
  have hdescent : baseEnd_6607833 < baseStart_6607833 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607847 : List Nat := [1, 1, 5, 2, 2, 2, 2, 2, 2, 4]
def baseStart_6607847 : Nat := 118140960795 + 6607847 * 2 ^ 59
def prefixEnd_6607847 : Nat := 4983230072969 + 3 ^ 40 * 6607847 * 2
def baseEnd_6607847 : Nat := 1131000534123371167307857

theorem tailTrace_6607847 : CollatzResearch.WordTrace tailWord_6607847 prefixEnd_6607847 1131000534123371167307857 := by
  unfold tailWord_6607847
  simp only [CollatzResearch.WordTrace]
  refine ⟨241007979691906324265813795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160671986461270882843875863 241007979691906324265813795)
  ·
    refine ⟨361511969537859486398720693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241007979691906324265813795 361511969537859486398720693)
    ·
      refine ⟨33891747144174326849880065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 361511969537859486398720693 33891747144174326849880065)
      ·
        refine ⟨25418810358130745137410049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33891747144174326849880065 25418810358130745137410049)
        ·
          refine ⟨19064107768598058853057537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25418810358130745137410049 19064107768598058853057537)
          ·
            refine ⟨14298080826448544139793153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19064107768598058853057537 14298080826448544139793153)
            ·
              refine ⟨10723560619836408104844865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14298080826448544139793153 10723560619836408104844865)
              ·
                refine ⟨8042670464877306078633649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10723560619836408104844865 8042670464877306078633649)
                ·
                  refine ⟨6032002848657979558975237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8042670464877306078633649 6032002848657979558975237)
                  ·
                    refine ⟨1131000534123371167307857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6032002848657979558975237 1131000534123371167307857)
                    ·
                      rfl

theorem cell23_6607847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_6607847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607847 prefixEnd_6607847 := by exact prefixLift 6607847
  have htrace : WordTrace (prefixWord ++ tailWord_6607847) baseStart_6607847 baseEnd_6607847 := by
    simpa [prefixWord, tailWord_6607847, baseEnd_6607847] using wordTrace_append hprefix tailTrace_6607847
  have hstable : (prefixWord ++ tailWord_6607847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607847).length < 2 ^ (prefixWord ++ tailWord_6607847).sum := by decide
  have hdescent : baseEnd_6607847 < baseStart_6607847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607903 : List Nat := [1, 1, 2, 4, 1, 3, 1, 2, 2, 6]
def baseStart_6607903 : Nat := 118140960795 + 6607903 * 2 ^ 59
def prefixEnd_6607903 : Nat := 4983230072969 + 3 ^ 40 * 6607903 * 2
def baseEnd_6607903 : Nat := 1131010119095588427607771

theorem tailTrace_6607903 : CollatzResearch.WordTrace tailWord_6607903 prefixEnd_6607903 1131010119095588427607771 := by
  unfold tailWord_6607903
  simp only [CollatzResearch.WordTrace]
  refine ⟨241010022179703445829852363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160673348119802297219901575 241010022179703445829852363)
  ·
    refine ⟨361515033269555168744778545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241010022179703445829852363 361515033269555168744778545)
    ·
      refine ⟨271136274952166376558583909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361515033269555168744778545 271136274952166376558583909)
      ·
        refine ⟨50838051553531195604734483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271136274952166376558583909 50838051553531195604734483)
        ·
          refine ⟨76257077330296793407101725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50838051553531195604734483 76257077330296793407101725)
          ·
            refine ⟨28596403998861297527663147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76257077330296793407101725 28596403998861297527663147)
            ·
              refine ⟨42894605998291946291494721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28596403998861297527663147 42894605998291946291494721)
              ·
                refine ⟨32170954498718959718621041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42894605998291946291494721 32170954498718959718621041)
                ·
                  refine ⟨24128215874039219788965781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32170954498718959718621041 24128215874039219788965781)
                  ·
                    refine ⟨1131010119095588427607771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24128215874039219788965781 1131010119095588427607771)
                    ·
                      rfl

theorem cell23_6607903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 2, 2, 6].length) (baseStart_6607903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607903 prefixEnd_6607903 := by exact prefixLift 6607903
  have htrace : WordTrace (prefixWord ++ tailWord_6607903) baseStart_6607903 baseEnd_6607903 := by
    simpa [prefixWord, tailWord_6607903, baseEnd_6607903] using wordTrace_append hprefix tailTrace_6607903
  have hstable : (prefixWord ++ tailWord_6607903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607903).length < 2 ^ (prefixWord ++ tailWord_6607903).sum := by decide
  have hdescent : baseEnd_6607903 < baseStart_6607903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607904 : List Nat := [2, 1, 1, 7, 1, 1, 1, 1, 4, 1, 3]
def baseStart_6607904 : Nat := 118140960795 + 6607904 * 2 ^ 59
def prefixEnd_6607904 : Nat := 4983230072969 + 3 ^ 40 * 6607904 * 2
def baseEnd_6607904 : Nat := 3393030870767419778910809

theorem tailTrace_6607904 : CollatzResearch.WordTrace tailWord_6607904 prefixEnd_6607904 3393030870767419778910809 := by
  unfold tailWord_6607904
  simp only [CollatzResearch.WordTrace]
  refine ⟨120505029326349911500319383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160673372435133215333759177 120505029326349911500319383)
  ·
    refine ⟨180757543989524867250479075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120505029326349911500319383 180757543989524867250479075)
    ·
      refine ⟨271136315984287300875718613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180757543989524867250479075 271136315984287300875718613)
      ·
        refine ⟨6354757405881733614274655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 271136315984287300875718613 6354757405881733614274655)
        ·
          refine ⟨9532136108822600421411983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6354757405881733614274655 9532136108822600421411983)
          ·
            refine ⟨14298204163233900632117975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9532136108822600421411983 14298204163233900632117975)
            ·
              refine ⟨21447306244850850948176963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14298204163233900632117975 21447306244850850948176963)
              ·
                refine ⟨32170959367276276422265445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21447306244850850948176963 32170959367276276422265445)
                ·
                  refine ⟨6032054881364301829174771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32170959367276276422265445 6032054881364301829174771)
                  ·
                    refine ⟨9048082322046452743762157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6032054881364301829174771 9048082322046452743762157)
                    ·
                      refine ⟨3393030870767419778910809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9048082322046452743762157 3393030870767419778910809)
                      ·
                        rfl

theorem cell23_6607904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_6607904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607904 prefixEnd_6607904 := by exact prefixLift 6607904
  have htrace : WordTrace (prefixWord ++ tailWord_6607904) baseStart_6607904 baseEnd_6607904 := by
    simpa [prefixWord, tailWord_6607904, baseEnd_6607904] using wordTrace_append hprefix tailTrace_6607904
  have hstable : (prefixWord ++ tailWord_6607904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607904).length < 2 ^ (prefixWord ++ tailWord_6607904).sum := by decide
  have hdescent : baseEnd_6607904 < baseStart_6607904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607967 : List Nat := [1, 1, 2, 3, 1, 1, 7, 2, 5]
def baseStart_6607967 : Nat := 118140960795 + 6607967 * 2 ^ 59
def prefixEnd_6607967 : Nat := 4983230072969 + 3 ^ 40 * 6607967 * 2
def baseEnd_6607967 : Nat := 377007024449850336935891

theorem tailTrace_6607967 : CollatzResearch.WordTrace tailWord_6607967 prefixEnd_6607967 377007024449850336935891 := by
  unfold tailWord_6607967
  simp only [CollatzResearch.WordTrace]
  refine ⟨241012356451471584760182155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160674904300981056506788103 241012356451471584760182155)
  ·
    refine ⟨361518534677207377140273233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241012356451471584760182155 361518534677207377140273233)
    ·
      refine ⟨271138901007905532855204925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361518534677207377140273233 271138901007905532855204925)
      ·
        refine ⟨101677087877964574820701847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271138901007905532855204925 101677087877964574820701847)
        ·
          refine ⟨152515631816946862231052771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101677087877964574820701847 152515631816946862231052771)
          ·
            refine ⟨228773447725420293346579157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152515631816946862231052771 228773447725420293346579157)
            ·
              refine ⟨5361877681064538125310449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 228773447725420293346579157 5361877681064538125310449)
              ·
                refine ⟨4021408260798403593982837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5361877681064538125310449 4021408260798403593982837)
                ·
                  refine ⟨377007024449850336935891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4021408260798403593982837 377007024449850336935891)
                  ·
                    rfl

theorem cell23_6607967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 7, 2, 5].length) (baseStart_6607967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607967 prefixEnd_6607967 := by exact prefixLift 6607967
  have htrace : WordTrace (prefixWord ++ tailWord_6607967) baseStart_6607967 baseEnd_6607967 := by
    simpa [prefixWord, tailWord_6607967, baseEnd_6607967] using wordTrace_append hprefix tailTrace_6607967
  have hstable : (prefixWord ++ tailWord_6607967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607967).length < 2 ^ (prefixWord ++ tailWord_6607967).sum := by decide
  have hdescent : baseEnd_6607967 < baseStart_6607967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607978 : List Nat := [3, 1, 3, 2, 2, 3, 2, 1, 2, 2, 2]
def baseStart_6607978 : Nat := 118140960795 + 6607978 * 2 ^ 59
def prefixEnd_6607978 : Nat := 4983230072969 + 3 ^ 40 * 6607978 * 2
def baseEnd_6607978 : Nat := 3393068868335852489385469

theorem tailTrace_6607978 : CollatzResearch.WordTrace tailWord_6607978 prefixEnd_6607978 3393068868335852489385469 := by
  unfold tailWord_6607978
  simp only [CollatzResearch.WordTrace]
  refine ⟨60253189413607933409708147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160675171769621155759221725 60253189413607933409708147)
  ·
    refine ⟨90379784120411900114562221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60253189413607933409708147 90379784120411900114562221)
    ·
      refine ⟨33892419045154462542960833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90379784120411900114562221 33892419045154462542960833)
      ·
        refine ⟨25419314283865846907220625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33892419045154462542960833 25419314283865846907220625)
        ·
          refine ⟨19064485712899385180415469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25419314283865846907220625 19064485712899385180415469)
          ·
            refine ⟨7149182142337269442655801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19064485712899385180415469 7149182142337269442655801)
            ·
              refine ⟨5361886606752952081991851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7149182142337269442655801 5361886606752952081991851)
              ·
                refine ⟨8042829910129428122987777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5361886606752952081991851 8042829910129428122987777)
                ·
                  refine ⟨6032122432597071092240833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8042829910129428122987777 6032122432597071092240833)
                  ·
                    refine ⟨4524091824447803319180625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6032122432597071092240833 4524091824447803319180625)
                    ·
                      refine ⟨3393068868335852489385469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524091824447803319180625 3393068868335852489385469)
                      ·
                        rfl

theorem cell23_6607978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_6607978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607978 prefixEnd_6607978 := by exact prefixLift 6607978
  have htrace : WordTrace (prefixWord ++ tailWord_6607978) baseStart_6607978 baseEnd_6607978 := by
    simpa [prefixWord, tailWord_6607978, baseEnd_6607978] using wordTrace_append hprefix tailTrace_6607978
  have hstable : (prefixWord ++ tailWord_6607978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607978).length < 2 ^ (prefixWord ++ tailWord_6607978).sum := by decide
  have hdescent : baseEnd_6607978 < baseStart_6607978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6607990 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_6607990 : Nat := 118140960795 + 6607990 * 2 ^ 59
def prefixEnd_6607990 : Nat := 4983230072969 + 3 ^ 40 * 6607990 * 2
def baseEnd_6607990 : Nat := 3393075030103706442435413

theorem tailTrace_6607990 : CollatzResearch.WordTrace tailWord_6607990 prefixEnd_6607990 3393075030103706442435413 := by
  unfold tailWord_6607990
  simp only [CollatzResearch.WordTrace]
  refine ⟨15063324708149266230516839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160675463553592173125512949 15063324708149266230516839)
  ·
    refine ⟨22594987062223899345775259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15063324708149266230516839 22594987062223899345775259)
    ·
      refine ⟨33892480593335849018662889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22594987062223899345775259 33892480593335849018662889)
      ·
        refine ⟨25419360445001886763997167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33892480593335849018662889 25419360445001886763997167)
        ·
          refine ⟨38129040667502830145995751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25419360445001886763997167 38129040667502830145995751)
          ·
            refine ⟨57193561001254245218993627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38129040667502830145995751 57193561001254245218993627)
            ·
              refine ⟨85790341501881367828490441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57193561001254245218993627 85790341501881367828490441)
              ·
                refine ⟨64342756126411025871367831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85790341501881367828490441 64342756126411025871367831)
                ·
                  refine ⟨96514134189616538807051747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64342756126411025871367831 96514134189616538807051747)
                  ·
                    refine ⟨144771201284424808210577621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96514134189616538807051747 144771201284424808210577621)
                    ·
                      refine ⟨3393075030103706442435413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144771201284424808210577621 3393075030103706442435413)
                      ·
                        rfl

theorem cell23_6607990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_6607990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6607990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6607990 prefixEnd_6607990 := by exact prefixLift 6607990
  have htrace : WordTrace (prefixWord ++ tailWord_6607990) baseStart_6607990 baseEnd_6607990 := by
    simpa [prefixWord, tailWord_6607990, baseEnd_6607990] using wordTrace_append hprefix tailTrace_6607990
  have hstable : (prefixWord ++ tailWord_6607990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6607990).length < 2 ^ (prefixWord ++ tailWord_6607990).sum := by decide
  have hdescent : baseEnd_6607990 < baseStart_6607990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6607990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608000 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 4]
def baseStart_6608000 : Nat := 118140960795 + 6608000 * 2 ^ 59
def prefixEnd_6608000 : Nat := 4983230072969 + 3 ^ 40 * 6608000 * 2
def baseEnd_6608000 : Nat := 3393080164910251403310367

theorem tailTrace_6608000 : CollatzResearch.WordTrace tailWord_6608000 prefixEnd_6608000 3393080164910251403310367 := by
  unfold tailWord_6608000
  simp only [CollatzResearch.WordTrace]
  refine ⟨120506780030176015698066727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160675706706901354264088969 120506780030176015698066727)
  ·
    refine ⟨180760170045264023547100091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120506780030176015698066727 180760170045264023547100091)
    ·
      refine ⟨271140255067896035320650137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180760170045264023547100091 271140255067896035320650137)
      ·
        refine ⟨203355191300922026490487603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271140255067896035320650137 203355191300922026490487603)
        ·
          refine ⟨305032786951383039735731405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203355191300922026490487603 305032786951383039735731405)
          ·
            refine ⟨114387295106768639900899277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305032786951383039735731405 114387295106768639900899277)
            ·
              refine ⟨42895235665038239962837229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114387295106768639900899277 42895235665038239962837229)
              ·
                refine ⟨16085713374389339986063961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42895235665038239962837229 16085713374389339986063961)
                ·
                  refine ⟨12064285030792004989547971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16085713374389339986063961 12064285030792004989547971)
                  ·
                    refine ⟨18096427546188007484321957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12064285030792004989547971 18096427546188007484321957)
                    ·
                      refine ⟨3393080164910251403310367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18096427546188007484321957 3393080164910251403310367)
                      ·
                        rfl

theorem cell23_6608000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 4].length) (baseStart_6608000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608000 prefixEnd_6608000 := by exact prefixLift 6608000
  have htrace : WordTrace (prefixWord ++ tailWord_6608000) baseStart_6608000 baseEnd_6608000 := by
    simpa [prefixWord, tailWord_6608000, baseEnd_6608000] using wordTrace_append hprefix tailTrace_6608000
  have hstable : (prefixWord ++ tailWord_6608000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608000).length < 2 ^ (prefixWord ++ tailWord_6608000).sum := by decide
  have hdescent : baseEnd_6608000 < baseStart_6608000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608107 : List Nat := [1, 1, 1, 1, 2, 6, 1, 4, 1, 1, 4]
def baseStart_6608107 : Nat := 118140960795 + 6608107 * 2 ^ 59
def prefixEnd_6608107 : Nat := 4983230072969 + 3 ^ 40 * 6608107 * 2
def baseEnd_6608107 : Nat := 3393135107340282484672375

theorem tailTrace_6608107 : CollatzResearch.WordTrace tailWord_6608107 prefixEnd_6608107 3393135107340282484672375 := by
  unfold tailWord_6608107
  simp only [CollatzResearch.WordTrace]
  refine ⟨241017462670964388670278575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160678308447309592446852383 241017462670964388670278575)
  ·
    refine ⟨361526194006446583005417863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241017462670964388670278575 361526194006446583005417863)
    ·
      refine ⟨542289291009669874508126795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361526194006446583005417863 542289291009669874508126795)
      ·
        refine ⟨813433936514504811762190193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542289291009669874508126795 813433936514504811762190193)
        ·
          refine ⟨610075452385878608821642645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 813433936514504811762190193 610075452385878608821642645)
          ·
            refine ⟨28597286830588059788514499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 610075452385878608821642645 28597286830588059788514499)
            ·
              refine ⟨42895930245882089682771749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28597286830588059788514499 42895930245882089682771749)
              ·
                refine ⟨8042986921102891815519703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42895930245882089682771749 8042986921102891815519703)
                ·
                  refine ⟨12064480381654337723279555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8042986921102891815519703 12064480381654337723279555)
                  ·
                    refine ⟨18096720572481506584919333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12064480381654337723279555 18096720572481506584919333)
                    ·
                      refine ⟨3393135107340282484672375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18096720572481506584919333 3393135107340282484672375)
                      ·
                        rfl

theorem cell23_6608107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 1, 1, 4].length) (baseStart_6608107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608107 prefixEnd_6608107 := by exact prefixLift 6608107
  have htrace : WordTrace (prefixWord ++ tailWord_6608107) baseStart_6608107 baseEnd_6608107 := by
    simpa [prefixWord, tailWord_6608107, baseEnd_6608107] using wordTrace_append hprefix tailTrace_6608107
  have hstable : (prefixWord ++ tailWord_6608107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608107).length < 2 ^ (prefixWord ++ tailWord_6608107).sum := by decide
  have hdescent : baseEnd_6608107 < baseStart_6608107 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608127 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 5]
def baseStart_6608127 : Nat := 118140960795 + 6608127 * 2 ^ 59
def prefixEnd_6608127 : Nat := 4983230072969 + 3 ^ 40 * 6608127 * 2
def baseEnd_6608127 : Nat := 3393145376953372406422283

theorem tailTrace_6608127 : CollatzResearch.WordTrace tailWord_6608127 prefixEnd_6608127 3393145376953372406422283 := by
  unfold tailWord_6608127
  simp only [CollatzResearch.WordTrace]
  refine ⟨241018192130891932086006635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160678794753927954724004423 241018192130891932086006635)
  ·
    refine ⟨361527288196337898129009953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241018192130891932086006635 361527288196337898129009953)
    ·
      refine ⟨271145466147253423596757465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361527288196337898129009953 271145466147253423596757465)
      ·
        refine ⟨203359099610440067697568099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271145466147253423596757465 203359099610440067697568099)
        ·
          refine ⟨305038649415660101546352149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203359099610440067697568099 305038649415660101546352149)
          ·
            refine ⟨14298686691359067259985257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 305038649415660101546352149 14298686691359067259985257)
            ·
              refine ⟨10724015018519300444988943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14298686691359067259985257 10724015018519300444988943)
              ·
                refine ⟨16086022527778950667483415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10724015018519300444988943 16086022527778950667483415)
                ·
                  refine ⟨24129033791668426001225123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16086022527778950667483415 24129033791668426001225123)
                  ·
                    refine ⟨36193550687502639001837685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24129033791668426001225123 36193550687502639001837685)
                    ·
                      refine ⟨3393145376953372406422283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36193550687502639001837685 3393145376953372406422283)
                      ·
                        rfl

theorem cell23_6608127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 5].length) (baseStart_6608127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608127 prefixEnd_6608127 := by exact prefixLift 6608127
  have htrace : WordTrace (prefixWord ++ tailWord_6608127) baseStart_6608127 baseEnd_6608127 := by
    simpa [prefixWord, tailWord_6608127, baseEnd_6608127] using wordTrace_append hprefix tailTrace_6608127
  have hstable : (prefixWord ++ tailWord_6608127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608127).length < 2 ^ (prefixWord ++ tailWord_6608127).sum := by decide
  have hdescent : baseEnd_6608127 < baseStart_6608127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608191 : List Nat := [1, 1, 2, 2, 4, 3, 2, 2, 2, 1, 3]
def baseStart_6608191 : Nat := 118140960795 + 6608191 * 2 ^ 59
def prefixEnd_6608191 : Nat := 4983230072969 + 3 ^ 40 * 6608191 * 2
def baseEnd_6608191 : Nat := 3393178239715260156021989

theorem tailTrace_6608191 : CollatzResearch.WordTrace tailWord_6608191 prefixEnd_6608191 3393178239715260156021989 := by
  unfold tailWord_6608191
  simp only [CollatzResearch.WordTrace]
  refine ⟨241020526402660071016336427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160680350935106714010890951 241020526402660071016336427)
  ·
    refine ⟨361530789603990106524504641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241020526402660071016336427 361530789603990106524504641)
    ·
      refine ⟨271148092202992579893378481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361530789603990106524504641 271148092202992579893378481)
      ·
        refine ⟨203361069152244434920033861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271148092202992579893378481 203361069152244434920033861)
        ·
          refine ⟨38130200466045831547506349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203361069152244434920033861 38130200466045831547506349)
          ·
            refine ⟨14298825174767186830314881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38130200466045831547506349 14298825174767186830314881)
            ·
              refine ⟨10724118881075390122736161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14298825174767186830314881 10724118881075390122736161)
              ·
                refine ⟨8043089160806542592052121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10724118881075390122736161 8043089160806542592052121)
                ·
                  refine ⟨6032316870604906944039091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8043089160806542592052121 6032316870604906944039091)
                  ·
                    refine ⟨9048475305907360416058637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6032316870604906944039091 9048475305907360416058637)
                    ·
                      refine ⟨3393178239715260156021989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9048475305907360416058637 3393178239715260156021989)
                      ·
                        rfl

theorem cell23_6608191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 2, 2, 1, 3].length) (baseStart_6608191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608191 prefixEnd_6608191 := by exact prefixLift 6608191
  have htrace : WordTrace (prefixWord ++ tailWord_6608191) baseStart_6608191 baseEnd_6608191 := by
    simpa [prefixWord, tailWord_6608191, baseEnd_6608191] using wordTrace_append hprefix tailTrace_6608191
  have hstable : (prefixWord ++ tailWord_6608191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608191).length < 2 ^ (prefixWord ++ tailWord_6608191).sum := by decide
  have hdescent : baseEnd_6608191 < baseStart_6608191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608198 : List Nat := [6, 1, 1, 3, 1, 2, 1, 8]
def baseStart_6608198 : Nat := 118140960795 + 6608198 * 2 ^ 59
def prefixEnd_6608198 : Nat := 4983230072969 + 3 ^ 40 * 6608198 * 2
def baseEnd_6608198 : Nat := 125673401262216356616091

theorem tailTrace_6608198 : CollatzResearch.WordTrace tailWord_6608198 prefixEnd_6608198 125673401262216356616091 := by
  unfold tailWord_6608198
  simp only [CollatzResearch.WordTrace]
  refine ⟨7531899428551084725370039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 160680521142423140807894165 7531899428551084725370039)
  ·
    refine ⟨11297849142826627088055059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7531899428551084725370039 11297849142826627088055059)
    ·
      refine ⟨16946773714239940632082589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11297849142826627088055059 16946773714239940632082589)
      ·
        refine ⟨6355040142839977737030971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16946773714239940632082589 6355040142839977737030971)
        ·
          refine ⟨9532560214259966605546457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6355040142839977737030971 9532560214259966605546457)
          ·
            refine ⟨7149420160694974954159843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9532560214259966605546457 7149420160694974954159843)
            ·
              refine ⟨10724130241042462431239765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7149420160694974954159843 10724130241042462431239765)
              ·
                refine ⟨125673401262216356616091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10724130241042462431239765 125673401262216356616091)
                ·
                  rfl

theorem cell23_6608198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 8].length) (baseStart_6608198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608198 prefixEnd_6608198 := by exact prefixLift 6608198
  have htrace : WordTrace (prefixWord ++ tailWord_6608198) baseStart_6608198 baseEnd_6608198 := by
    simpa [prefixWord, tailWord_6608198, baseEnd_6608198] using wordTrace_append hprefix tailTrace_6608198
  have hstable : (prefixWord ++ tailWord_6608198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608198).length < 2 ^ (prefixWord ++ tailWord_6608198).sum := by decide
  have hdescent : baseEnd_6608198 < baseStart_6608198 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608247 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 3]
def baseStart_6608247 : Nat := 118140960795 + 6608247 * 2 ^ 59
def prefixEnd_6608247 : Nat := 4983230072969 + 3 ^ 40 * 6608247 * 2
def baseEnd_6608247 : Nat := 3393206994631911936921731

theorem tailTrace_6608247 : CollatzResearch.WordTrace tailWord_6608247 prefixEnd_6608247 3393206994631911936921731 := by
  unfold tailWord_6608247
  simp only [CollatzResearch.WordTrace]
  refine ⟨241022568890457192580374995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160681712593638128386916663 241022568890457192580374995)
  ·
    refine ⟨361533853335685788870562493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241022568890457192580374995 361533853335685788870562493)
    ·
      refine ⟨135575195000882170826460935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361533853335685788870562493 135575195000882170826460935)
      ·
        refine ⟨203362792501323256239691403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135575195000882170826460935 203362792501323256239691403)
        ·
          refine ⟨305044188751984884359537105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203362792501323256239691403 305044188751984884359537105)
          ·
            refine ⟨228783141563988663269652829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305044188751984884359537105 228783141563988663269652829)
            ·
              refine ⟨85793678086495748726119811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228783141563988663269652829 85793678086495748726119811)
              ·
                refine ⟨128690517129743623089179717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85793678086495748726119811 128690517129743623089179717)
                ·
                  refine ⟨24129471961826929329221197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128690517129743623089179717 24129471961826929329221197)
                  ·
                    refine ⟨9048551985685098498457949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24129471961826929329221197 9048551985685098498457949)
                    ·
                      refine ⟨3393206994631911936921731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9048551985685098498457949 3393206994631911936921731)
                      ·
                        rfl

theorem cell23_6608247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 3].length) (baseStart_6608247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608247 prefixEnd_6608247 := by exact prefixLift 6608247
  have htrace : WordTrace (prefixWord ++ tailWord_6608247) baseStart_6608247 baseEnd_6608247 := by
    simpa [prefixWord, tailWord_6608247, baseEnd_6608247] using wordTrace_append hprefix tailTrace_6608247
  have hstable : (prefixWord ++ tailWord_6608247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608247).length < 2 ^ (prefixWord ++ tailWord_6608247).sum := by decide
  have hdescent : baseEnd_6608247 < baseStart_6608247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608264 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_6608264 : Nat := 118140960795 + 6608264 * 2 ^ 59
def prefixEnd_6608264 : Nat := 4983230072969 + 3 ^ 40 * 6608264 * 2
def baseEnd_6608264 : Nat := 3393215723803038370409153

theorem tailTrace_6608264 : CollatzResearch.WordTrace tailWord_6608264 prefixEnd_6608264 3393215723803038370409153 := by
  unfold tailWord_6608264
  simp only [CollatzResearch.WordTrace]
  refine ⟨120511594465697802241871923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160682125954263736322495897 120511594465697802241871923)
  ·
    refine ⟨180767391698546703362807885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120511594465697802241871923 180767391698546703362807885)
    ·
      refine ⟨67787771886955013761052957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180767391698546703362807885 67787771886955013761052957)
      ·
        refine ⟨25420414457608130160394859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67787771886955013761052957 25420414457608130160394859)
        ·
          refine ⟨38130621686412195240592289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25420414457608130160394859 38130621686412195240592289)
          ·
            refine ⟨28597966264809146430444217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38130621686412195240592289 28597966264809146430444217)
            ·
              refine ⟨21448474698606859822833163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28597966264809146430444217 21448474698606859822833163)
              ·
                refine ⟨32172712047910289734249745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21448474698606859822833163 32172712047910289734249745)
                ·
                  refine ⟨24129534035932717300687309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32172712047910289734249745 24129534035932717300687309)
                  ·
                    refine ⟨9048575263474768987757741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24129534035932717300687309 9048575263474768987757741)
                    ·
                      refine ⟨3393215723803038370409153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9048575263474768987757741 3393215723803038370409153)
                      ·
                        rfl

theorem cell23_6608264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_6608264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608264 prefixEnd_6608264 := by exact prefixLift 6608264
  have htrace : WordTrace (prefixWord ++ tailWord_6608264) baseStart_6608264 baseEnd_6608264 := by
    simpa [prefixWord, tailWord_6608264, baseEnd_6608264] using wordTrace_append hprefix tailTrace_6608264
  have hstable : (prefixWord ++ tailWord_6608264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608264).length < 2 ^ (prefixWord ++ tailWord_6608264).sum := by decide
  have hdescent : baseEnd_6608264 < baseStart_6608264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608265 : List Nat := [1, 2, 1, 1, 7, 1, 3, 1, 2, 2, 2]
def baseStart_6608265 : Nat := 118140960795 + 6608265 * 2 ^ 59
def prefixEnd_6608265 : Nat := 4983230072969 + 3 ^ 40 * 6608265 * 2
def baseEnd_6608265 : Nat := 3393216237283692866496649

theorem tailTrace_6608265 : CollatzResearch.WordTrace tailWord_6608265 prefixEnd_6608265 3393216237283692866496649 := by
  unfold tailWord_6608265
  simp only [CollatzResearch.WordTrace]
  refine ⟨241023225404391981654530249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160682150269594654436353499 241023225404391981654530249)
  ·
    refine ⟨180767419053293986240897687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241023225404391981654530249 180767419053293986240897687)
    ·
      refine ⟨271151128579940979361346531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180767419053293986240897687 271151128579940979361346531)
      ·
        refine ⟨406726692869911469042019797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271151128579940979361346531 406726692869911469042019797)
        ·
          refine ⟨9532656864138550055672339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 406726692869911469042019797 9532656864138550055672339)
          ·
            refine ⟨14298985296207825083508509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9532656864138550055672339 14298985296207825083508509)
            ·
              refine ⟨5362119486077934406315691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14298985296207825083508509 5362119486077934406315691)
              ·
                refine ⟨8043179229116901609473537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5362119486077934406315691 8043179229116901609473537)
                ·
                  refine ⟨6032384421837676207105153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8043179229116901609473537 6032384421837676207105153)
                  ·
                    refine ⟨4524288316378257155328865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6032384421837676207105153 4524288316378257155328865)
                    ·
                      refine ⟨3393216237283692866496649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524288316378257155328865 3393216237283692866496649)
                      ·
                        rfl

theorem cell23_6608265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 1, 2, 2, 2].length) (baseStart_6608265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608265 prefixEnd_6608265 := by exact prefixLift 6608265
  have htrace : WordTrace (prefixWord ++ tailWord_6608265) baseStart_6608265 baseEnd_6608265 := by
    simpa [prefixWord, tailWord_6608265, baseEnd_6608265] using wordTrace_append hprefix tailTrace_6608265
  have hstable : (prefixWord ++ tailWord_6608265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608265).length < 2 ^ (prefixWord ++ tailWord_6608265).sum := by decide
  have hdescent : baseEnd_6608265 < baseStart_6608265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608301 : List Nat := [1, 5, 2, 2, 1, 2, 1, 2, 2, 5]
def baseStart_6608301 : Nat := 118140960795 + 6608301 * 2 ^ 59
def prefixEnd_6608301 : Nat := 4983230072969 + 3 ^ 40 * 6608301 * 2
def baseEnd_6608301 : Nat := 1131078240862418241882161

theorem tailTrace_6608301 : CollatzResearch.WordTrace tailWord_6608301 prefixEnd_6608301 1131078240862418241882161 := by
  unfold tailWord_6608301
  simp only [CollatzResearch.WordTrace]
  refine ⟨241024538432261559802840757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160683025621507706535227171 241024538432261559802840757)
  ·
    refine ⟨22596050478024521231516321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241024538432261559802840757 22596050478024521231516321)
    ·
      refine ⟨16947037858518390923637241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22596050478024521231516321 16947037858518390923637241)
      ·
        refine ⟨12710278393888793192727931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16947037858518390923637241 12710278393888793192727931)
        ·
          refine ⟨19065417590833189789091897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12710278393888793192727931 19065417590833189789091897)
          ·
            refine ⟨14299063193124892341818923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19065417590833189789091897 14299063193124892341818923)
            ·
              refine ⟨21448594789687338512728385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14299063193124892341818923 21448594789687338512728385)
              ·
                refine ⟨16086446092265503884546289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21448594789687338512728385 16086446092265503884546289)
                ·
                  refine ⟨12064834569199127913409717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16086446092265503884546289 12064834569199127913409717)
                  ·
                    refine ⟨1131078240862418241882161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12064834569199127913409717 1131078240862418241882161)
                    ·
                      rfl

theorem cell23_6608301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_6608301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608301 prefixEnd_6608301 := by exact prefixLift 6608301
  have htrace : WordTrace (prefixWord ++ tailWord_6608301) baseStart_6608301 baseEnd_6608301 := by
    simpa [prefixWord, tailWord_6608301, baseEnd_6608301] using wordTrace_append hprefix tailTrace_6608301
  have hstable : (prefixWord ++ tailWord_6608301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608301).length < 2 ^ (prefixWord ++ tailWord_6608301).sum := by decide
  have hdescent : baseEnd_6608301 < baseStart_6608301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608304 : List Nat := [2, 1, 1, 1, 2, 1, 1, 6, 2, 4, 2]
def baseStart_6608304 : Nat := 118140960795 + 6608304 * 2 ^ 59
def prefixEnd_6608304 : Nat := 4983230072969 + 3 ^ 40 * 6608304 * 2
def baseEnd_6608304 : Nat := 3393236263029218213908969

theorem tailTrace_6608304 : CollatzResearch.WordTrace tailWord_6608304 prefixEnd_6608304 3393236263029218213908969 := by
  unfold tailWord_6608304
  simp only [CollatzResearch.WordTrace]
  refine ⟨120512323925625345657599983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160683098567500460876799977 120512323925625345657599983)
  ·
    refine ⟨180768485888438018486399975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120512323925625345657599983 180768485888438018486399975)
    ·
      refine ⟨271152728832657027729599963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180768485888438018486399975 271152728832657027729599963)
      ·
        refine ⟨406729093248985541594399945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271152728832657027729599963 406729093248985541594399945)
        ·
          refine ⟨305046819936739156195799959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406729093248985541594399945 305046819936739156195799959)
          ·
            refine ⟨457570229905108734293699939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305046819936739156195799959 457570229905108734293699939)
            ·
              refine ⟨686355344857663101440549909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457570229905108734293699939 686355344857663101440549909)
              ·
                refine ⟨32172906790202957880025777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 686355344857663101440549909 32172906790202957880025777)
                ·
                  refine ⟨24129680092652218410019333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32172906790202957880025777 24129680092652218410019333)
                  ·
                    refine ⟨4524315017372290951878625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24129680092652218410019333 4524315017372290951878625)
                    ·
                      refine ⟨3393236263029218213908969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524315017372290951878625 3393236263029218213908969)
                      ·
                        rfl

theorem cell23_6608304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 2, 4, 2].length) (baseStart_6608304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608304 prefixEnd_6608304 := by exact prefixLift 6608304
  have htrace : WordTrace (prefixWord ++ tailWord_6608304) baseStart_6608304 baseEnd_6608304 := by
    simpa [prefixWord, tailWord_6608304, baseEnd_6608304] using wordTrace_append hprefix tailTrace_6608304
  have hstable : (prefixWord ++ tailWord_6608304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608304).length < 2 ^ (prefixWord ++ tailWord_6608304).sum := by decide
  have hdescent : baseEnd_6608304 < baseStart_6608304 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608341 : List Nat := [1, 3, 2, 3, 1, 1, 4, 1, 2, 2, 3]
def baseStart_6608341 : Nat := 118140960795 + 6608341 * 2 ^ 59
def prefixEnd_6608341 : Nat := 4983230072969 + 3 ^ 40 * 6608341 * 2
def baseEnd_6608341 : Nat := 3393255261813434569146299

theorem tailTrace_6608341 : CollatzResearch.WordTrace tailWord_6608341 prefixEnd_6608341 3393255261813434569146299 := by
  unfold tailWord_6608341
  simp only [CollatzResearch.WordTrace]
  refine ⟨241025997352116646634296877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160683998234744431089531251 241025997352116646634296877)
  ·
    refine ⟨90384749007043742487861329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241025997352116646634296877 90384749007043742487861329)
    ·
      refine ⟨67788561755282806865895997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90384749007043742487861329 67788561755282806865895997)
      ·
        refine ⟨25420710658231052574710999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67788561755282806865895997 25420710658231052574710999)
        ·
          refine ⟨38131065987346578862066499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25420710658231052574710999 38131065987346578862066499)
          ·
            refine ⟨57196598981019868293099749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38131065987346578862066499 57196598981019868293099749)
            ·
              refine ⟨10724362308941225304956203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57196598981019868293099749 10724362308941225304956203)
              ·
                refine ⟨16086543463411837957434305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10724362308941225304956203 16086543463411837957434305)
                ·
                  refine ⟨12064907597558878468075729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16086543463411837957434305 12064907597558878468075729)
                  ·
                    refine ⟨9048680698169158851056797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12064907597558878468075729 9048680698169158851056797)
                    ·
                      refine ⟨3393255261813434569146299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9048680698169158851056797 3393255261813434569146299)
                      ·
                        rfl

theorem cell23_6608341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_6608341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608341 prefixEnd_6608341 := by exact prefixLift 6608341
  have htrace : WordTrace (prefixWord ++ tailWord_6608341) baseStart_6608341 baseEnd_6608341 := by
    simpa [prefixWord, tailWord_6608341, baseEnd_6608341] using wordTrace_append hprefix tailTrace_6608341
  have hstable : (prefixWord ++ tailWord_6608341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608341).length < 2 ^ (prefixWord ++ tailWord_6608341).sum := by decide
  have hdescent : baseEnd_6608341 < baseStart_6608341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608365 : List Nat := [1, 5, 1, 3, 2, 1, 1, 4, 1, 4]
def baseStart_6608365 : Nat := 118140960795 + 6608365 * 2 ^ 59
def prefixEnd_6608365 : Nat := 4983230072969 + 3 ^ 40 * 6608365 * 2
def baseEnd_6608365 : Nat := 1131089195116380825082063

theorem tailTrace_6608365 : CollatzResearch.WordTrace tailWord_6608365 prefixEnd_6608365 1131089195116380825082063 := by
  unfold tailWord_6608365
  simp only [CollatzResearch.WordTrace]
  refine ⟨241026872704029698733170549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160684581802686465822113699 241026872704029698733170549)
  ·
    refine ⟨22596269316002784256234739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241026872704029698733170549 22596269316002784256234739)
    ·
      refine ⟨33894403974004176384352109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22596269316002784256234739 33894403974004176384352109)
      ·
        refine ⟨12710401490251566144132041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33894403974004176384352109 12710401490251566144132041)
        ·
          refine ⟨9532801117688674608099031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12710401490251566144132041 9532801117688674608099031)
          ·
            refine ⟨14299201676533011912148547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9532801117688674608099031 14299201676533011912148547)
            ·
              refine ⟨21448802514799517868222821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14299201676533011912148547 21448802514799517868222821)
              ·
                refine ⟨4021650471524909600291779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21448802514799517868222821 4021650471524909600291779)
                ·
                  refine ⟨6032475707287364400437669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4021650471524909600291779 6032475707287364400437669)
                  ·
                    refine ⟨1131089195116380825082063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6032475707287364400437669 1131089195116380825082063)
                    ·
                      rfl

theorem cell23_6608365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 4, 1, 4].length) (baseStart_6608365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608365 prefixEnd_6608365 := by exact prefixLift 6608365
  have htrace : WordTrace (prefixWord ++ tailWord_6608365) baseStart_6608365 baseEnd_6608365 := by
    simpa [prefixWord, tailWord_6608365, baseEnd_6608365] using wordTrace_append hprefix tailTrace_6608365
  have hstable : (prefixWord ++ tailWord_6608365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608365).length < 2 ^ (prefixWord ++ tailWord_6608365).sum := by decide
  have hdescent : baseEnd_6608365 < baseStart_6608365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608398 : List Nat := [4, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2]
def baseStart_6608398 : Nat := 118140960795 + 6608398 * 2 ^ 59
def prefixEnd_6608398 : Nat := 4983230072969 + 3 ^ 40 * 6608398 * 2
def baseEnd_6608398 : Nat := 3393284530210740846133537

theorem tailTrace_6608398 : CollatzResearch.WordTrace tailWord_6608398 prefixEnd_6608398 3393284530210740846133537 := by
  unfold tailWord_6608398
  simp only [CollatzResearch.WordTrace]
  refine ⟨30128509539113768171140231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160685384208606763579414565 30128509539113768171140231)
  ·
    refine ⟨45192764308670652256710347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30128509539113768171140231 45192764308670652256710347)
    ·
      refine ⟨67789146463005978385065521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45192764308670652256710347 67789146463005978385065521)
      ·
        refine ⟨50841859847254483788799141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67789146463005978385065521 50841859847254483788799141)
        ·
          refine ⟨9532848721360215710399839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50841859847254483788799141 9532848721360215710399839)
          ·
            refine ⟨14299273082040323565599759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9532848721360215710399839 14299273082040323565599759)
            ·
              refine ⟨21448909623060485348399639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14299273082040323565599759 21448909623060485348399639)
              ·
                refine ⟨32173364434590728022599459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21448909623060485348399639 32173364434590728022599459)
                ·
                  refine ⟨48260046651886092033899189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32173364434590728022599459 48260046651886092033899189)
                  ·
                    refine ⟨4524379373614321128178049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48260046651886092033899189 4524379373614321128178049)
                    ·
                      refine ⟨3393284530210740846133537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524379373614321128178049 3393284530210740846133537)
                      ·
                        rfl

theorem cell23_6608398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_6608398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608398 prefixEnd_6608398 := by exact prefixLift 6608398
  have htrace : WordTrace (prefixWord ++ tailWord_6608398) baseStart_6608398 baseEnd_6608398 := by
    simpa [prefixWord, tailWord_6608398, baseEnd_6608398] using wordTrace_append hprefix tailTrace_6608398
  have hstable : (prefixWord ++ tailWord_6608398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608398).length < 2 ^ (prefixWord ++ tailWord_6608398).sum := by decide
  have hdescent : baseEnd_6608398 < baseStart_6608398 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608405 : List Nat := [1, 3, 2, 1, 3, 3, 2, 3, 1, 1, 3]
def baseStart_6608405 : Nat := 118140960795 + 6608405 * 2 ^ 59
def prefixEnd_6608405 : Nat := 4983230072969 + 3 ^ 40 * 6608405 * 2
def baseEnd_6608405 : Nat := 3393288124575322318746005

theorem tailTrace_6608405 : CollatzResearch.WordTrace tailWord_6608405 prefixEnd_6608405 3393288124575322318746005 := by
  unfold tailWord_6608405
  simp only [CollatzResearch.WordTrace]
  refine ⟨241028331623884785564626669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160685554415923190376417779 241028331623884785564626669)
  ·
    refine ⟨90385624358956794586735001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241028331623884785564626669 90385624358956794586735001)
    ·
      refine ⟨67789218269217595940051251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90385624358956794586735001 67789218269217595940051251)
      ·
        refine ⟨101683827403826393910076877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67789218269217595940051251 101683827403826393910076877)
        ·
          refine ⟨38131435276434897716278829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101683827403826393910076877 38131435276434897716278829)
          ·
            refine ⟨14299288228663086643604561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38131435276434897716278829 14299288228663086643604561)
            ·
              refine ⟨10724466171497314982703421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14299288228663086643604561 10724466171497314982703421)
              ·
                refine ⟨4021674814311493118513783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10724466171497314982703421 4021674814311493118513783)
                ·
                  refine ⟨6032512221467239677770675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4021674814311493118513783 6032512221467239677770675)
                  ·
                    refine ⟨9048768332200859516656013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6032512221467239677770675 9048768332200859516656013)
                    ·
                      refine ⟨3393288124575322318746005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9048768332200859516656013 3393288124575322318746005)
                      ·
                        rfl

theorem cell23_6608405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 3, 1, 1, 3].length) (baseStart_6608405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608405 prefixEnd_6608405 := by exact prefixLift 6608405
  have htrace : WordTrace (prefixWord ++ tailWord_6608405) baseStart_6608405 baseEnd_6608405 := by
    simpa [prefixWord, tailWord_6608405, baseEnd_6608405] using wordTrace_append hprefix tailTrace_6608405
  have hstable : (prefixWord ++ tailWord_6608405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608405).length < 2 ^ (prefixWord ++ tailWord_6608405).sum := by decide
  have hdescent : baseEnd_6608405 < baseStart_6608405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608427 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 7]
def baseStart_6608427 : Nat := 118140960795 + 6608427 * 2 ^ 59
def prefixEnd_6608427 : Nat := 4983230072969 + 3 ^ 40 * 6608427 * 2
def baseEnd_6608427 : Nat := 3393299421149721232670903

theorem tailTrace_6608427 : CollatzResearch.WordTrace tailWord_6608427 prefixEnd_6608427 3393299421149721232670903 := by
  unfold tailWord_6608427
  simp only [CollatzResearch.WordTrace]
  refine ⟨241029134029805083321927535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160686089353203388881285023 241029134029805083321927535)
  ·
    refine ⟨361543701044707624982891303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241029134029805083321927535 361543701044707624982891303)
    ·
      refine ⟨542315551567061437474336955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361543701044707624982891303 542315551567061437474336955)
      ·
        refine ⟨813473327350592156211505433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542315551567061437474336955 813473327350592156211505433)
        ·
          refine ⟨610104995512944117158629075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 813473327350592156211505433 610104995512944117158629075)
          ·
            refine ⟨915157493269416175737943613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 610104995512944117158629075 915157493269416175737943613)
            ·
              refine ⟨343184059976031065901728855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 915157493269416175737943613 343184059976031065901728855)
              ·
                refine ⟨514776089964046598852593283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 343184059976031065901728855 514776089964046598852593283)
                ·
                  refine ⟨772164134946069898278889925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 514776089964046598852593283 772164134946069898278889925)
                  ·
                    refine ⟨144780775302388105927291861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 772164134946069898278889925 144780775302388105927291861)
                    ·
                      refine ⟨3393299421149721232670903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144780775302388105927291861 3393299421149721232670903)
                      ·
                        rfl

theorem cell23_6608427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 7].length) (baseStart_6608427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608427 prefixEnd_6608427 := by exact prefixLift 6608427
  have htrace : WordTrace (prefixWord ++ tailWord_6608427) baseStart_6608427 baseEnd_6608427 := by
    simpa [prefixWord, tailWord_6608427, baseEnd_6608427] using wordTrace_append hprefix tailTrace_6608427
  have hstable : (prefixWord ++ tailWord_6608427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608427).length < 2 ^ (prefixWord ++ tailWord_6608427).sum := by decide
  have hdescent : baseEnd_6608427 < baseStart_6608427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608441 : List Nat := [1, 2, 1, 5, 1, 2, 3, 1, 1, 2, 4]
def baseStart_6608441 : Nat := 118140960795 + 6608441 * 2 ^ 59
def prefixEnd_6608441 : Nat := 4983230072969 + 3 ^ 40 * 6608441 * 2
def baseEnd_6608441 : Nat := 3393306609878884177895839

theorem tailTrace_6608441 : CollatzResearch.WordTrace tailWord_6608441 prefixEnd_6608441 3393306609878884177895839 := by
  unfold tailWord_6608441
  simp only [CollatzResearch.WordTrace]
  refine ⟨241029644651754363712937177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160686429767836242475291451 241029644651754363712937177)
  ·
    refine ⟨180772233488815772784702883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241029644651754363712937177 180772233488815772784702883)
    ·
      refine ⟨271158350233223659177054325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180772233488815772784702883 271158350233223659177054325)
      ·
        refine ⟨25421095334364718047848843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 271158350233223659177054325 25421095334364718047848843)
        ·
          refine ⟨38131643001547077071773265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25421095334364718047848843 38131643001547077071773265)
          ·
            refine ⟨28598732251160307803829949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38131643001547077071773265 28598732251160307803829949)
            ·
              refine ⟨10724524594185115426436231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28598732251160307803829949 10724524594185115426436231)
              ·
                refine ⟨16086786891277673139654347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10724524594185115426436231 16086786891277673139654347)
                ·
                  refine ⟨24130180336916509709481521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16086786891277673139654347 24130180336916509709481521)
                  ·
                    refine ⟨18097635252687382282111141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24130180336916509709481521 18097635252687382282111141)
                    ·
                      refine ⟨3393306609878884177895839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18097635252687382282111141 3393306609878884177895839)
                      ·
                        rfl

theorem cell23_6608441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_6608441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608441 prefixEnd_6608441 := by exact prefixLift 6608441
  have htrace : WordTrace (prefixWord ++ tailWord_6608441) baseStart_6608441 baseEnd_6608441 := by
    simpa [prefixWord, tailWord_6608441, baseEnd_6608441] using wordTrace_append hprefix tailTrace_6608441
  have hstable : (prefixWord ++ tailWord_6608441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608441).length < 2 ^ (prefixWord ++ tailWord_6608441).sum := by decide
  have hdescent : baseEnd_6608441 < baseStart_6608441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608522 : List Nat := [3, 1, 2, 3, 2, 2, 3, 1, 1, 3, 2]
def baseStart_6608522 : Nat := 118140960795 + 6608522 * 2 ^ 59
def prefixEnd_6608522 : Nat := 4983230072969 + 3 ^ 40 * 6608522 * 2
def baseEnd_6608522 : Nat := 3393348201811898360982967

theorem tailTrace_6608522 : CollatzResearch.WordTrace tailWord_6608522 prefixEnd_6608522 3393348201811898360982967 := by
  unfold tailWord_6608522
  simp only [CollatzResearch.WordTrace]
  refine ⟨60258149741115228636658955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160688399309640609697757213 60258149741115228636658955)
  ·
    refine ⟨90387224611672842954988433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60258149741115228636658955 90387224611672842954988433)
    ·
      refine ⟨67790418458754632216241325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90387224611672842954988433 67790418458754632216241325)
      ·
        refine ⟨25421406922032987081090497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67790418458754632216241325 25421406922032987081090497)
        ·
          refine ⟨19066055191524740310817873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25421406922032987081090497 19066055191524740310817873)
          ·
            refine ⟨14299541393643555233113405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19066055191524740310817873 14299541393643555233113405)
            ·
              refine ⟨5362328022616333212417527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14299541393643555233113405 5362328022616333212417527)
              ·
                refine ⟨8043492033924499818626291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5362328022616333212417527 8043492033924499818626291)
                ·
                  refine ⟨12065238050886749727939437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8043492033924499818626291 12065238050886749727939437)
                  ·
                    refine ⟨4524464269082531147977289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12065238050886749727939437 4524464269082531147977289)
                    ·
                      refine ⟨3393348201811898360982967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524464269082531147977289 3393348201811898360982967)
                      ·
                        rfl

theorem cell23_6608522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_6608522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608522 prefixEnd_6608522 := by exact prefixLift 6608522
  have htrace : WordTrace (prefixWord ++ tailWord_6608522) baseStart_6608522 baseEnd_6608522 := by
    simpa [prefixWord, tailWord_6608522, baseEnd_6608522] using wordTrace_append hprefix tailTrace_6608522
  have hstable : (prefixWord ++ tailWord_6608522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608522).length < 2 ^ (prefixWord ++ tailWord_6608522).sum := by decide
  have hdescent : baseEnd_6608522 < baseStart_6608522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608535 : List Nat := [1, 1, 3, 3, 2, 2, 1, 4, 2, 2, 2]
def baseStart_6608535 : Nat := 118140960795 + 6608535 * 2 ^ 59
def prefixEnd_6608535 : Nat := 4983230072969 + 3 ^ 40 * 6608535 * 2
def baseEnd_6608535 : Nat := 3393354877060406810120407

theorem tailTrace_6608535 : CollatzResearch.WordTrace tailWord_6608535 prefixEnd_6608535 3393354877060406810120407 := by
  unfold tailWord_6608535
  simp only [CollatzResearch.WordTrace]
  refine ⟨241033073113413817766859059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160688715408942545177906039 241033073113413817766859059)
  ·
    refine ⟨361549609670120726650288589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241033073113413817766859059 361549609670120726650288589)
    ·
      refine ⟨135581103626295272493858221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361549609670120726650288589 135581103626295272493858221)
      ·
        refine ⟨50842913859860727185196833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135581103626295272493858221 50842913859860727185196833)
        ·
          refine ⟨38132185394895545388897625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50842913859860727185196833 38132185394895545388897625)
          ·
            refine ⟨28599139046171659041673219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38132185394895545388897625 28599139046171659041673219)
            ·
              refine ⟨42898708569257488562509829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28599139046171659041673219 42898708569257488562509829)
              ·
                refine ⟨8043507856735779105470593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42898708569257488562509829 8043507856735779105470593)
                ·
                  refine ⟨6032630892551834329102945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8043507856735779105470593 6032630892551834329102945)
                  ·
                    refine ⟨4524473169413875746827209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6032630892551834329102945 4524473169413875746827209)
                    ·
                      refine ⟨3393354877060406810120407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524473169413875746827209 3393354877060406810120407)
                      ·
                        rfl

theorem cell23_6608535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 4, 2, 2, 2].length) (baseStart_6608535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608535 prefixEnd_6608535 := by exact prefixLift 6608535
  have htrace : WordTrace (prefixWord ++ tailWord_6608535) baseStart_6608535 baseEnd_6608535 := by
    simpa [prefixWord, tailWord_6608535, baseEnd_6608535] using wordTrace_append hprefix tailTrace_6608535
  have hstable : (prefixWord ++ tailWord_6608535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608535).length < 2 ^ (prefixWord ++ tailWord_6608535).sum := by decide
  have hdescent : baseEnd_6608535 < baseStart_6608535 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608591 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 4]
def baseStart_6608591 : Nat := 118140960795 + 6608591 * 2 ^ 59
def prefixEnd_6608591 : Nat := 4983230072969 + 3 ^ 40 * 6608591 * 2
def baseEnd_6608591 : Nat := 3393383631977058591020149

theorem tailTrace_6608591 : CollatzResearch.WordTrace tailWord_6608591 prefixEnd_6608591 3393383631977058591020149 := by
  unfold tailWord_6608591
  simp only [CollatzResearch.WordTrace]
  refine ⟨241035115601210939330897627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160690077067473959553931751 241035115601210939330897627)
  ·
    refine ⟨361552673401816408996346441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241035115601210939330897627 361552673401816408996346441)
    ·
      refine ⟨271164505051362306747259831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361552673401816408996346441 271164505051362306747259831)
      ·
        refine ⟨406746757577043460120889747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271164505051362306747259831 406746757577043460120889747)
        ·
          refine ⟨610120136365565190181334621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406746757577043460120889747 610120136365565190181334621)
          ·
            refine ⟨228795051137086946318000483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 610120136365565190181334621 228795051137086946318000483)
            ·
              refine ⟨343192576705630419477000725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228795051137086946318000483 343192576705630419477000725)
              ·
                refine ⟨16087152033076425912984409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 343192576705630419477000725 16087152033076425912984409)
                ·
                  refine ⟨12065364024807319434738307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16087152033076425912984409 12065364024807319434738307)
                  ·
                    refine ⟨18098046037210979152107461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12065364024807319434738307 18098046037210979152107461)
                    ·
                      refine ⟨3393383631977058591020149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18098046037210979152107461 3393383631977058591020149)
                      ·
                        rfl

theorem cell23_6608591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 2, 1, 4].length) (baseStart_6608591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608591 prefixEnd_6608591 := by exact prefixLift 6608591
  have htrace : WordTrace (prefixWord ++ tailWord_6608591) baseStart_6608591 baseEnd_6608591 := by
    simpa [prefixWord, tailWord_6608591, baseEnd_6608591] using wordTrace_append hprefix tailTrace_6608591
  have hstable : (prefixWord ++ tailWord_6608591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608591).length < 2 ^ (prefixWord ++ tailWord_6608591).sum := by decide
  have hdescent : baseEnd_6608591 < baseStart_6608591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608608 : List Nat := [2, 1, 1, 3, 1, 2, 4, 1, 2, 4, 2]
def baseStart_6608608 : Nat := 118140960795 + 6608608 * 2 ^ 59
def prefixEnd_6608608 : Nat := 4983230072969 + 3 ^ 40 * 6608608 * 2
def baseEnd_6608608 : Nat := 3393392361148185024507571

theorem tailTrace_6608608 : CollatzResearch.WordTrace tailWord_6608608 prefixEnd_6608608 3393392361148185024507571 := by
  unfold tailWord_6608608
  simp only [CollatzResearch.WordTrace]
  refine ⟨120517867821074675617133239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160690490428099567489510985 120517867821074675617133239)
  ·
    refine ⟨180776801731612013425699859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120517867821074675617133239 180776801731612013425699859)
    ·
      refine ⟨271165202597418020138549789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180776801731612013425699859 271165202597418020138549789)
      ·
        refine ⟨101686950974031757551956171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271165202597418020138549789 101686950974031757551956171)
        ·
          refine ⟨152530426461047636327934257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101686950974031757551956171 152530426461047636327934257)
          ·
            refine ⟨114397819845785727245950693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152530426461047636327934257 114397819845785727245950693)
            ·
              refine ⟨21449591221084823858615755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114397819845785727245950693 21449591221084823858615755)
              ·
                refine ⟨32174386831627235787923633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21449591221084823858615755 32174386831627235787923633)
                ·
                  refine ⟨24130790123720426840942725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32174386831627235787923633 24130790123720426840942725)
                  ·
                    refine ⟨4524523148197580032676761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24130790123720426840942725 4524523148197580032676761)
                    ·
                      refine ⟨3393392361148185024507571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524523148197580032676761 3393392361148185024507571)
                      ·
                        rfl

theorem cell23_6608608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 2, 4, 2].length) (baseStart_6608608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608608 prefixEnd_6608608 := by exact prefixLift 6608608
  have htrace : WordTrace (prefixWord ++ tailWord_6608608) baseStart_6608608 baseEnd_6608608 := by
    simpa [prefixWord, tailWord_6608608, baseEnd_6608608] using wordTrace_append hprefix tailTrace_6608608
  have hstable : (prefixWord ++ tailWord_6608608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608608).length < 2 ^ (prefixWord ++ tailWord_6608608).sum := by decide
  have hdescent : baseEnd_6608608 < baseStart_6608608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608618 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 3, 4]
def baseStart_6608618 : Nat := 118140960795 + 6608618 * 2 ^ 59
def prefixEnd_6608618 : Nat := 4983230072969 + 3 ^ 40 * 6608618 * 2
def baseEnd_6608618 : Nat := 1131132498651576661794175

theorem tailTrace_6608618 : CollatzResearch.WordTrace tailWord_6608618 prefixEnd_6608618 1131132498651576661794175 := by
  unfold tailWord_6608618
  simp only [CollatzResearch.WordTrace]
  refine ⟨60259025093028280735532627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160690733581408748628087005 60259025093028280735532627)
  ·
    refine ⟨90388537639542421103298941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60259025093028280735532627 90388537639542421103298941)
    ·
      refine ⟨33895701614828407913737103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90388537639542421103298941 33895701614828407913737103)
      ·
        refine ⟨50843552422242611870605655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33895701614828407913737103 50843552422242611870605655)
        ·
          refine ⟨76265328633363917805908483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50843552422242611870605655 76265328633363917805908483)
          ·
            refine ⟨114397992950045876708862725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76265328633363917805908483 114397992950045876708862725)
            ·
              refine ⟨21449623678133601882911761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114397992950045876708862725 21449623678133601882911761)
              ·
                refine ⟨16087217758600201412183821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21449623678133601882911761 16087217758600201412183821)
                ·
                  refine ⟨6032706659475075529568933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16087217758600201412183821 6032706659475075529568933)
                  ·
                    refine ⟨1131132498651576661794175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6032706659475075529568933 1131132498651576661794175)
                    ·
                      rfl

theorem cell23_6608618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_6608618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608618 prefixEnd_6608618 := by exact prefixLift 6608618
  have htrace : WordTrace (prefixWord ++ tailWord_6608618) baseStart_6608618 baseEnd_6608618 := by
    simpa [prefixWord, tailWord_6608618, baseEnd_6608618] using wordTrace_append hprefix tailTrace_6608618
  have hstable : (prefixWord ++ tailWord_6608618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608618).length < 2 ^ (prefixWord ++ tailWord_6608618).sum := by decide
  have hdescent : baseEnd_6608618 < baseStart_6608618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608702 : List Nat := [4, 2, 1, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_6608702 : Nat := 118140960795 + 6608702 * 2 ^ 59
def prefixEnd_6608702 : Nat := 4983230072969 + 3 ^ 40 * 6608702 * 2
def baseEnd_6608702 : Nat := 3393440628329707656732139

theorem tailTrace_6608702 : CollatzResearch.WordTrace tailWord_6608702 prefixEnd_6608702 3393440628329707656732139 := by
  unfold tailWord_6608702
  simp only [CollatzResearch.WordTrace]
  refine ⟨30129895512976100661023545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160692776069205870192125573 30129895512976100661023545)
  ·
    refine ⟨22597421634732075495767659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30129895512976100661023545 22597421634732075495767659)
    ·
      refine ⟨33896132452098113243651489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22597421634732075495767659 33896132452098113243651489)
      ·
        refine ⟨25422099339073584932738617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33896132452098113243651489 25422099339073584932738617)
        ·
          refine ⟨19066574504305188699553963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25422099339073584932738617 19066574504305188699553963)
          ·
            refine ⟨28599861756457783049330945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19066574504305188699553963 28599861756457783049330945)
            ·
              refine ⟨21449896317343337286998209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28599861756457783049330945 21449896317343337286998209)
              ·
                refine ⟨16087422238007502965248657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21449896317343337286998209 16087422238007502965248657)
                ·
                  refine ⟨12065566678505627223936493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16087422238007502965248657 12065566678505627223936493)
                  ·
                    refine ⟨4524587504439610208976185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12065566678505627223936493 4524587504439610208976185)
                    ·
                      refine ⟨3393440628329707656732139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524587504439610208976185 3393440628329707656732139)
                      ·
                        rfl

theorem cell23_6608702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_6608702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608702 prefixEnd_6608702 := by exact prefixLift 6608702
  have htrace : WordTrace (prefixWord ++ tailWord_6608702) baseStart_6608702 baseEnd_6608702 := by
    simpa [prefixWord, tailWord_6608702, baseEnd_6608702] using wordTrace_append hprefix tailTrace_6608702
  have hstable : (prefixWord ++ tailWord_6608702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608702).length < 2 ^ (prefixWord ++ tailWord_6608702).sum := by decide
  have hdescent : baseEnd_6608702 < baseStart_6608702 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608711 : List Nat := [1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 6]
def baseStart_6608711 : Nat := 118140960795 + 6608711 * 2 ^ 59
def prefixEnd_6608711 : Nat := 4983230072969 + 3 ^ 40 * 6608711 * 2
def baseEnd_6608711 : Nat := 3393445249655598121519597

theorem tailTrace_6608711 : CollatzResearch.WordTrace tailWord_6608711 prefixEnd_6608711 3393445249655598121519597 := by
  unfold tailWord_6608711
  simp only [CollatzResearch.WordTrace]
  refine ⟨241039492360776199825265987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160692994907184133216843991 241039492360776199825265987)
  ·
    refine ⟨361559238541164299737898981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241039492360776199825265987 361559238541164299737898981)
    ·
      refine ⟨67792357226468306200856059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361559238541164299737898981 67792357226468306200856059)
      ·
        refine ⟨101688535839702459301284089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67792357226468306200856059 101688535839702459301284089)
        ·
          refine ⟨76266401879776844475963067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101688535839702459301284089 76266401879776844475963067)
          ·
            refine ⟨114399602819665266713944601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76266401879776844475963067 114399602819665266713944601)
            ·
              refine ⟨85799702114748950035458451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114399602819665266713944601 85799702114748950035458451)
              ·
                refine ⟨128699553172123425053187677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85799702114748950035458451 128699553172123425053187677)
                ·
                  refine ⟨48262332439546284394945379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128699553172123425053187677 48262332439546284394945379)
                  ·
                    refine ⟨72393498659319426592418069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48262332439546284394945379 72393498659319426592418069)
                    ·
                      refine ⟨3393445249655598121519597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72393498659319426592418069 3393445249655598121519597)
                      ·
                        rfl

theorem cell23_6608711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_6608711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608711 prefixEnd_6608711 := by exact prefixLift 6608711
  have htrace : WordTrace (prefixWord ++ tailWord_6608711) baseStart_6608711 baseEnd_6608711 := by
    simpa [prefixWord, tailWord_6608711, baseEnd_6608711] using wordTrace_append hprefix tailTrace_6608711
  have hstable : (prefixWord ++ tailWord_6608711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608711).length < 2 ^ (prefixWord ++ tailWord_6608711).sum := by decide
  have hdescent : baseEnd_6608711 < baseStart_6608711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608725 : List Nat := [1, 3, 2, 2, 2, 2, 2, 3, 2, 4]
def baseStart_6608725 : Nat := 118140960795 + 6608725 * 2 ^ 59
def prefixEnd_6608725 : Nat := 4983230072969 + 3 ^ 40 * 6608725 * 2
def baseEnd_6608725 : Nat := 1131150812794920355581511

theorem tailTrace_6608725 : CollatzResearch.WordTrace tailWord_6608725 prefixEnd_6608725 1131150812794920355581511 := by
  unfold tailWord_6608725
  simp only [CollatzResearch.WordTrace]
  refine ⟨241040002982725480216275629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160693335321816986810850419 241040002982725480216275629)
  ·
    refine ⟨90390001118522055081103361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241040002982725480216275629 90390001118522055081103361)
    ·
      refine ⟨67792500838891541310827521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90390001118522055081103361 67792500838891541310827521)
      ·
        refine ⟨50844375629168655983120641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67792500838891541310827521 50844375629168655983120641)
        ·
          refine ⟨38133281721876491987340481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50844375629168655983120641 38133281721876491987340481)
          ·
            refine ⟨28599961291407368990505361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38133281721876491987340481 28599961291407368990505361)
            ·
              refine ⟨21449970968555526742879021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28599961291407368990505361 21449970968555526742879021)
              ·
                refine ⟨8043739113208322528579633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21449970968555526742879021 8043739113208322528579633)
                ·
                  refine ⟨6032804334906241896434725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8043739113208322528579633 6032804334906241896434725)
                  ·
                    refine ⟨1131150812794920355581511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6032804334906241896434725 1131150812794920355581511)
                    ·
                      rfl

theorem cell23_6608725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 2, 4].length) (baseStart_6608725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608725 prefixEnd_6608725 := by exact prefixLift 6608725
  have htrace : WordTrace (prefixWord ++ tailWord_6608725) baseStart_6608725 baseEnd_6608725 := by
    simpa [prefixWord, tailWord_6608725, baseEnd_6608725] using wordTrace_append hprefix tailTrace_6608725
  have hstable : (prefixWord ++ tailWord_6608725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608725).length < 2 ^ (prefixWord ++ tailWord_6608725).sum := by decide
  have hdescent : baseEnd_6608725 < baseStart_6608725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608746 : List Nat := [3, 1, 3, 4, 2, 1, 2, 1, 1, 5]
def baseStart_6608746 : Nat := 118140960795 + 6608746 * 2 ^ 59
def prefixEnd_6608746 : Nat := 4983230072969 + 3 ^ 40 * 6608746 * 2
def baseEnd_6608746 : Nat := 1131154407159501828193979

theorem tailTrace_6608746 : CollatzResearch.WordTrace tailWord_6608746 prefixEnd_6608746 1131154407159501828193979 := by
  unfold tailWord_6608746
  simp only [CollatzResearch.WordTrace]
  refine ⟨60260192228912350200697523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160693845943766267201860061 60260192228912350200697523)
  ·
    refine ⟨90390288343368525301046285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60260192228912350200697523 90390288343368525301046285)
    ·
      refine ⟨33896358128763196987892357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90390288343368525301046285 33896358128763196987892357)
      ·
        refine ⟨6355567149143099435229817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33896358128763196987892357 6355567149143099435229817)
        ·
          refine ⟨4766675361857324576422363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6355567149143099435229817 4766675361857324576422363)
          ·
            refine ⟨7150013042785986864633545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4766675361857324576422363 7150013042785986864633545)
            ·
              refine ⟨5362509782089490148475159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7150013042785986864633545 5362509782089490148475159)
              ·
                refine ⟨8043764673134235222712739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5362509782089490148475159 8043764673134235222712739)
                ·
                  refine ⟨12065647009701352834069109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8043764673134235222712739 12065647009701352834069109)
                  ·
                    refine ⟨1131154407159501828193979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12065647009701352834069109 1131154407159501828193979)
                    ·
                      rfl

theorem cell23_6608746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_6608746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608746 prefixEnd_6608746 := by exact prefixLift 6608746
  have htrace : WordTrace (prefixWord ++ tailWord_6608746) baseStart_6608746 baseEnd_6608746 := by
    simpa [prefixWord, tailWord_6608746, baseEnd_6608746] using wordTrace_append hprefix tailTrace_6608746
  have hstable : (prefixWord ++ tailWord_6608746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608746).length < 2 ^ (prefixWord ++ tailWord_6608746).sum := by decide
  have hdescent : baseEnd_6608746 < baseStart_6608746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608749 : List Nat := [1, 5, 1, 1, 1, 1, 3, 5, 1, 2, 2]
def baseStart_6608749 : Nat := 118140960795 + 6608749 * 2 ^ 59
def prefixEnd_6608749 : Nat := 4983230072969 + 3 ^ 40 * 6608749 * 2
def baseEnd_6608749 : Nat := 3393464761920468972844423

theorem tailTrace_6608749 : CollatzResearch.WordTrace tailWord_6608749 prefixEnd_6608749 3393464761920468972844423 := by
  unfold tailWord_6608749
  simp only [CollatzResearch.WordTrace]
  refine ⟨241040878334638532315149301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160693918889759021543432867 241040878334638532315149301)
  ·
    refine ⟨22597582343872362404545247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241040878334638532315149301 22597582343872362404545247)
    ·
      refine ⟨33896373515808543606817871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22597582343872362404545247 33896373515808543606817871)
      ·
        refine ⟨50844560273712815410226807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33896373515808543606817871 50844560273712815410226807)
        ·
          refine ⟨76266840410569223115340211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50844560273712815410226807 76266840410569223115340211)
          ·
            refine ⟨114400260615853834673010317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76266840410569223115340211 114400260615853834673010317)
            ·
              refine ⟨42900097730945188002378869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114400260615853834673010317 42900097730945188002378869)
              ·
                refine ⟨4021884162276111375223019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42900097730945188002378869 4021884162276111375223019)
                ·
                  refine ⟨6032826243414167062834529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4021884162276111375223019 6032826243414167062834529)
                  ·
                    refine ⟨4524619682560625297125897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6032826243414167062834529 4524619682560625297125897)
                    ·
                      refine ⟨3393464761920468972844423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524619682560625297125897 3393464761920468972844423)
                      ·
                        rfl

theorem cell23_6608749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 5, 1, 2, 2].length) (baseStart_6608749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608749 prefixEnd_6608749 := by exact prefixLift 6608749
  have htrace : WordTrace (prefixWord ++ tailWord_6608749) baseStart_6608749 baseEnd_6608749 := by
    simpa [prefixWord, tailWord_6608749, baseEnd_6608749] using wordTrace_append hprefix tailTrace_6608749
  have hstable : (prefixWord ++ tailWord_6608749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608749).length < 2 ^ (prefixWord ++ tailWord_6608749).sum := by decide
  have hdescent : baseEnd_6608749 < baseStart_6608749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608766 : List Nat := [4, 2, 3, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_6608766 : Nat := 118140960795 + 6608766 * 2 ^ 59
def prefixEnd_6608766 : Nat := 4983230072969 + 3 ^ 40 * 6608766 * 2
def baseEnd_6608766 : Nat := 3393473491091595406331845

theorem tailTrace_6608766 : CollatzResearch.WordTrace tailWord_6608766 prefixEnd_6608766 3393473491091595406331845 := by
  unfold tailWord_6608766
  simp only [CollatzResearch.WordTrace]
  refine ⟨30130187296947118027314769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160694332250384629479012101 30130187296947118027314769)
  ·
    refine ⟨22597640472710338520486077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30130187296947118027314769 22597640472710338520486077)
    ·
      refine ⟨8474115177266376945182279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22597640472710338520486077 8474115177266376945182279)
      ·
        refine ⟨12711172765899565417773419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8474115177266376945182279 12711172765899565417773419)
        ·
          refine ⟨19066759148849348126660129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12711172765899565417773419 19066759148849348126660129)
          ·
            refine ⟨14300069361637011094995097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19066759148849348126660129 14300069361637011094995097)
            ·
              refine ⟨10725052021227758321246323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14300069361637011094995097 10725052021227758321246323)
              ·
                refine ⟨16087578031841637481869485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10725052021227758321246323 16087578031841637481869485)
                ·
                  refine ⟨6032841761940614055701057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16087578031841637481869485 6032841761940614055701057)
                  ·
                    refine ⟨4524631321455460541775793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6032841761940614055701057 4524631321455460541775793)
                    ·
                      refine ⟨3393473491091595406331845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524631321455460541775793 3393473491091595406331845)
                      ·
                        rfl

theorem cell23_6608766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_6608766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608766 prefixEnd_6608766 := by exact prefixLift 6608766
  have htrace : WordTrace (prefixWord ++ tailWord_6608766) baseStart_6608766 baseEnd_6608766 := by
    simpa [prefixWord, tailWord_6608766, baseEnd_6608766] using wordTrace_append hprefix tailTrace_6608766
  have hstable : (prefixWord ++ tailWord_6608766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608766).length < 2 ^ (prefixWord ++ tailWord_6608766).sum := by decide
  have hdescent : baseEnd_6608766 < baseStart_6608766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608805 : List Nat := [1, 3, 1, 2, 1, 1, 1, 6, 1, 4, 2]
def baseStart_6608805 : Nat := 118140960795 + 6608805 * 2 ^ 59
def prefixEnd_6608805 : Nat := 4983230072969 + 3 ^ 40 * 6608805 * 2
def baseEnd_6608805 : Nat := 3393493516837120753744165

theorem tailTrace_6608805 : CollatzResearch.WordTrace tailWord_6608805 prefixEnd_6608805 3393493516837120753744165 := by
  unfold tailWord_6608805
  simp only [CollatzResearch.WordTrace]
  refine ⟨241042920822435653879187869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160695280548290435919458579 241042920822435653879187869)
  ·
    refine ⟨90391095308413370204695451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241042920822435653879187869 90391095308413370204695451)
    ·
      refine ⟨135586642962620055307043177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90391095308413370204695451 135586642962620055307043177)
      ·
        refine ⟨101689982221965041480282383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135586642962620055307043177 101689982221965041480282383)
        ·
          refine ⟨152534973332947562220423575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101689982221965041480282383 152534973332947562220423575)
          ·
            refine ⟨228802459999421343330635363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152534973332947562220423575 228802459999421343330635363)
            ·
              refine ⟨343203689999132014995953045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228802459999421343330635363 343203689999132014995953045)
              ·
                refine ⟨16087672968709313202935299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 343203689999132014995953045 16087672968709313202935299)
                ·
                  refine ⟨24131509453063969804402949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16087672968709313202935299 24131509453063969804402949)
                  ·
                    refine ⟨4524658022449494338325553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24131509453063969804402949 4524658022449494338325553)
                    ·
                      refine ⟨3393493516837120753744165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524658022449494338325553 3393493516837120753744165)
                      ·
                        rfl

theorem cell23_6608805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_6608805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608805 prefixEnd_6608805 := by exact prefixLift 6608805
  have htrace : WordTrace (prefixWord ++ tailWord_6608805) baseStart_6608805 baseEnd_6608805 := by
    simpa [prefixWord, tailWord_6608805, baseEnd_6608805] using wordTrace_append hprefix tailTrace_6608805
  have hstable : (prefixWord ++ tailWord_6608805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608805).length < 2 ^ (prefixWord ++ tailWord_6608805).sum := by decide
  have hdescent : baseEnd_6608805 < baseStart_6608805 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608818 : List Nat := [3, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4]
def baseStart_6608818 : Nat := 118140960795 + 6608818 * 2 ^ 59
def prefixEnd_6608818 : Nat := 4983230072969 + 3 ^ 40 * 6608818 * 2
def baseEnd_6608818 : Nat := 3393500192085629202881605

theorem tailTrace_6608818 : CollatzResearch.WordTrace tailWord_6608818 prefixEnd_6608818 3393500192085629202881605 := by
  unfold tailWord_6608818
  simp only [CollatzResearch.WordTrace]
  refine ⟨60260848742847139274852777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160695596647592371399607405 60260848742847139274852777)
  ·
    refine ⟨45195636557135354456139583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60260848742847139274852777 45195636557135354456139583)
    ·
      refine ⟨67793454835703031684209375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45195636557135354456139583 67793454835703031684209375)
      ·
        refine ⟨101690182253554547526314063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67793454835703031684209375 101690182253554547526314063)
        ·
          refine ⟨152535273380331821289471095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101690182253554547526314063 152535273380331821289471095)
          ·
            refine ⟨228802910070497731934206643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152535273380331821289471095 228802910070497731934206643)
            ·
              refine ⟨343204365105746597901309965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228802910070497731934206643 343204365105746597901309965)
              ·
                refine ⟨128701636914654974212991237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 343204365105746597901309965 128701636914654974212991237)
                ·
                  refine ⟨24131556921497807664935857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 128701636914654974212991237 24131556921497807664935857)
                  ·
                    refine ⟨18098667691123355748701893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24131556921497807664935857 18098667691123355748701893)
                    ·
                      refine ⟨3393500192085629202881605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18098667691123355748701893 3393500192085629202881605)
                      ·
                        rfl

theorem cell23_6608818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_6608818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608818 prefixEnd_6608818 := by exact prefixLift 6608818
  have htrace : WordTrace (prefixWord ++ tailWord_6608818) baseStart_6608818 baseEnd_6608818 := by
    simpa [prefixWord, tailWord_6608818, baseEnd_6608818] using wordTrace_append hprefix tailTrace_6608818
  have hstable : (prefixWord ++ tailWord_6608818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608818).length < 2 ^ (prefixWord ++ tailWord_6608818).sum := by decide
  have hdescent : baseEnd_6608818 < baseStart_6608818 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608860 : List Nat := [2, 2, 6, 1, 1, 1, 3, 1, 1, 3, 2]
def baseStart_6608860 : Nat := 118140960795 + 6608860 * 2 ^ 59
def prefixEnd_6608860 : Nat := 4983230072969 + 3 ^ 40 * 6608860 * 2
def baseEnd_6608860 : Nat := 3393521758273118038556413

theorem tailTrace_6608860 : CollatzResearch.WordTrace tailWord_6608860 prefixEnd_6608860 3393521758273118038556413 := by
  unfold tailWord_6608860
  simp only [CollatzResearch.WordTrace]
  refine ⟨120522463418618199136220017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160696617891490932181626689 120522463418618199136220017)
  ·
    refine ⟨90391847563963649352165013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120522463418618199136220017 90391847563963649352165013)
    ·
      refine ⟨4237117854560796063382735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 90391847563963649352165013 4237117854560796063382735)
      ·
        refine ⟨6355676781841194095074103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4237117854560796063382735 6355676781841194095074103)
        ·
          refine ⟨9533515172761791142611155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6355676781841194095074103 9533515172761791142611155)
          ·
            refine ⟨14300272759142686713916733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9533515172761791142611155 14300272759142686713916733)
            ·
              refine ⟨5362602284678507517718775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14300272759142686713916733 5362602284678507517718775)
              ·
                refine ⟨8043903427017761276578163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5362602284678507517718775 8043903427017761276578163)
                ·
                  refine ⟨12065855140526641914867245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8043903427017761276578163 12065855140526641914867245)
                  ·
                    refine ⟨4524695677697490718075217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12065855140526641914867245 4524695677697490718075217)
                    ·
                      refine ⟨3393521758273118038556413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524695677697490718075217 3393521758273118038556413)
                      ·
                        rfl

theorem cell23_6608860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_6608860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608860 prefixEnd_6608860 := by exact prefixLift 6608860
  have htrace : WordTrace (prefixWord ++ tailWord_6608860) baseStart_6608860 baseEnd_6608860 := by
    simpa [prefixWord, tailWord_6608860, baseEnd_6608860] using wordTrace_append hprefix tailTrace_6608860
  have hstable : (prefixWord ++ tailWord_6608860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608860).length < 2 ^ (prefixWord ++ tailWord_6608860).sum := by decide
  have hdescent : baseEnd_6608860 < baseStart_6608860 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608868 : List Nat := [2, 3, 1, 1, 1, 1, 3, 1, 3, 2, 5]
def baseStart_6608868 : Nat := 118140960795 + 6608868 * 2 ^ 59
def prefixEnd_6608868 : Nat := 4983230072969 + 3 ^ 40 * 6608868 * 2
def baseEnd_6608868 : Nat := 3393525866118354007256375

theorem tailTrace_6608868 : CollatzResearch.WordTrace tailWord_6608868 prefixEnd_6608868 3393525866118354007256375 := by
  unfold tailWord_6608868
  simp only [CollatzResearch.WordTrace]
  refine ⟨120522609310603707819365629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160696812414138277092487505 120522609310603707819365629)
  ·
    refine ⟨45195978491476390432262111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120522609310603707819365629 45195978491476390432262111)
    ·
      refine ⟨67793967737214585648393167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45195978491476390432262111 67793967737214585648393167)
      ·
        refine ⟨101690951605821878472589751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67793967737214585648393167 101690951605821878472589751)
        ·
          refine ⟨152536427408732817708884627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101690951605821878472589751 152536427408732817708884627)
          ·
            refine ⟨228804641113099226563326941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152536427408732817708884627 228804641113099226563326941)
            ·
              refine ⟨85801740417412209961247603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228804641113099226563326941 85801740417412209961247603)
              ·
                refine ⟨128702610626118314941871405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85801740417412209961247603 128702610626118314941871405)
                ·
                  refine ⟨48263478984794368103201777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128702610626118314941871405 48263478984794368103201777)
                  ·
                    refine ⟨36197609238595776077401333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48263478984794368103201777 36197609238595776077401333)
                    ·
                      refine ⟨3393525866118354007256375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36197609238595776077401333 3393525866118354007256375)
                      ·
                        rfl

theorem cell23_6608868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 1, 3, 2, 5].length) (baseStart_6608868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608868 prefixEnd_6608868 := by exact prefixLift 6608868
  have htrace : WordTrace (prefixWord ++ tailWord_6608868) baseStart_6608868 baseEnd_6608868 := by
    simpa [prefixWord, tailWord_6608868, baseEnd_6608868] using wordTrace_append hprefix tailTrace_6608868
  have hstable : (prefixWord ++ tailWord_6608868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608868).length < 2 ^ (prefixWord ++ tailWord_6608868).sum := by decide
  have hdescent : baseEnd_6608868 < baseStart_6608868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608925 : List Nat := [1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_6608925 : Nat := 118140960795 + 6608925 * 2 ^ 59
def prefixEnd_6608925 : Nat := 4983230072969 + 3 ^ 40 * 6608925 * 2
def baseEnd_6608925 : Nat := 3393555134515660284243613

theorem tailTrace_6608925 : CollatzResearch.WordTrace tailWord_6608925 prefixEnd_6608925 3393555134515660284243613 := by
  unfold tailWord_6608925
  simp only [CollatzResearch.WordTrace]
  refine ⟨241047297582000914373556229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160698198388000609582370819 241047297582000914373556229)
  ·
    refine ⟨45196368296625171445041793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241047297582000914373556229 45196368296625171445041793)
    ·
      refine ⟨33897276222468878583781345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45196368296625171445041793 33897276222468878583781345)
      ·
        refine ⟨25422957166851658937836009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33897276222468878583781345 25422957166851658937836009)
        ·
          refine ⟨19067217875138744203377007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25422957166851658937836009 19067217875138744203377007)
          ·
            refine ⟨28600826812708116305065511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19067217875138744203377007 28600826812708116305065511)
            ·
              refine ⟨42901240219062174457598267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28600826812708116305065511 42901240219062174457598267)
              ·
                refine ⟨64351860328593261686397401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42901240219062174457598267 64351860328593261686397401)
                ·
                  refine ⟨48263895246444946264798051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64351860328593261686397401 48263895246444946264798051)
                  ·
                    refine ⟨72395842869667419397197077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48263895246444946264798051 72395842869667419397197077)
                    ·
                      refine ⟨3393555134515660284243613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72395842869667419397197077 3393555134515660284243613)
                      ·
                        rfl

theorem cell23_6608925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_6608925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608925 prefixEnd_6608925 := by exact prefixLift 6608925
  have htrace : WordTrace (prefixWord ++ tailWord_6608925) baseStart_6608925 baseEnd_6608925 := by
    simpa [prefixWord, tailWord_6608925, baseEnd_6608925] using wordTrace_append hprefix tailTrace_6608925
  have hstable : (prefixWord ++ tailWord_6608925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608925).length < 2 ^ (prefixWord ++ tailWord_6608925).sum := by decide
  have hdescent : baseEnd_6608925 < baseStart_6608925 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608972 : List Nat := [2, 2, 1, 3, 1, 1, 4, 1, 1, 5, 2]
def baseStart_6608972 : Nat := 118140960795 + 6608972 * 2 ^ 59
def prefixEnd_6608972 : Nat := 4983230072969 + 3 ^ 40 * 6608972 * 2
def baseEnd_6608972 : Nat := 3393579268106421600355897

theorem tailTrace_6608972 : CollatzResearch.WordTrace tailWord_6608972 prefixEnd_6608972 3393579268106421600355897 := by
  unfold tailWord_6608972
  simp only [CollatzResearch.WordTrace]
  refine ⟨120524505906415320700258585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160699341208553760933678113 120524505906415320700258585)
  ·
    refine ⟨90393379429811490525193939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120524505906415320700258585 90393379429811490525193939)
    ·
      refine ⟨135590069144717235787790909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90393379429811490525193939 135590069144717235787790909)
      ·
        refine ⟨50846275929268963420421591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135590069144717235787790909 50846275929268963420421591)
        ·
          refine ⟨76269413893903445130632387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50846275929268963420421591 76269413893903445130632387)
          ·
            refine ⟨114404120840855167695948581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76269413893903445130632387 114404120840855167695948581)
            ·
              refine ⟨21450772657660343942990359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114404120840855167695948581 21450772657660343942990359)
              ·
                refine ⟨32176158986490515914485539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21450772657660343942990359 32176158986490515914485539)
                ·
                  refine ⟨48264238479735773871728309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32176158986490515914485539 48264238479735773871728309)
                  ·
                    refine ⟨4524772357475228800474529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48264238479735773871728309 4524772357475228800474529)
                    ·
                      refine ⟨3393579268106421600355897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524772357475228800474529 3393579268106421600355897)
                      ·
                        rfl

theorem cell23_6608972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 1, 5, 2].length) (baseStart_6608972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608972 prefixEnd_6608972 := by exact prefixLift 6608972
  have htrace : WordTrace (prefixWord ++ tailWord_6608972) baseStart_6608972 baseEnd_6608972 := by
    simpa [prefixWord, tailWord_6608972, baseEnd_6608972] using wordTrace_append hprefix tailTrace_6608972
  have hstable : (prefixWord ++ tailWord_6608972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608972).length < 2 ^ (prefixWord ++ tailWord_6608972).sum := by decide
  have hdescent : baseEnd_6608972 < baseStart_6608972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6608990 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 3, 4]
def baseStart_6608990 : Nat := 118140960795 + 6608990 * 2 ^ 59
def prefixEnd_6608990 : Nat := 4983230072969 + 3 ^ 40 * 6608990 * 2
def baseEnd_6608990 : Nat := 1131196170252734176643605

theorem tailTrace_6608990 : CollatzResearch.WordTrace tailWord_6608990 prefixEnd_6608990 1131196170252734176643605 := by
  unfold tailWord_6608990
  simp only [CollatzResearch.WordTrace]
  refine ⟨30131208540845678809334053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160699778884510286983114949 30131208540845678809334053)
  ·
    refine ⟨5649601601408564776750135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30131208540845678809334053 5649601601408564776750135)
    ·
      refine ⟨8474402402112847165125203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5649601601408564776750135 8474402402112847165125203)
      ·
        refine ⟨12711603603169270747687805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8474402402112847165125203 12711603603169270747687805)
        ·
          refine ⟨4766851351188476530382927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12711603603169270747687805 4766851351188476530382927)
          ·
            refine ⟨7150277026782714795574391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4766851351188476530382927 7150277026782714795574391)
            ·
              refine ⟨10725415540174072193361587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7150277026782714795574391 10725415540174072193361587)
              ·
                refine ⟨16088123310261108290042381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10725415540174072193361587 16088123310261108290042381)
                ·
                  refine ⟨6033046241347915608765893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16088123310261108290042381 6033046241347915608765893)
                  ·
                    refine ⟨1131196170252734176643605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6033046241347915608765893 1131196170252734176643605)
                    ·
                      rfl

theorem cell23_6608990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_6608990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6608990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6608990 prefixEnd_6608990 := by exact prefixLift 6608990
  have htrace : WordTrace (prefixWord ++ tailWord_6608990) baseStart_6608990 baseEnd_6608990 := by
    simpa [prefixWord, tailWord_6608990, baseEnd_6608990] using wordTrace_append hprefix tailTrace_6608990
  have hstable : (prefixWord ++ tailWord_6608990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6608990).length < 2 ^ (prefixWord ++ tailWord_6608990).sum := by decide
  have hdescent : baseEnd_6608990 < baseStart_6608990 := by decide
  rcases family_descends (prefixWord ++ tailWord_6608990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609015 : List Nat := [1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 6]
def baseStart_6609015 : Nat := 118140960795 + 6609015 * 2 ^ 59
def prefixEnd_6609015 : Nat := 4983230072969 + 3 ^ 40 * 6609015 * 2
def baseEnd_6609015 : Nat := 3393601347774564932118199

theorem tailTrace_6609015 : CollatzResearch.WordTrace tailWord_6609015 prefixEnd_6609015 3393601347774564932118199 := by
  unfold tailWord_6609015
  simp only [CollatzResearch.WordTrace]
  refine ⟨241050580151674859744332499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160700386767783239829554999 241050580151674859744332499)
  ·
    refine ⟨361575870227512289616498749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241050580151674859744332499 361575870227512289616498749)
    ·
      refine ⟨135590951335317108606187031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361575870227512289616498749 135590951335317108606187031)
      ·
        refine ⟨203386427002975662909280547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135590951335317108606187031 203386427002975662909280547)
        ·
          refine ⟨305079640504463494363920821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203386427002975662909280547 305079640504463494363920821)
          ·
            refine ⟨28601216297293452596617577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 305079640504463494363920821 28601216297293452596617577)
            ·
              refine ⟨21450912222970089447463183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28601216297293452596617577 21450912222970089447463183)
              ·
                refine ⟨32176368334455134171194775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21450912222970089447463183 32176368334455134171194775)
                ·
                  refine ⟨48264552501682701256792163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32176368334455134171194775 48264552501682701256792163)
                  ·
                    refine ⟨72396828752524051885188245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48264552501682701256792163 72396828752524051885188245)
                    ·
                      refine ⟨3393601347774564932118199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72396828752524051885188245 3393601347774564932118199)
                      ·
                        rfl

theorem cell23_6609015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 6].length) (baseStart_6609015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609015 prefixEnd_6609015 := by exact prefixLift 6609015
  have htrace : WordTrace (prefixWord ++ tailWord_6609015) baseStart_6609015 baseEnd_6609015 := by
    simpa [prefixWord, tailWord_6609015, baseEnd_6609015] using wordTrace_append hprefix tailTrace_6609015
  have hstable : (prefixWord ++ tailWord_6609015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609015).length < 2 ^ (prefixWord ++ tailWord_6609015).sum := by decide
  have hdescent : baseEnd_6609015 < baseStart_6609015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609032 : List Nat := [2, 1, 3, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_6609032 : Nat := 118140960795 + 6609032 * 2 ^ 59
def prefixEnd_6609032 : Nat := 4983230072969 + 3 ^ 40 * 6609032 * 2
def baseEnd_6609032 : Nat := 3393610076945691365605621

theorem tailTrace_6609032 : CollatzResearch.WordTrace tailWord_6609032 prefixEnd_6609032 3393610076945691365605621 := by
  unfold tailWord_6609032
  simp only [CollatzResearch.WordTrace]
  refine ⟨120525600096306635823850675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160700800128408847765134233 120525600096306635823850675)
  ·
    refine ⟨180788400144459953735776013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120525600096306635823850675 180788400144459953735776013)
    ·
      refine ⟨67795650054172482650916005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180788400144459953735776013 67795650054172482650916005)
      ·
        refine ⟨12711684385157340497046751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67795650054172482650916005 12711684385157340497046751)
        ·
          refine ⟨19067526577736010745570127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12711684385157340497046751 19067526577736010745570127)
          ·
            refine ⟨28601289866604016118355191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19067526577736010745570127 28601289866604016118355191)
            ·
              refine ⟨42901934799906024177532787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28601289866604016118355191 42901934799906024177532787)
              ·
                refine ⟨64352902199859036266299181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42901934799906024177532787 64352902199859036266299181)
                ·
                  refine ⟨24132338324947138599862193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64352902199859036266299181 24132338324947138599862193)
                  ·
                    refine ⟨18099253743710353949896645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24132338324947138599862193 18099253743710353949896645)
                    ·
                      refine ⟨3393610076945691365605621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18099253743710353949896645 3393610076945691365605621)
                      ·
                        rfl

theorem cell23_6609032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_6609032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609032 prefixEnd_6609032 := by exact prefixLift 6609032
  have htrace : WordTrace (prefixWord ++ tailWord_6609032) baseStart_6609032 baseEnd_6609032 := by
    simpa [prefixWord, tailWord_6609032, baseEnd_6609032] using wordTrace_append hprefix tailTrace_6609032
  have hstable : (prefixWord ++ tailWord_6609032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609032).length < 2 ^ (prefixWord ++ tailWord_6609032).sum := by decide
  have hdescent : baseEnd_6609032 < baseStart_6609032 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609052 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 3, 3, 3]
def baseStart_6609052 : Nat := 118140960795 + 6609052 * 2 ^ 59
def prefixEnd_6609052 : Nat := 4983230072969 + 3 ^ 40 * 6609052 * 2
def baseEnd_6609052 : Nat := 3393620346558781287355529

theorem tailTrace_6609052 : CollatzResearch.WordTrace tailWord_6609052 prefixEnd_6609052 3393620346558781287355529 := by
  unfold tailWord_6609052
  simp only [CollatzResearch.WordTrace]
  refine ⟨120525964826270407531714705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160701286435027210042286273 120525964826270407531714705)
  ·
    refine ⟨90394473619702805648786029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120525964826270407531714705 90394473619702805648786029)
    ·
      refine ⟨33897927607388552118294761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90394473619702805648786029 33897927607388552118294761)
      ·
        refine ⟨25423445705541414088721071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33897927607388552118294761 25423445705541414088721071)
        ·
          refine ⟨38135168558312121133081607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25423445705541414088721071 38135168558312121133081607)
          ·
            refine ⟨57202752837468181699622411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38135168558312121133081607 57202752837468181699622411)
            ·
              refine ⟨85804129256202272549433617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57202752837468181699622411 85804129256202272549433617)
              ·
                refine ⟨64353096942151704412075213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85804129256202272549433617 64353096942151704412075213)
                ·
                  refine ⟨24132411353306889154528205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 64353096942151704412075213 24132411353306889154528205)
                  ·
                    refine ⟨9049654257490083432948077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24132411353306889154528205 9049654257490083432948077)
                    ·
                      refine ⟨3393620346558781287355529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9049654257490083432948077 3393620346558781287355529)
                      ·
                        rfl

theorem cell23_6609052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_6609052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609052 prefixEnd_6609052 := by exact prefixLift 6609052
  have htrace : WordTrace (prefixWord ++ tailWord_6609052) baseStart_6609052 baseEnd_6609052 := by
    simpa [prefixWord, tailWord_6609052, baseEnd_6609052] using wordTrace_append hprefix tailTrace_6609052
  have hstable : (prefixWord ++ tailWord_6609052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609052).length < 2 ^ (prefixWord ++ tailWord_6609052).sum := by decide
  have hdescent : baseEnd_6609052 < baseStart_6609052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609053 : List Nat := [1, 4, 2, 1, 1, 4, 1, 4, 1, 2, 2]
def baseStart_6609053 : Nat := 118140960795 + 6609053 * 2 ^ 59
def prefixEnd_6609053 : Nat := 4983230072969 + 3 ^ 40 * 6609053 * 2
def baseEnd_6609053 : Nat := 3393620860039435783443025

theorem tailTrace_6609053 : CollatzResearch.WordTrace tailWord_6609053 prefixEnd_6609053 3393620860039435783443025 := by
  unfold tailWord_6609053
  simp only [CollatzResearch.WordTrace]
  refine ⟨241051966125537192234215813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160701310750358128156143875 241051966125537192234215813)
  ·
    refine ⟨45197243648538223543915465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241051966125537192234215813 45197243648538223543915465)
    ·
      refine ⟨33897932736403667657936599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45197243648538223543915465 33897932736403667657936599)
      ·
        refine ⟨50846899104605501486904899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33897932736403667657936599 50846899104605501486904899)
        ·
          refine ⟨76270348656908252230357349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50846899104605501486904899 76270348656908252230357349)
          ·
            refine ⟨14300690373170297293192003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76270348656908252230357349 14300690373170297293192003)
            ·
              refine ⟨21451035559755445939788005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14300690373170297293192003 21451035559755445939788005)
              ·
                refine ⟨4022069167454146113710251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21451035559755445939788005 4022069167454146113710251)
                ·
                  refine ⟨6033103751181219170565377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4022069167454146113710251 6033103751181219170565377)
                  ·
                    refine ⟨4524827813385914377924033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6033103751181219170565377 4524827813385914377924033)
                    ·
                      refine ⟨3393620860039435783443025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524827813385914377924033 3393620860039435783443025)
                      ·
                        rfl

theorem cell23_6609053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_6609053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609053 prefixEnd_6609053 := by exact prefixLift 6609053
  have htrace : WordTrace (prefixWord ++ tailWord_6609053) baseStart_6609053 baseEnd_6609053 := by
    simpa [prefixWord, tailWord_6609053, baseEnd_6609053] using wordTrace_append hprefix tailTrace_6609053
  have hstable : (prefixWord ++ tailWord_6609053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609053).length < 2 ^ (prefixWord ++ tailWord_6609053).sum := by decide
  have hdescent : baseEnd_6609053 < baseStart_6609053 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609066 : List Nat := [3, 1, 5, 1, 2, 1, 2, 1, 1, 2, 4]
def baseStart_6609066 : Nat := 118140960795 + 6609066 * 2 ^ 59
def prefixEnd_6609066 : Nat := 4983230072969 + 3 ^ 40 * 6609066 * 2
def baseEnd_6609066 : Nat := 3393627535287944232580465

theorem tailTrace_6609066 : CollatzResearch.WordTrace tailWord_6609066 prefixEnd_6609066 3393627535287944232580465 := by
  unfold tailWord_6609066
  simp only [CollatzResearch.WordTrace]
  refine ⟨60263110068622523863609763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160701626849660063636292701 60263110068622523863609763)
  ·
    refine ⟨90394665102933785795414645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60263110068622523863609763 90394665102933785795414645)
    ·
      refine ⟨8474499853400042418320123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 90394665102933785795414645 8474499853400042418320123)
      ·
        refine ⟨12711749780100063627480185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8474499853400042418320123 12711749780100063627480185)
        ·
          refine ⟨9533812335075047720610139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12711749780100063627480185 9533812335075047720610139)
          ·
            refine ⟨14300718502612571580915209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9533812335075047720610139 14300718502612571580915209)
            ·
              refine ⟨10725538876959428685686407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14300718502612571580915209 10725538876959428685686407)
              ·
                refine ⟨16088308315439143028529611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10725538876959428685686407 16088308315439143028529611)
                ·
                  refine ⟨24132462473158714542794417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16088308315439143028529611 24132462473158714542794417)
                  ·
                    refine ⟨18099346854869035907095813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24132462473158714542794417 18099346854869035907095813)
                    ·
                      refine ⟨3393627535287944232580465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18099346854869035907095813 3393627535287944232580465)
                      ·
                        rfl

theorem cell23_6609066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_6609066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609066 prefixEnd_6609066 := by exact prefixLift 6609066
  have htrace : WordTrace (prefixWord ++ tailWord_6609066) baseStart_6609066 baseEnd_6609066 := by
    simpa [prefixWord, tailWord_6609066, baseEnd_6609066] using wordTrace_append hprefix tailTrace_6609066
  have hstable : (prefixWord ++ tailWord_6609066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609066).length < 2 ^ (prefixWord ++ tailWord_6609066).sum := by decide
  have hdescent : baseEnd_6609066 < baseStart_6609066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609069 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 1, 3, 3]
def baseStart_6609069 : Nat := 118140960795 + 6609069 * 2 ^ 59
def prefixEnd_6609069 : Nat := 4983230072969 + 3 ^ 40 * 6609069 * 2
def baseEnd_6609069 : Nat := 3393629075729907720842951

theorem tailTrace_6609069 : CollatzResearch.WordTrace tailWord_6609069 prefixEnd_6609069 3393629075729907720842951 := by
  unfold tailWord_6609069
  simp only [CollatzResearch.WordTrace]
  refine ⟨241052549693479226966798261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160701699795652817977865507 241052549693479226966798261)
  ·
    refine ⟨22598676533763677528137337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 241052549693479226966798261 22598676533763677528137337)
    ·
      refine ⟨16949007400322758146103003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22598676533763677528137337 16949007400322758146103003)
      ·
        refine ⟨25423511100484137219154505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16949007400322758146103003 25423511100484137219154505)
        ·
          refine ⟨19067633325363102914365879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25423511100484137219154505 19067633325363102914365879)
          ·
            refine ⟨28601449988044654371548819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19067633325363102914365879 28601449988044654371548819)
            ·
              refine ⟨42902174982066981557323229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28601449988044654371548819 42902174982066981557323229)
              ·
                refine ⟨16088315618275118083996211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42902174982066981557323229 16088315618275118083996211)
                ·
                  refine ⟨24132473427412677125994317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16088315618275118083996211 24132473427412677125994317)
                  ·
                    refine ⟨9049677535279753922247869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24132473427412677125994317 9049677535279753922247869)
                    ·
                      refine ⟨3393629075729907720842951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9049677535279753922247869 3393629075729907720842951)
                      ·
                        rfl

theorem cell23_6609069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_6609069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609069 prefixEnd_6609069 := by exact prefixLift 6609069
  have htrace : WordTrace (prefixWord ++ tailWord_6609069) baseStart_6609069 baseEnd_6609069 := by
    simpa [prefixWord, tailWord_6609069, baseEnd_6609069] using wordTrace_append hprefix tailTrace_6609069
  have hstable : (prefixWord ++ tailWord_6609069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609069).length < 2 ^ (prefixWord ++ tailWord_6609069).sum := by decide
  have hdescent : baseEnd_6609069 < baseStart_6609069 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609070 : List Nat := [4, 1, 4, 2, 1, 1, 1, 2, 3, 2, 2]
def baseStart_6609070 : Nat := 118140960795 + 6609070 * 2 ^ 59
def prefixEnd_6609070 : Nat := 4983230072969 + 3 ^ 40 * 6609070 * 2
def baseEnd_6609070 : Nat := 3393629589210562216930447

theorem tailTrace_6609070 : CollatzResearch.WordTrace tailWord_6609070 prefixEnd_6609070 3393629589210562216930447 := by
  unfold tailWord_6609070
  simp only [CollatzResearch.WordTrace]
  refine ⟨30131573270809450517198083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160701724110983736091723109 30131573270809450517198083)
  ·
    refine ⟨45197359906214175775797125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30131573270809450517198083 45197359906214175775797125)
    ·
      refine ⟨8474504982415157957961961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45197359906214175775797125 8474504982415157957961961)
      ·
        refine ⟨6355878736811368468471471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8474504982415157957961961 6355878736811368468471471)
        ·
          refine ⟨9533818105217052702707207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6355878736811368468471471 9533818105217052702707207)
          ·
            refine ⟨14300727157825579054060811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9533818105217052702707207 14300727157825579054060811)
            ·
              refine ⟨21451090736738368581091217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14300727157825579054060811 21451090736738368581091217)
              ·
                refine ⟨16088318052553776435818413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21451090736738368581091217 16088318052553776435818413)
                ·
                  refine ⟨6033119269707666163431905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16088318052553776435818413 6033119269707666163431905)
                  ·
                    refine ⟨4524839452280749622573929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6033119269707666163431905 4524839452280749622573929)
                    ·
                      refine ⟨3393629589210562216930447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524839452280749622573929 3393629589210562216930447)
                      ·
                        rfl

theorem cell23_6609070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_6609070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609070 prefixEnd_6609070 := by exact prefixLift 6609070
  have htrace : WordTrace (prefixWord ++ tailWord_6609070) baseStart_6609070 baseEnd_6609070 := by
    simpa [prefixWord, tailWord_6609070, baseEnd_6609070] using wordTrace_append hprefix tailTrace_6609070
  have hstable : (prefixWord ++ tailWord_6609070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609070).length < 2 ^ (prefixWord ++ tailWord_6609070).sum := by decide
  have hdescent : baseEnd_6609070 < baseStart_6609070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609075 : List Nat := [1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 4]
def baseStart_6609075 : Nat := 118140960795 + 6609075 * 2 ^ 59
def prefixEnd_6609075 : Nat := 4983230072969 + 3 ^ 40 * 6609075 * 2
def baseEnd_6609075 : Nat := 3393632156613834697367923

theorem tailTrace_6609075 : CollatzResearch.WordTrace tailWord_6609075 prefixEnd_6609075 3393632156613834697367923 := by
  unfold tailWord_6609075
  simp only [CollatzResearch.WordTrace]
  refine ⟨241052768531457489991516679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160701845687638326661011119 241052768531457489991516679)
  ·
    refine ⟨361579152797186234987275019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241052768531457489991516679 361579152797186234987275019)
    ·
      refine ⟨542368729195779352480912529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361579152797186234987275019 542368729195779352480912529)
      ·
        refine ⟨406776546896834514360684397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542368729195779352480912529 406776546896834514360684397)
        ·
          refine ⟨152541205086312942885256649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 406776546896834514360684397 152541205086312942885256649)
          ·
            refine ⟨114405903814734707163942487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152541205086312942885256649 114405903814734707163942487)
            ·
              refine ⟨171608855722102060745913731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114405903814734707163942487 171608855722102060745913731)
              ·
                refine ⟨257413283583153091118870597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171608855722102060745913731 257413283583153091118870597)
                ·
                  refine ⟨48264990671841204584788237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 257413283583153091118870597 48264990671841204584788237)
                  ·
                    refine ⟨18099371501940451719295589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48264990671841204584788237 18099371501940451719295589)
                    ·
                      refine ⟨3393632156613834697367923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18099371501940451719295589 3393632156613834697367923)
                      ·
                        rfl

theorem cell23_6609075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_6609075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609075 prefixEnd_6609075 := by exact prefixLift 6609075
  have htrace : WordTrace (prefixWord ++ tailWord_6609075) baseStart_6609075 baseEnd_6609075 := by
    simpa [prefixWord, tailWord_6609075, baseEnd_6609075] using wordTrace_append hprefix tailTrace_6609075
  have hstable : (prefixWord ++ tailWord_6609075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609075).length < 2 ^ (prefixWord ++ tailWord_6609075).sum := by decide
  have hdescent : baseEnd_6609075 < baseStart_6609075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609079 : List Nat := [1, 1, 3, 1, 4, 2, 2, 1, 3, 3, 2]
def baseStart_6609079 : Nat := 118140960795 + 6609079 * 2 ^ 59
def prefixEnd_6609079 : Nat := 4983230072969 + 3 ^ 40 * 6609079 * 2
def baseEnd_6609079 : Nat := 3393634210536452681717905

theorem tailTrace_6609079 : CollatzResearch.WordTrace tailWord_6609079 prefixEnd_6609079 3393634210536452681717905 := by
  unfold tailWord_6609079
  simp only [CollatzResearch.WordTrace]
  refine ⟨241052914423442998674662291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160701942948961999116441527 241052914423442998674662291)
  ·
    refine ⟨361579371635164498011993437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241052914423442998674662291 361579371635164498011993437)
    ·
      refine ⟨135592264363186686754497539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 361579371635164498011993437 135592264363186686754497539)
      ·
        refine ⟨203388396544780030131746309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135592264363186686754497539 203388396544780030131746309)
        ·
          refine ⟨38135324352146255649702433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 203388396544780030131746309 38135324352146255649702433)
          ·
            refine ⟨28601493264109691737276825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38135324352146255649702433 28601493264109691737276825)
            ·
              refine ⟨21451119948082268802957619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28601493264109691737276825 21451119948082268802957619)
              ·
                refine ⟨32176679922123403204436429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21451119948082268802957619 32176679922123403204436429)
                ·
                  refine ⟨12066254970796276201663661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32176679922123403204436429 12066254970796276201663661)
                  ·
                    refine ⟨4524845614048603575623873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12066254970796276201663661 4524845614048603575623873)
                    ·
                      refine ⟨3393634210536452681717905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524845614048603575623873 3393634210536452681717905)
                      ·
                        rfl

theorem cell23_6609079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 3, 2].length) (baseStart_6609079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609079 prefixEnd_6609079 := by exact prefixLift 6609079
  have htrace : WordTrace (prefixWord ++ tailWord_6609079) baseStart_6609079 baseEnd_6609079 := by
    simpa [prefixWord, tailWord_6609079, baseEnd_6609079] using wordTrace_append hprefix tailTrace_6609079
  have hstable : (prefixWord ++ tailWord_6609079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609079).length < 2 ^ (prefixWord ++ tailWord_6609079).sum := by decide
  have hdescent : baseEnd_6609079 < baseStart_6609079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609085 : List Nat := [1, 4, 1, 2, 1, 1, 1, 1, 3, 8]
def baseStart_6609085 : Nat := 118140960795 + 6609085 * 2 ^ 59
def prefixEnd_6609085 : Nat := 4983230072969 + 3 ^ 40 * 6609085 * 2
def baseEnd_6609085 : Nat := 1131212430473459886080959

theorem tailTrace_6609085 : CollatzResearch.WordTrace tailWord_6609085 prefixEnd_6609085 1131212430473459886080959 := by
  unfold tailWord_6609085
  simp only [CollatzResearch.WordTrace]
  refine ⟨241053133261421261699380709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160702088840947507799587139 241053133261421261699380709)
  ·
    refine ⟨45197462486516486568633883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241053133261421261699380709 45197462486516486568633883)
    ·
      refine ⟨67796193729774729852950825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45197462486516486568633883 67796193729774729852950825)
      ·
        refine ⟨50847145297331047389713119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67796193729774729852950825 50847145297331047389713119)
        ·
          refine ⟨76270717945996571084569679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50847145297331047389713119 76270717945996571084569679)
          ·
            refine ⟨114406076918994856626854519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76270717945996571084569679 114406076918994856626854519)
            ·
              refine ⟨171609115378492284940281779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114406076918994856626854519 171609115378492284940281779)
              ·
                refine ⟨257413673067738427410422669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171609115378492284940281779 257413673067738427410422669)
                ·
                  refine ⟨96530127400401910278908501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 257413673067738427410422669 96530127400401910278908501)
                  ·
                    refine ⟨1131212430473459886080959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 96530127400401910278908501 1131212430473459886080959)
                    ·
                      rfl

theorem cell23_6609085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 8].length) (baseStart_6609085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609085 prefixEnd_6609085 := by exact prefixLift 6609085
  have htrace : WordTrace (prefixWord ++ tailWord_6609085) baseStart_6609085 baseEnd_6609085 := by
    simpa [prefixWord, tailWord_6609085, baseEnd_6609085] using wordTrace_append hprefix tailTrace_6609085
  have hstable : (prefixWord ++ tailWord_6609085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609085).length < 2 ^ (prefixWord ++ tailWord_6609085).sum := by decide
  have hdescent : baseEnd_6609085 < baseStart_6609085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609090 : List Nat := [3, 5, 1, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_6609090 : Nat := 118140960795 + 6609090 * 2 ^ 59
def prefixEnd_6609090 : Nat := 4983230072969 + 3 ^ 40 * 6609090 * 2
def baseEnd_6609090 : Nat := 3393639858823652138680355

theorem tailTrace_6609090 : CollatzResearch.WordTrace tailWord_6609090 prefixEnd_6609090 3393639858823652138680355 := by
  unfold tailWord_6609090
  simp only [CollatzResearch.WordTrace]
  refine ⟨60263328906600786888328181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160702210417602098368875149 60263328906600786888328181)
  ·
    refine ⟨5649687084993823770780767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 60263328906600786888328181 5649687084993823770780767)
    ·
      refine ⟨8474530627490735656171151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5649687084993823770780767 8474530627490735656171151)
      ·
        refine ⟨12711795941236103484256727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8474530627490735656171151 12711795941236103484256727)
        ·
          refine ⟨19067693911854155226385091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12711795941236103484256727 19067693911854155226385091)
          ·
            refine ⟨28601540867781232839577637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19067693911854155226385091 28601540867781232839577637)
            ·
              refine ⟨5362788912708981157420807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28601540867781232839577637 5362788912708981157420807)
              ·
                refine ⟨8044183369063471736131211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5362788912708981157420807 8044183369063471736131211)
                ·
                  refine ⟨12066275053595207604196817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8044183369063471736131211 12066275053595207604196817)
                  ·
                    refine ⟨9049706290196405703147613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12066275053595207604196817 9049706290196405703147613)
                    ·
                      refine ⟨3393639858823652138680355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9049706290196405703147613 3393639858823652138680355)
                      ·
                        rfl

theorem cell23_6609090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_6609090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609090 prefixEnd_6609090 := by exact prefixLift 6609090
  have htrace : WordTrace (prefixWord ++ tailWord_6609090) baseStart_6609090 baseEnd_6609090 := by
    simpa [prefixWord, tailWord_6609090, baseEnd_6609090] using wordTrace_append hprefix tailTrace_6609090
  have hstable : (prefixWord ++ tailWord_6609090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609090).length < 2 ^ (prefixWord ++ tailWord_6609090).sum := by decide
  have hdescent : baseEnd_6609090 < baseStart_6609090 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609102 : List Nat := [4, 1, 1, 1, 4, 1, 1, 2, 2, 6]
def baseStart_6609102 : Nat := 118140960795 + 6609102 * 2 ^ 59
def prefixEnd_6609102 : Nat := 4983230072969 + 3 ^ 40 * 6609102 * 2
def baseEnd_6609102 : Nat := 1131215340197168697243433

theorem tailTrace_6609102 : CollatzResearch.WordTrace tailWord_6609102 prefixEnd_6609102 1131215340197168697243433 := by
  unfold tailWord_6609102
  simp only [CollatzResearch.WordTrace]
  refine ⟨30131719162794959200343695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160702502201573115735166373 30131719162794959200343695)
  ·
    refine ⟨45197578744192438800515543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30131719162794959200343695 45197578744192438800515543)
    ·
      refine ⟨67796368116288658200773315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45197578744192438800515543 67796368116288658200773315)
      ·
        refine ⟨101694552174432987301159973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67796368116288658200773315 101694552174432987301159973)
        ·
          refine ⟨19067728532706185118967495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101694552174432987301159973 19067728532706185118967495)
          ·
            refine ⟨28601592799059277678451243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19067728532706185118967495 28601592799059277678451243)
            ·
              refine ⟨42902389198588916517676865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28601592799059277678451243 42902389198588916517676865)
              ·
                refine ⟨32176791898941687388257649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42902389198588916517676865 32176791898941687388257649)
                ·
                  refine ⟨24132593924206265541193237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32176791898941687388257649 24132593924206265541193237)
                  ·
                    refine ⟨1131215340197168697243433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24132593924206265541193237 1131215340197168697243433)
                    ·
                      rfl

theorem cell23_6609102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 2, 2, 6].length) (baseStart_6609102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609102 prefixEnd_6609102 := by exact prefixLift 6609102
  have htrace : WordTrace (prefixWord ++ tailWord_6609102) baseStart_6609102 baseEnd_6609102 := by
    simpa [prefixWord, tailWord_6609102, baseEnd_6609102] using wordTrace_append hprefix tailTrace_6609102
  have hstable : (prefixWord ++ tailWord_6609102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609102).length < 2 ^ (prefixWord ++ tailWord_6609102).sum := by decide
  have hdescent : baseEnd_6609102 < baseStart_6609102 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609115 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 7]
def baseStart_6609115 : Nat := 118140960795 + 6609115 * 2 ^ 59
def prefixEnd_6609115 : Nat := 4983230072969 + 3 ^ 40 * 6609115 * 2
def baseEnd_6609115 : Nat := 377072521760001615651971

theorem tailTrace_6609115 : CollatzResearch.WordTrace tailWord_6609115 prefixEnd_6609115 377072521760001615651971 := by
  unfold tailWord_6609115
  simp only [CollatzResearch.WordTrace]
  refine ⟨241054227451312576822972799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160702818300875051215315199 241054227451312576822972799)
  ·
    refine ⟨361581341176968865234459199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241054227451312576822972799 361581341176968865234459199)
    ·
      refine ⟨542372011765453297851688799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361581341176968865234459199 542372011765453297851688799)
      ·
        refine ⟨813558017648179946777533199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542372011765453297851688799 813558017648179946777533199)
        ·
          refine ⟨1220337026472269920166299799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 813558017648179946777533199 1220337026472269920166299799)
          ·
            refine ⟨1830505539708404880249449699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220337026472269920166299799 1830505539708404880249449699)
            ·
              refine ⟨2745758309562607320374174549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1830505539708404880249449699 2745758309562607320374174549)
              ·
                refine ⟨16088427595093402267817429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2745758309562607320374174549 16088427595093402267817429)
                ·
                  refine ⟨377072521760001615651971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16088427595093402267817429 377072521760001615651971)
                  ·
                    rfl

theorem cell23_6609115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 7].length) (baseStart_6609115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609115 prefixEnd_6609115 := by exact prefixLift 6609115
  have htrace : WordTrace (prefixWord ++ tailWord_6609115) baseStart_6609115 baseEnd_6609115 := by
    simpa [prefixWord, tailWord_6609115, baseEnd_6609115] using wordTrace_append hprefix tailTrace_6609115
  have hstable : (prefixWord ++ tailWord_6609115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609115).length < 2 ^ (prefixWord ++ tailWord_6609115).sum := by decide
  have hdescent : baseEnd_6609115 < baseStart_6609115 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609162 : List Nat := [3, 1, 2, 2, 1, 1, 3, 1, 4, 5]
def baseStart_6609162 : Nat := 118140960795 + 6609162 * 2 ^ 59
def prefixEnd_6609162 : Nat := 4983230072969 + 3 ^ 40 * 6609162 * 2
def baseEnd_6609162 : Nat := 1131225609810258618993341

theorem tailTrace_6609162 : CollatzResearch.WordTrace tailWord_6609162 prefixEnd_6609162 1131225609810258618993341 := by
  unfold tailWord_6609162
  simp only [CollatzResearch.WordTrace]
  refine ⟨60263985420535575962483435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160703961121428202566622493 60263985420535575962483435)
  ·
    refine ⟨90395978130803363943725153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60263985420535575962483435 90395978130803363943725153)
    ·
      refine ⟨67796983598102522957793865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90395978130803363943725153 67796983598102522957793865)
      ·
        refine ⟨50847737698576892218345399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67796983598102522957793865 50847737698576892218345399)
        ·
          refine ⟨76271606547865338327518099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50847737698576892218345399 76271606547865338327518099)
          ·
            refine ⟨114407409821798007491277149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76271606547865338327518099 114407409821798007491277149)
            ·
              refine ⟨42902778683174252809228931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114407409821798007491277149 42902778683174252809228931)
              ·
                refine ⟨64354168024761379213843397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42902778683174252809228931 64354168024761379213843397)
                ·
                  refine ⟨12066406504642758602595637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64354168024761379213843397 12066406504642758602595637)
                  ·
                    refine ⟨1131225609810258618993341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12066406504642758602595637 1131225609810258618993341)
                    ·
                      rfl

theorem cell23_6609162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_6609162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609162 prefixEnd_6609162 := by exact prefixLift 6609162
  have htrace : WordTrace (prefixWord ++ tailWord_6609162) baseStart_6609162 baseEnd_6609162 := by
    simpa [prefixWord, tailWord_6609162, baseEnd_6609162] using wordTrace_append hprefix tailTrace_6609162
  have hstable : (prefixWord ++ tailWord_6609162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609162).length < 2 ^ (prefixWord ++ tailWord_6609162).sum := by decide
  have hdescent : baseEnd_6609162 < baseStart_6609162 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609166 : List Nat := [4, 1, 1, 2, 1, 2, 5, 2, 5]
def baseStart_6609166 : Nat := 118140960795 + 6609166 * 2 ^ 59
def prefixEnd_6609166 : Nat := 4983230072969 + 3 ^ 40 * 6609166 * 2
def baseEnd_6609166 : Nat := 377075431483710426814445

theorem tailTrace_6609166 : CollatzResearch.WordTrace tailWord_6609166 prefixEnd_6609166 377075431483710426814445 := by
  unfold tailWord_6609166
  simp only [CollatzResearch.WordTrace]
  refine ⟨30132010946765976566634919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160704058382751875022052901 30132010946765976566634919)
  ·
    refine ⟨45198016420148964849952379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30132010946765976566634919 45198016420148964849952379)
    ·
      refine ⟨67797024630223447274928569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45198016420148964849952379 67797024630223447274928569)
      ·
        refine ⟨50847768472667585456196427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67797024630223447274928569 50847768472667585456196427)
        ·
          refine ⟨76271652709001378184294641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50847768472667585456196427 76271652709001378184294641)
          ·
            refine ⟨57203739531751033638220981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76271652709001378184294641 57203739531751033638220981)
            ·
              refine ⟨5362850581101659403583217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57203739531751033638220981 5362850581101659403583217)
              ·
                refine ⟨4022137935826244552687413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5362850581101659403583217 4022137935826244552687413)
                ·
                  refine ⟨377075431483710426814445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4022137935826244552687413 377075431483710426814445)
                  ·
                    rfl

theorem cell23_6609166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 5].length) (baseStart_6609166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609166 prefixEnd_6609166 := by exact prefixLift 6609166
  have htrace : WordTrace (prefixWord ++ tailWord_6609166) baseStart_6609166 baseEnd_6609166 := by
    simpa [prefixWord, tailWord_6609166, baseEnd_6609166] using wordTrace_append hprefix tailTrace_6609166
  have hstable : (prefixWord ++ tailWord_6609166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609166).length < 2 ^ (prefixWord ++ tailWord_6609166).sum := by decide
  have hdescent : baseEnd_6609166 < baseStart_6609166 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609212 : List Nat := [2, 2, 2, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_6609212 : Nat := 118140960795 + 6609212 * 2 ^ 59
def prefixEnd_6609212 : Nat := 4983230072969 + 3 ^ 40 * 6609212 * 2
def baseEnd_6609212 : Nat := 3393702503463500661354793

theorem tailTrace_6609212 : CollatzResearch.WordTrace tailWord_6609212 prefixEnd_6609212 3393702503463500661354793 := by
  unfold tailWord_6609212
  simp only [CollatzResearch.WordTrace]
  refine ⟨120528882665980581194626945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160705176887974108259502593 120528882665980581194626945)
  ·
    refine ⟨90396661999485435895970209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120528882665980581194626945 90396661999485435895970209)
    ·
      refine ⟨67797496499614076921977657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90396661999485435895970209 67797496499614076921977657)
      ·
        refine ⟨50848122374710557691483243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67797496499614076921977657 50848122374710557691483243)
        ·
          refine ⟨76272183562065836537224865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50848122374710557691483243 76272183562065836537224865)
          ·
            refine ⟨57204137671549377402918649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76272183562065836537224865 57204137671549377402918649)
            ·
              refine ⟨42903103253662033052188987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57204137671549377402918649 42903103253662033052188987)
              ·
                refine ⟨64354654880493049578283481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42903103253662033052188987 64354654880493049578283481)
                ·
                  refine ⟨48265991160369787183712611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64354654880493049578283481 48265991160369787183712611)
                  ·
                    refine ⟨72398986740554680775568917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48265991160369787183712611 72398986740554680775568917)
                    ·
                      refine ⟨3393702503463500661354793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 72398986740554680775568917 3393702503463500661354793)
                      ·
                        rfl

theorem cell23_6609212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_6609212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609212 prefixEnd_6609212 := by exact prefixLift 6609212
  have htrace : WordTrace (prefixWord ++ tailWord_6609212) baseStart_6609212 baseEnd_6609212 := by
    simpa [prefixWord, tailWord_6609212, baseEnd_6609212] using wordTrace_append hprefix tailTrace_6609212
  have hstable : (prefixWord ++ tailWord_6609212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609212).length < 2 ^ (prefixWord ++ tailWord_6609212).sum := by decide
  have hdescent : baseEnd_6609212 < baseStart_6609212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609219 : List Nat := [1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 3]
def baseStart_6609219 : Nat := 118140960795 + 6609219 * 2 ^ 59
def prefixEnd_6609219 : Nat := 4983230072969 + 3 ^ 40 * 6609219 * 2
def baseEnd_6609219 : Nat := 3393706097828082133967261

theorem tailTrace_6609219 : CollatzResearch.WordTrace tailWord_6609219 prefixEnd_6609219 3393706097828082133967261 := by
  unfold tailWord_6609219
  simp only [CollatzResearch.WordTrace]
  refine ⟨241058020642935802584758711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160705347095290535056505807 241058020642935802584758711)
  ·
    refine ⟨361587030964403703877138067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241058020642935802584758711 361587030964403703877138067)
    ·
      refine ⟨542380546446605555815707101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361587030964403703877138067 542380546446605555815707101)
      ·
        refine ⟨203392704917477083430890163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 542380546446605555815707101 203392704917477083430890163)
        ·
          refine ⟨305089057376215625146335245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203392704917477083430890163 305089057376215625146335245)
          ·
            refine ⟨114408396516080859429875717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305089057376215625146335245 114408396516080859429875717)
            ·
              refine ⟨21451574346765161143101697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114408396516080859429875717 21451574346765161143101697)
              ·
                refine ⟨16088680760073870857326273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21451574346765161143101697 16088680760073870857326273)
                ·
                  refine ⟨12066510570055403142994705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16088680760073870857326273 12066510570055403142994705)
                  ·
                    refine ⟨9049882927541552357246029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12066510570055403142994705 9049882927541552357246029)
                    ·
                      refine ⟨3393706097828082133967261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9049882927541552357246029 3393706097828082133967261)
                      ·
                        rfl

theorem cell23_6609219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_6609219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609219 prefixEnd_6609219 := by exact prefixLift 6609219
  have htrace : WordTrace (prefixWord ++ tailWord_6609219) baseStart_6609219 baseEnd_6609219 := by
    simpa [prefixWord, tailWord_6609219, baseEnd_6609219] using wordTrace_append hprefix tailTrace_6609219
  have hstable : (prefixWord ++ tailWord_6609219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609219).length < 2 ^ (prefixWord ++ tailWord_6609219).sum := by decide
  have hdescent : baseEnd_6609219 < baseStart_6609219 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609259 : List Nat := [1, 1, 1, 1, 2, 2, 2, 5, 1, 5, 2]
def baseStart_6609259 : Nat := 118140960795 + 6609259 * 2 ^ 59
def prefixEnd_6609259 : Nat := 4983230072969 + 3 ^ 40 * 6609259 * 2
def baseEnd_6609259 : Nat := 3393726637054261977467077

theorem tailTrace_6609259 : CollatzResearch.WordTrace tailWord_6609259 prefixEnd_6609259 3393726637054261977467077 := by
  unfold tailWord_6609259
  simp only [CollatzResearch.WordTrace]
  refine ⟨241059479562790889416214831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160706319708527259610809887 241059479562790889416214831)
  ·
    refine ⟨361589219344186334124322247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241059479562790889416214831 361589219344186334124322247)
    ·
      refine ⟨542383829016279501186483371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361589219344186334124322247 542383829016279501186483371)
      ·
        refine ⟨813575743524419251779725057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542383829016279501186483371 813575743524419251779725057)
        ·
          refine ⟨610181807643314438834793793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 813575743524419251779725057 610181807643314438834793793)
          ·
            refine ⟨457636355732485829126095345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610181807643314438834793793 457636355732485829126095345)
            ·
              refine ⟨343227266799364371844571509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 457636355732485829126095345 343227266799364371844571509)
              ·
                refine ⟨32177556262440409860428579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 343227266799364371844571509 32177556262440409860428579)
                ·
                  refine ⟨48266334393660614790642869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32177556262440409860428579 48266334393660614790642869)
                  ·
                    refine ⟨4524968849405682636622769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48266334393660614790642869 4524968849405682636622769)
                    ·
                      refine ⟨3393726637054261977467077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4524968849405682636622769 3393726637054261977467077)
                      ·
                        rfl

theorem cell23_6609259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 5, 2].length) (baseStart_6609259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609259 prefixEnd_6609259 := by exact prefixLift 6609259
  have htrace : WordTrace (prefixWord ++ tailWord_6609259) baseStart_6609259 baseEnd_6609259 := by
    simpa [prefixWord, tailWord_6609259, baseEnd_6609259] using wordTrace_append hprefix tailTrace_6609259
  have hstable : (prefixWord ++ tailWord_6609259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609259).length < 2 ^ (prefixWord ++ tailWord_6609259).sum := by decide
  have hdescent : baseEnd_6609259 < baseStart_6609259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609283 : List Nat := [1, 1, 1, 3, 6, 1, 2, 1, 3, 1, 3]
def baseStart_6609283 : Nat := 118140960795 + 6609283 * 2 ^ 59
def prefixEnd_6609283 : Nat := 4983230072969 + 3 ^ 40 * 6609283 * 2
def baseEnd_6609283 : Nat := 3393738960589969883566967

theorem tailTrace_6609283 : CollatzResearch.WordTrace tailWord_6609283 prefixEnd_6609283 3393738960589969883566967 := by
  unfold tailWord_6609283
  simp only [CollatzResearch.WordTrace]
  refine ⟨241060354914703941515088503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160706903276469294343392335 241060354914703941515088503)
  ·
    refine ⟨361590532372055912272632755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241060354914703941515088503 361590532372055912272632755)
    ·
      refine ⟨542385798558083868408949133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361590532372055912272632755 542385798558083868408949133)
      ·
        refine ⟨203394674459281450653355925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 542385798558083868408949133 203394674459281450653355925)
        ·
          refine ⟨9534125365278817999376059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 203394674459281450653355925 9534125365278817999376059)
          ·
            refine ⟨14301188047918226999064089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9534125365278817999376059 14301188047918226999064089)
            ·
              refine ⟨10725891035938670249298067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14301188047918226999064089 10725891035938670249298067)
              ·
                refine ⟨16088836553908005373947101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10725891035938670249298067 16088836553908005373947101)
                ·
                  refine ⟨6033313707715502015230163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16088836553908005373947101 6033313707715502015230163)
                  ·
                    refine ⟨9049970561573253022845245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6033313707715502015230163 9049970561573253022845245)
                    ·
                      refine ⟨3393738960589969883566967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9049970561573253022845245 3393738960589969883566967)
                      ·
                        rfl

theorem cell23_6609283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_6609283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609283 prefixEnd_6609283 := by exact prefixLift 6609283
  have htrace : WordTrace (prefixWord ++ tailWord_6609283) baseStart_6609283 baseEnd_6609283 := by
    simpa [prefixWord, tailWord_6609283, baseEnd_6609283] using wordTrace_append hprefix tailTrace_6609283
  have hstable : (prefixWord ++ tailWord_6609283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609283).length < 2 ^ (prefixWord ++ tailWord_6609283).sum := by decide
  have hdescent : baseEnd_6609283 < baseStart_6609283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609306 : List Nat := [3, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4]
def baseStart_6609306 : Nat := 118140960795 + 6609306 * 2 ^ 59
def prefixEnd_6609306 : Nat := 4983230072969 + 3 ^ 40 * 6609306 * 2
def baseEnd_6609306 : Nat := 3393750770645023293579361

theorem tailTrace_6609306 : CollatzResearch.WordTrace tailWord_6609306 prefixEnd_6609306 3393750770645023293579361 := by
  unfold tailWord_6609306
  simp only [CollatzResearch.WordTrace]
  refine ⟨60265298448405154110793943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160707462529080410962117181 60265298448405154110793943)
  ·
    refine ⟨90397947672607731166190915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60265298448405154110793943 90397947672607731166190915)
    ·
      refine ⟨135596921508911596749286373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90397947672607731166190915 135596921508911596749286373)
      ·
        refine ⟨25424422782920924390491195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135596921508911596749286373 25424422782920924390491195)
        ·
          refine ⟨38136634174381386585736793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25424422782920924390491195 38136634174381386585736793)
          ·
            refine ⟨28602475630786039939302595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38136634174381386585736793 28602475630786039939302595)
            ·
              refine ⟨42903713446179059908953893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28602475630786039939302595 42903713446179059908953893)
              ·
                refine ⟨8044446271158573732928855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42903713446179059908953893 8044446271158573732928855)
                ·
                  refine ⟨12066669406737860599393283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8044446271158573732928855 12066669406737860599393283)
                  ·
                    refine ⟨18100004110106790899089925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12066669406737860599393283 18100004110106790899089925)
                    ·
                      refine ⟨3393750770645023293579361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18100004110106790899089925 3393750770645023293579361)
                      ·
                        rfl

theorem cell23_6609306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_6609306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609306 prefixEnd_6609306 := by exact prefixLift 6609306
  have htrace : WordTrace (prefixWord ++ tailWord_6609306) baseStart_6609306 baseEnd_6609306 := by
    simpa [prefixWord, tailWord_6609306, baseEnd_6609306] using wordTrace_append hprefix tailTrace_6609306
  have hstable : (prefixWord ++ tailWord_6609306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609306).length < 2 ^ (prefixWord ++ tailWord_6609306).sum := by decide
  have hdescent : baseEnd_6609306 < baseStart_6609306 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609329 : List Nat := [1, 2, 2, 4, 1, 4, 9]
def baseStart_6609329 : Nat := 118140960795 + 6609329 * 2 ^ 59
def prefixEnd_6609329 : Nat := 4983230072969 + 3 ^ 40 * 6609329 * 2
def baseEnd_6609329 : Nat := 41898303465433045723355

theorem tailTrace_6609329 : CollatzResearch.WordTrace tailWord_6609329 prefixEnd_6609329 41898303465433045723355 := by
  unfold tailWord_6609329
  simp only [CollatzResearch.WordTrace]
  refine ⟨241062032672537291371263041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160708021781691527580842027 241062032672537291371263041)
  ·
    refine ⟨180796524504402968528447281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241062032672537291371263041 180796524504402968528447281)
    ·
      refine ⟨135597393378302226396335461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180796524504402968528447281 135597393378302226396335461)
      ·
        refine ⟨25424511258431667449312899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135597393378302226396335461 25424511258431667449312899)
        ·
          refine ⟨38136766887647501173969349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25424511258431667449312899 38136766887647501173969349)
          ·
            refine ⟨7150643791433906470119253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38136766887647501173969349 7150643791433906470119253)
            ·
              refine ⟨41898303465433045723355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7150643791433906470119253 41898303465433045723355)
              ·
                rfl

theorem cell23_6609329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 9].length) (baseStart_6609329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609329 prefixEnd_6609329 := by exact prefixLift 6609329
  have htrace : WordTrace (prefixWord ++ tailWord_6609329) baseStart_6609329 baseEnd_6609329 := by
    simpa [prefixWord, tailWord_6609329, baseEnd_6609329] using wordTrace_append hprefix tailTrace_6609329
  have hstable : (prefixWord ++ tailWord_6609329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609329).length < 2 ^ (prefixWord ++ tailWord_6609329).sum := by decide
  have hdescent : baseEnd_6609329 < baseStart_6609329 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609340 : List Nat := [2, 2, 2, 4, 1, 1, 3, 1, 3, 2, 2]
def baseStart_6609340 : Nat := 118140960795 + 6609340 * 2 ^ 59
def prefixEnd_6609340 : Nat := 4983230072969 + 3 ^ 40 * 6609340 * 2
def baseEnd_6609340 : Nat := 3393768228987276160554205

theorem tailTrace_6609340 : CollatzResearch.WordTrace tailWord_6609340 prefixEnd_6609340 3393768228987276160554205 := by
  unfold tailWord_6609340
  simp only [CollatzResearch.WordTrace]
  refine ⟨120531216937748720124956737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160708289250331626833275649 120531216937748720124956737)
  ·
    refine ⟨90398412703311540093717553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120531216937748720124956737 90398412703311540093717553)
    ·
      refine ⟨67798809527483655070288165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90398412703311540093717553 67798809527483655070288165)
      ·
        refine ⟨12712276786403185325679031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67798809527483655070288165 12712276786403185325679031)
        ·
          refine ⟨19068415179604777988518547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12712276786403185325679031 19068415179604777988518547)
          ·
            refine ⟨28602622769407166982777821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19068415179604777988518547 28602622769407166982777821)
            ·
              refine ⟨10725983538527687618541683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28602622769407166982777821 10725983538527687618541683)
              ·
                refine ⟨16088975307791531427812525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10725983538527687618541683 16088975307791531427812525)
                ·
                  refine ⟨6033365740421824285429697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16088975307791531427812525 6033365740421824285429697)
                  ·
                    refine ⟨4525024305316368214072273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6033365740421824285429697 4525024305316368214072273)
                    ·
                      refine ⟨3393768228987276160554205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4525024305316368214072273 3393768228987276160554205)
                      ·
                        rfl

theorem cell23_6609340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_6609340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609340 prefixEnd_6609340 := by exact prefixLift 6609340
  have htrace : WordTrace (prefixWord ++ tailWord_6609340) baseStart_6609340 baseEnd_6609340 := by
    simpa [prefixWord, tailWord_6609340, baseEnd_6609340] using wordTrace_append hprefix tailTrace_6609340
  have hstable : (prefixWord ++ tailWord_6609340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609340).length < 2 ^ (prefixWord ++ tailWord_6609340).sum := by decide
  have hdescent : baseEnd_6609340 < baseStart_6609340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609390 : List Nat := [4, 1, 2, 1, 2, 3, 2, 2, 2, 1, 3]
def baseStart_6609390 : Nat := 118140960795 + 6609390 * 2 ^ 59
def prefixEnd_6609390 : Nat := 4983230072969 + 3 ^ 40 * 6609390 * 2
def baseEnd_6609390 : Nat := 3393793903020000964928975

theorem tailTrace_6609390 : CollatzResearch.WordTrace tailWord_6609390 prefixEnd_6609390 3393793903020000964928975 := by
  unfold tailWord_6609390
  simp only [CollatzResearch.WordTrace]
  refine ⟨30133032190664537348654203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160709505016877532526155749 30133032190664537348654203)
  ·
    refine ⟨45199548285996806022981305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30133032190664537348654203 45199548285996806022981305)
    ·
      refine ⟨33899661214497604517235979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45199548285996806022981305 33899661214497604517235979)
      ·
        refine ⟨50849491821746406775853969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33899661214497604517235979 50849491821746406775853969)
        ·
          refine ⟨38137118866309805081890477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50849491821746406775853969 38137118866309805081890477)
          ·
            refine ⟨14301419574866176905708929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38137118866309805081890477 14301419574866176905708929)
            ·
              refine ⟨10726064681149632679281697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14301419574866176905708929 10726064681149632679281697)
              ·
                refine ⟨8044548510862224509461273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10726064681149632679281697 8044548510862224509461273)
                ·
                  refine ⟨6033411383146668382095955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8044548510862224509461273 6033411383146668382095955)
                  ·
                    refine ⟨9050117074720002573143933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6033411383146668382095955 9050117074720002573143933)
                    ·
                      refine ⟨3393793903020000964928975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9050117074720002573143933 3393793903020000964928975)
                      ·
                        rfl

theorem cell23_6609390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_6609390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609390 prefixEnd_6609390 := by exact prefixLift 6609390
  have htrace : WordTrace (prefixWord ++ tailWord_6609390) baseStart_6609390 baseEnd_6609390 := by
    simpa [prefixWord, tailWord_6609390, baseEnd_6609390] using wordTrace_append hprefix tailTrace_6609390
  have hstable : (prefixWord ++ tailWord_6609390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609390).length < 2 ^ (prefixWord ++ tailWord_6609390).sum := by decide
  have hdescent : baseEnd_6609390 < baseStart_6609390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609419 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 9]
def baseStart_6609419 : Nat := 118140960795 + 6609419 * 2 ^ 59
def prefixEnd_6609419 : Nat := 4983230072969 + 3 ^ 40 * 6609419 * 2
def baseEnd_6609419 : Nat := 377089865995442372385149

theorem tailTrace_6609419 : CollatzResearch.WordTrace tailWord_6609419 prefixEnd_6609419 377089865995442372385149 := by
  unfold tailWord_6609419
  simp only [CollatzResearch.WordTrace]
  refine ⟨241065315242211236742039311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160710210161474157828026207 241065315242211236742039311)
  ·
    refine ⟨361597972863316855113058967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241065315242211236742039311 361597972863316855113058967)
    ·
      refine ⟨542396959294975282669588451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361597972863316855113058967 542396959294975282669588451)
      ·
        refine ⟨813595438942462924004382677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 542396959294975282669588451 813595438942462924004382677)
        ·
          refine ⟨19068643100213974781352719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 813595438942462924004382677 19068643100213974781352719)
          ·
            refine ⟨28602964650320962172029079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19068643100213974781352719 28602964650320962172029079)
            ·
              refine ⟨42904446975481443258043619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28602964650320962172029079 42904446975481443258043619)
              ·
                refine ⟨64356670463222164887065429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42904446975481443258043619 64356670463222164887065429)
                ·
                  refine ⟨377089865995442372385149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 64356670463222164887065429 377089865995442372385149)
                  ·
                    rfl

theorem cell23_6609419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 9].length) (baseStart_6609419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609419 prefixEnd_6609419 := by exact prefixLift 6609419
  have htrace : WordTrace (prefixWord ++ tailWord_6609419) baseStart_6609419 baseEnd_6609419 := by
    simpa [prefixWord, tailWord_6609419, baseEnd_6609419] using wordTrace_append hprefix tailTrace_6609419
  have hstable : (prefixWord ++ tailWord_6609419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609419).length < 2 ^ (prefixWord ++ tailWord_6609419).sum := by decide
  have hdescent : baseEnd_6609419 < baseStart_6609419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609456 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 1, 7, 2]
def baseStart_6609456 : Nat := 118140960795 + 6609456 * 2 ^ 59
def prefixEnd_6609456 : Nat := 4983230072969 + 3 ^ 40 * 6609456 * 2
def baseEnd_6609456 : Nat := 3393827792743197706703671

theorem tailTrace_6609456 : CollatzResearch.WordTrace tailWord_6609456 prefixEnd_6609456 3393827792743197706703671 := by
  unfold tailWord_6609456
  simp only [CollatzResearch.WordTrace]
  refine ⟨120533332371538596030568111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160711109828718128040757481 120533332371538596030568111)
  ·
    refine ⟨180799998557307894045852167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120533332371538596030568111 180799998557307894045852167)
    ·
      refine ⟨271199997835961841068778251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180799998557307894045852167 271199997835961841068778251)
      ·
        refine ⟨406799996753942761603167377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271199997835961841068778251 406799996753942761603167377)
        ·
          refine ⟨305099997565457071202375533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 406799996753942761603167377 305099997565457071202375533)
          ·
            refine ⟨114412499087046401700890825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 305099997565457071202375533 114412499087046401700890825)
            ·
              refine ⟨85809374315284801275668119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114412499087046401700890825 85809374315284801275668119)
              ·
                refine ⟨128714061472927201913502179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85809374315284801275668119 128714061472927201913502179)
                ·
                  refine ⟨193071092209390802870253269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128714061472927201913502179 193071092209390802870253269)
                  ·
                    refine ⟨4525103723657596942271561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 193071092209390802870253269 4525103723657596942271561)
                    ·
                      refine ⟨3393827792743197706703671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4525103723657596942271561 3393827792743197706703671)
                      ·
                        rfl

theorem cell23_6609456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 1, 7, 2].length) (baseStart_6609456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609456 prefixEnd_6609456 := by exact prefixLift 6609456
  have htrace : WordTrace (prefixWord ++ tailWord_6609456) baseStart_6609456 baseEnd_6609456 := by
    simpa [prefixWord, tailWord_6609456, baseEnd_6609456] using wordTrace_append hprefix tailTrace_6609456
  have hstable : (prefixWord ++ tailWord_6609456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609456).length < 2 ^ (prefixWord ++ tailWord_6609456).sum := by decide
  have hdescent : baseEnd_6609456 < baseStart_6609456 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609459 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 7]
def baseStart_6609459 : Nat := 118140960795 + 6609459 * 2 ^ 59
def prefixEnd_6609459 : Nat := 4983230072969 + 3 ^ 40 * 6609459 * 2
def baseEnd_6609459 : Nat := 3393829333185161194966157

theorem tailTrace_6609459 : CollatzResearch.WordTrace tailWord_6609459 prefixEnd_6609459 3393829333185161194966157 := by
  unfold tailWord_6609459
  simp only [CollatzResearch.WordTrace]
  refine ⟨241066774162066323573495431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160711182774710882382330287 241066774162066323573495431)
  ·
    refine ⟨361600161243099485360243147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241066774162066323573495431 361600161243099485360243147)
    ·
      refine ⟨542400241864649228040364721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361600161243099485360243147 542400241864649228040364721)
      ·
        refine ⟨406800181398486921030273541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542400241864649228040364721 406800181398486921030273541)
        ·
          refine ⟨76275034012216297693176289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 406800181398486921030273541 76275034012216297693176289)
          ·
            refine ⟨57206275509162223269882217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76275034012216297693176289 57206275509162223269882217)
            ·
              refine ⟨42904706631871667452411663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57206275509162223269882217 42904706631871667452411663)
              ·
                refine ⟨64357059947807501178617495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42904706631871667452411663 64357059947807501178617495)
                ·
                  refine ⟨96535589921711251767926243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64357059947807501178617495 96535589921711251767926243)
                  ·
                    refine ⟨144803384882566877651889365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 96535589921711251767926243 144803384882566877651889365)
                    ·
                      refine ⟨3393829333185161194966157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 144803384882566877651889365 3393829333185161194966157)
                      ·
                        rfl

theorem cell23_6609459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_6609459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609459 prefixEnd_6609459 := by exact prefixLift 6609459
  have htrace : WordTrace (prefixWord ++ tailWord_6609459) baseStart_6609459 baseEnd_6609459 := by
    simpa [prefixWord, tailWord_6609459, baseEnd_6609459] using wordTrace_append hprefix tailTrace_6609459
  have hstable : (prefixWord ++ tailWord_6609459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609459).length < 2 ^ (prefixWord ++ tailWord_6609459).sum := by decide
  have hdescent : baseEnd_6609459 < baseStart_6609459 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609486 : List Nat := [4, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4]
def baseStart_6609486 : Nat := 118140960795 + 6609486 * 2 ^ 59
def prefixEnd_6609486 : Nat := 4983230072969 + 3 ^ 40 * 6609486 * 2
def baseEnd_6609486 : Nat := 3393843197162832589328533

theorem tailTrace_6609486 : CollatzResearch.WordTrace tailWord_6609486 prefixEnd_6609486 3393843197162832589328533 := by
  unfold tailWord_6609486
  simp only [CollatzResearch.WordTrace]
  refine ⟨30133469866621063398091039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160711839288645671456485541 30133469866621063398091039)
  ·
    refine ⟨45200204799931595097136559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30133469866621063398091039 45200204799931595097136559)
    ·
      refine ⟨67800307199897392645704839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45200204799931595097136559 67800307199897392645704839)
      ·
        refine ⟨101700460799846088968557259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67800307199897392645704839 101700460799846088968557259)
        ·
          refine ⟨152550691199769133452835889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101700460799846088968557259 152550691199769133452835889)
          ·
            refine ⟨114413018399826850089626917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152550691199769133452835889 114413018399826850089626917)
            ·
              refine ⟨21452440949967534391805047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 114413018399826850089626917 21452440949967534391805047)
              ·
                refine ⟨32178661424951301587707571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21452440949967534391805047 32178661424951301587707571)
                ·
                  refine ⟨48267992137426952381561357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32178661424951301587707571 48267992137426952381561357)
                  ·
                    refine ⟨18100497051535107143085509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48267992137426952381561357 18100497051535107143085509)
                    ·
                      refine ⟨3393843197162832589328533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18100497051535107143085509 3393843197162832589328533)
                      ·
                        rfl

theorem cell23_6609486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_6609486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609486 prefixEnd_6609486 := by exact prefixLift 6609486
  have htrace : WordTrace (prefixWord ++ tailWord_6609486) baseStart_6609486 baseEnd_6609486 := by
    simpa [prefixWord, tailWord_6609486, baseEnd_6609486] using wordTrace_append hprefix tailTrace_6609486
  have hstable : (prefixWord ++ tailWord_6609486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609486).length < 2 ^ (prefixWord ++ tailWord_6609486).sum := by decide
  have hdescent : baseEnd_6609486 < baseStart_6609486 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609496 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 5, 4]
def baseStart_6609496 : Nat := 118140960795 + 6609496 * 2 ^ 59
def prefixEnd_6609496 : Nat := 4983230072969 + 3 ^ 40 * 6609496 * 2
def baseEnd_6609496 : Nat := 1131282777323125850067829

theorem tailTrace_6609496 : CollatzResearch.WordTrace tailWord_6609496 prefixEnd_6609496 1131282777323125850067829 := by
  unfold tailWord_6609496
  simp only [CollatzResearch.WordTrace]
  refine ⟨120534061831466139446296171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160712082441954852595061561 120534061831466139446296171)
  ·
    refine ⟨180801092747199209169444257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120534061831466139446296171 180801092747199209169444257)
    ·
      refine ⟨135600819560399406877083193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180801092747199209169444257 135600819560399406877083193)
      ·
        refine ⟨101700614670299555157812395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 135600819560399406877083193 101700614670299555157812395)
        ·
          refine ⟨152550922005449332736718593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 101700614670299555157812395 152550922005449332736718593)
          ·
            refine ⟨114413191504086999552538945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 152550922005449332736718593 114413191504086999552538945)
            ·
              refine ⟨85809893628065249664404209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114413191504086999552538945 85809893628065249664404209)
              ·
                refine ⟨64357420221048937248303157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85809893628065249664404209 64357420221048937248303157)
                ·
                  refine ⟨6033508145723337867028421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 64357420221048937248303157 6033508145723337867028421)
                  ·
                    refine ⟨1131282777323125850067829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6033508145723337867028421 1131282777323125850067829)
                    ·
                      rfl

theorem cell23_6609496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_6609496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609496 prefixEnd_6609496 := by exact prefixLift 6609496
  have htrace : WordTrace (prefixWord ++ tailWord_6609496) baseStart_6609496 baseEnd_6609496 := by
    simpa [prefixWord, tailWord_6609496, baseEnd_6609496] using wordTrace_append hprefix tailTrace_6609496
  have hstable : (prefixWord ++ tailWord_6609496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609496).length < 2 ^ (prefixWord ++ tailWord_6609496).sum := by decide
  have hdescent : baseEnd_6609496 < baseStart_6609496 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609540 : List Nat := [2, 3, 2, 1, 3, 2, 2, 1, 2, 2, 3]
def baseStart_6609540 : Nat := 118140960795 + 6609540 * 2 ^ 59
def prefixEnd_6609540 : Nat := 4983230072969 + 3 ^ 40 * 6609540 * 2
def baseEnd_6609540 : Nat := 3393870925118175378053285

theorem tailTrace_6609540 : CollatzResearch.WordTrace tailWord_6609540 prefixEnd_6609540 3393870925118175378053285 := by
  unfold tailWord_6609540
  simp only [CollatzResearch.WordTrace]
  refine ⟨120534864237386437203597037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160713152316515249604796049 120534864237386437203597037)
  ·
    refine ⟨45200574089019913951348889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120534864237386437203597037 45200574089019913951348889)
    ·
      refine ⟨33900430566764935463511667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45200574089019913951348889 33900430566764935463511667)
      ·
        refine ⟨50850645850147403195267501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33900430566764935463511667 50850645850147403195267501)
        ·
          refine ⟨19068992193805276198225313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50850645850147403195267501 19068992193805276198225313)
          ·
            refine ⟨14301744145353957148668985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19068992193805276198225313 14301744145353957148668985)
            ·
              refine ⟨10726308109015467861501739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14301744145353957148668985 10726308109015467861501739)
              ·
                refine ⟨16089462163523201792252609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10726308109015467861501739 16089462163523201792252609)
                ·
                  refine ⟨12067096622642401344189457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16089462163523201792252609 12067096622642401344189457)
                  ·
                    refine ⟨9050322466981801008142093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12067096622642401344189457 9050322466981801008142093)
                    ·
                      refine ⟨3393870925118175378053285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9050322466981801008142093 3393870925118175378053285)
                      ·
                        rfl

theorem cell23_6609540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_6609540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609540 prefixEnd_6609540 := by exact prefixLift 6609540
  have htrace : WordTrace (prefixWord ++ tailWord_6609540) baseStart_6609540 baseEnd_6609540 := by
    simpa [prefixWord, tailWord_6609540, baseEnd_6609540] using wordTrace_append hprefix tailTrace_6609540
  have hstable : (prefixWord ++ tailWord_6609540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609540).length < 2 ^ (prefixWord ++ tailWord_6609540).sum := by decide
  have hdescent : baseEnd_6609540 < baseStart_6609540 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609564 : List Nat := [2, 2, 3, 2, 2, 3, 2, 2, 1, 4]
def baseStart_6609564 : Nat := 118140960795 + 6609564 * 2 ^ 59
def prefixEnd_6609564 : Nat := 4983230072969 + 3 ^ 40 * 6609564 * 2
def baseEnd_6609564 : Nat := 1131294416217961094717725

theorem tailTrace_6609564 : CollatzResearch.WordTrace tailWord_6609564 prefixEnd_6609564 1131294416217961094717725 := by
  unfold tailWord_6609564
  simp only [CollatzResearch.WordTrace]
  refine ⟨120535301913342963253033873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160713735884457284337378497 120535301913342963253033873)
  ·
    refine ⟨90401476435007222439775405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120535301913342963253033873 90401476435007222439775405)
    ·
      refine ⟨33900553663127708414915777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90401476435007222439775405 33900553663127708414915777)
      ·
        refine ⟨25425415247345781311186833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33900553663127708414915777 25425415247345781311186833)
        ·
          refine ⟨19069061435509335983390125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25425415247345781311186833 19069061435509335983390125)
          ·
            refine ⟨7150898038316000993771297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19069061435509335983390125 7150898038316000993771297)
            ·
              refine ⟨5363173528737000745328473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7150898038316000993771297 5363173528737000745328473)
              ·
                refine ⟨4022380146552750558996355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5363173528737000745328473 4022380146552750558996355)
                ·
                  refine ⟨6033570219829125838494533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4022380146552750558996355 6033570219829125838494533)
                  ·
                    refine ⟨1131294416217961094717725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6033570219829125838494533 1131294416217961094717725)
                    ·
                      rfl

theorem cell23_6609564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 2, 1, 4].length) (baseStart_6609564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609564 prefixEnd_6609564 := by exact prefixLift 6609564
  have htrace : WordTrace (prefixWord ++ tailWord_6609564) baseStart_6609564 baseEnd_6609564 := by
    simpa [prefixWord, tailWord_6609564, baseEnd_6609564] using wordTrace_append hprefix tailTrace_6609564
  have hstable : (prefixWord ++ tailWord_6609564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609564).length < 2 ^ (prefixWord ++ tailWord_6609564).sum := by decide
  have hdescent : baseEnd_6609564 < baseStart_6609564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609593 : List Nat := [1, 2, 1, 4, 1, 1, 1, 6, 1, 1, 4]
def baseStart_6609593 : Nat := 118140960795 + 6609593 * 2 ^ 59
def prefixEnd_6609593 : Nat := 4983230072969 + 3 ^ 40 * 6609593 * 2
def baseEnd_6609593 : Nat := 3393898139592863670690541

theorem tailTrace_6609593 : CollatzResearch.WordTrace tailWord_6609593 prefixEnd_6609593 3393898139592863670690541 := by
  unfold tailWord_6609593
  simp only [CollatzResearch.WordTrace]
  refine ⟨241071661543580864458873433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160714441029053909639248955 241071661543580864458873433)
  ·
    refine ⟨180803746157685648344155075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241071661543580864458873433 180803746157685648344155075)
    ·
      refine ⟨271205619236528472516232613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180803746157685648344155075 271205619236528472516232613)
      ·
        refine ⟨50851053606849088596793615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271205619236528472516232613 50851053606849088596793615)
        ·
          refine ⟨76276580410273632895190423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50851053606849088596793615 76276580410273632895190423)
          ·
            refine ⟨114414870615410449342785635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76276580410273632895190423 114414870615410449342785635)
            ·
              refine ⟨171622305923115674014178453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114414870615410449342785635 171622305923115674014178453)
              ·
                refine ⟨8044795590146047219414615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 171622305923115674014178453 8044795590146047219414615)
                ·
                  refine ⟨12067193385219070829121923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8044795590146047219414615 12067193385219070829121923)
                  ·
                    refine ⟨18100790077828606243682885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12067193385219070829121923 18100790077828606243682885)
                    ·
                      refine ⟨3393898139592863670690541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18100790077828606243682885 3393898139592863670690541)
                      ·
                        rfl

theorem cell23_6609593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_6609593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609593 prefixEnd_6609593 := by exact prefixLift 6609593
  have htrace : WordTrace (prefixWord ++ tailWord_6609593) baseStart_6609593 baseEnd_6609593 := by
    simpa [prefixWord, tailWord_6609593, baseEnd_6609593] using wordTrace_append hprefix tailTrace_6609593
  have hstable : (prefixWord ++ tailWord_6609593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609593).length < 2 ^ (prefixWord ++ tailWord_6609593).sum := by decide
  have hdescent : baseEnd_6609593 < baseStart_6609593 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609597 : List Nat := [1, 4, 1, 2, 1, 5, 1, 1, 2, 3, 2]
def baseStart_6609597 : Nat := 118140960795 + 6609597 * 2 ^ 59
def prefixEnd_6609597 : Nat := 4983230072969 + 3 ^ 40 * 6609597 * 2
def baseEnd_6609597 : Nat := 3393900193515481655040523

theorem tailTrace_6609597 : CollatzResearch.WordTrace tailWord_6609597 prefixEnd_6609597 3393900193515481655040523 := by
  unfold tailWord_6609597
  simp only [CollatzResearch.WordTrace]
  refine ⟨241071807435566373142019045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160714538290377582094679363 241071807435566373142019045)
  ·
    refine ⟨45200963894168694964128571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 241071807435566373142019045 45200963894168694964128571)
    ·
      refine ⟨67801445841253042446192857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45200963894168694964128571 67801445841253042446192857)
      ·
        refine ⟨50851084380939781834644643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67801445841253042446192857 50851084380939781834644643)
        ·
          refine ⟨76276626571409672751966965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50851084380939781834644643 76276626571409672751966965)
          ·
            refine ⟨7150933741069656820496903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76276626571409672751966965 7150933741069656820496903)
            ·
              refine ⟨10726400611604485230745355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7150933741069656820496903 10726400611604485230745355)
              ·
                refine ⟨16089600917406727846118033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10726400611604485230745355 16089600917406727846118033)
                ·
                  refine ⟨12067200688055045884588525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16089600917406727846118033 12067200688055045884588525)
                  ·
                    refine ⟨4525200258020642206720697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12067200688055045884588525 4525200258020642206720697)
                    ·
                      refine ⟨3393900193515481655040523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4525200258020642206720697 3393900193515481655040523)
                      ·
                        rfl

theorem cell23_6609597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_6609597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609597 prefixEnd_6609597 := by exact prefixLift 6609597
  have htrace : WordTrace (prefixWord ++ tailWord_6609597) baseStart_6609597 baseEnd_6609597 := by
    simpa [prefixWord, tailWord_6609597, baseEnd_6609597] using wordTrace_append hprefix tailTrace_6609597
  have hstable : (prefixWord ++ tailWord_6609597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609597).length < 2 ^ (prefixWord ++ tailWord_6609597).sum := by decide
  have hdescent : baseEnd_6609597 < baseStart_6609597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609604 : List Nat := [2, 3, 3, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_6609604 : Nat := 118140960795 + 6609604 * 2 ^ 59
def prefixEnd_6609604 : Nat := 4983230072969 + 3 ^ 40 * 6609604 * 2
def baseEnd_6609604 : Nat := 3393903787880063127652991

theorem tailTrace_6609604 : CollatzResearch.WordTrace tailWord_6609604 prefixEnd_6609604 3393903787880063127652991 := by
  unfold tailWord_6609604
  simp only [CollatzResearch.WordTrace]
  refine ⟨120536031373270506668761933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160714708497694008891682577 120536031373270506668761933)
  ·
    refine ⟨45201011764976440000785725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120536031373270506668761933 45201011764976440000785725)
    ·
      refine ⟨16950379411866165000294647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45201011764976440000785725 16950379411866165000294647)
      ·
        refine ⟨25425569117799247500441971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16950379411866165000294647 25425569117799247500441971)
        ·
          refine ⟨38138353676698871250662957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25425569117799247500441971 38138353676698871250662957)
          ·
            refine ⟨14301882628762076718998609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38138353676698871250662957 14301882628762076718998609)
            ·
              refine ⟨10726411971571557539248957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14301882628762076718998609 10726411971571557539248957)
              ·
                refine ⟨4022404489339334077218359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10726411971571557539248957 4022404489339334077218359)
                ·
                  refine ⟨6033606734009001115827539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4022404489339334077218359 6033606734009001115827539)
                  ·
                    refine ⟨9050410101013501673741309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6033606734009001115827539 9050410101013501673741309)
                    ·
                      refine ⟨3393903787880063127652991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9050410101013501673741309 3393903787880063127652991)
                      ·
                        rfl

theorem cell23_6609604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_6609604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609604 prefixEnd_6609604 := by exact prefixLift 6609604
  have htrace : WordTrace (prefixWord ++ tailWord_6609604) baseStart_6609604 baseEnd_6609604 := by
    simpa [prefixWord, tailWord_6609604, baseEnd_6609604] using wordTrace_append hprefix tailTrace_6609604
  have hstable : (prefixWord ++ tailWord_6609604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609604).length < 2 ^ (prefixWord ++ tailWord_6609604).sum := by decide
  have hdescent : baseEnd_6609604 < baseStart_6609604 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609610 : List Nat := [3, 1, 2, 1, 4, 2, 1, 3, 1, 1, 4]
def baseStart_6609610 : Nat := 118140960795 + 6609610 * 2 ^ 59
def prefixEnd_6609610 : Nat := 4983230072969 + 3 ^ 40 * 6609610 * 2
def baseEnd_6609610 : Nat := 3393906868763990104177963

theorem tailTrace_6609610 : CollatzResearch.WordTrace tailWord_6609610 prefixEnd_6609610 3393906868763990104177963 := by
  unfold tailWord_6609610
  simp only [CollatzResearch.WordTrace]
  refine ⟨60268070396129819090560571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160714854389679517574828189 60268070396129819090560571)
  ·
    refine ⟨90402105594194728635840857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60268070396129819090560571 90402105594194728635840857)
    ·
      refine ⟨67801579195646046476880643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90402105594194728635840857 67801579195646046476880643)
      ·
        refine ⟨101702368793469069715320965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67801579195646046476880643 101702368793469069715320965)
        ·
          refine ⟨19069194148775450571622681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 101702368793469069715320965 19069194148775450571622681)
          ·
            refine ⟨14301895611581587928717011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19069194148775450571622681 14301895611581587928717011)
            ·
              refine ⟨21452843417372381893075517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14301895611581587928717011 21452843417372381893075517)
              ·
                refine ⟨8044816281514643209903319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21452843417372381893075517 8044816281514643209903319)
                ·
                  refine ⟨12067224422271964814854979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8044816281514643209903319 12067224422271964814854979)
                  ·
                    refine ⟨18100836633407947222282469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12067224422271964814854979 18100836633407947222282469)
                    ·
                      refine ⟨3393906868763990104177963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18100836633407947222282469 3393906868763990104177963)
                      ·
                        rfl

theorem cell23_6609610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_6609610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609610 prefixEnd_6609610 := by exact prefixLift 6609610
  have htrace : WordTrace (prefixWord ++ tailWord_6609610) baseStart_6609610 baseEnd_6609610 := by
    simpa [prefixWord, tailWord_6609610, baseEnd_6609610] using wordTrace_append hprefix tailTrace_6609610
  have hstable : (prefixWord ++ tailWord_6609610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609610).length < 2 ^ (prefixWord ++ tailWord_6609610).sum := by decide
  have hdescent : baseEnd_6609610 < baseStart_6609610 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609637 : List Nat := [1, 3, 1, 4, 1, 3, 3, 1, 2, 4]
def baseStart_6609637 : Nat := 118140960795 + 6609637 * 2 ^ 59
def prefixEnd_6609637 : Nat := 4983230072969 + 3 ^ 40 * 6609637 * 2
def baseEnd_6609637 : Nat := 1131306910913887166180113

theorem tailTrace_6609637 : CollatzResearch.WordTrace tailWord_6609637 prefixEnd_6609637 1131306910913887166180113 := by
  unfold tailWord_6609637
  simp only [CollatzResearch.WordTrace]
  refine ⟨241073266355421459973475165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160715510903614306648983443 241073266355421459973475165)
  ·
    refine ⟨90402474883283047490053187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241073266355421459973475165 90402474883283047490053187)
    ·
      refine ⟨135603712324924571235079781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90402474883283047490053187 135603712324924571235079781)
      ·
        refine ⟨25425696060923357106577459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 135603712324924571235079781 25425696060923357106577459)
        ·
          refine ⟨38138544091385035659866189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25425696060923357106577459 38138544091385035659866189)
          ·
            refine ⟨14301954034269388372449821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38138544091385035659866189 14301954034269388372449821)
            ·
              refine ⟨5363232762851020639668683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14301954034269388372449821 5363232762851020639668683)
              ·
                refine ⟨8044849144276530959503025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363232762851020639668683 8044849144276530959503025)
                ·
                  refine ⟨6033636858207398219627269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8044849144276530959503025 6033636858207398219627269)
                  ·
                    refine ⟨1131306910913887166180113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6033636858207398219627269 1131306910913887166180113)
                    ·
                      rfl

theorem cell23_6609637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 2, 4].length) (baseStart_6609637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609637 prefixEnd_6609637 := by exact prefixLift 6609637
  have htrace : WordTrace (prefixWord ++ tailWord_6609637) baseStart_6609637 baseEnd_6609637 := by
    simpa [prefixWord, tailWord_6609637, baseEnd_6609637] using wordTrace_append hprefix tailTrace_6609637
  have hstable : (prefixWord ++ tailWord_6609637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609637).length < 2 ^ (prefixWord ++ tailWord_6609637).sum := by decide
  have hdescent : baseEnd_6609637 < baseStart_6609637 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609650 : List Nat := [3, 2, 1, 3, 1, 4, 2, 7]
def baseStart_6609650 : Nat := 118140960795 + 6609650 * 2 ^ 59
def prefixEnd_6609650 : Nat := 4983230072969 + 3 ^ 40 * 6609650 * 2
def baseEnd_6609650 : Nat := 125701015110747035099177

theorem tailTrace_6609650 : CollatzResearch.WordTrace tailWord_6609650 prefixEnd_6609650 125701015110747035099177 := by
  unfold tailWord_6609650
  simp only [CollatzResearch.WordTrace]
  refine ⟨60268435126093590798424601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 160715827002916242129132269 60268435126093590798424601)
  ·
    refine ⟨45201326344570193098818451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60268435126093590798424601 45201326344570193098818451)
    ·
      refine ⟨67801989516855289648227677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45201326344570193098818451 67801989516855289648227677)
      ·
        refine ⟨25425746068820733618085379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67801989516855289648227677 25425746068820733618085379)
        ·
          refine ⟨38138619103231100427128069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25425746068820733618085379 38138619103231100427128069)
          ·
            refine ⟨7150991081855831330086513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38138619103231100427128069 7150991081855831330086513)
            ·
              refine ⟨5363243311391873497564885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7150991081855831330086513 5363243311391873497564885)
              ·
                refine ⟨125701015110747035099177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5363243311391873497564885 125701015110747035099177)
                ·
                  rfl

theorem cell23_6609650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 4, 2, 7].length) (baseStart_6609650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609650 prefixEnd_6609650 := by exact prefixLift 6609650
  have htrace : WordTrace (prefixWord ++ tailWord_6609650) baseStart_6609650 baseEnd_6609650 := by
    simpa [prefixWord, tailWord_6609650, baseEnd_6609650] using wordTrace_append hprefix tailTrace_6609650
  have hstable : (prefixWord ++ tailWord_6609650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609650).length < 2 ^ (prefixWord ++ tailWord_6609650).sum := by decide
  have hdescent : baseEnd_6609650 < baseStart_6609650 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609656 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_6609656 : Nat := 118140960795 + 6609656 * 2 ^ 59
def prefixEnd_6609656 : Nat := 4983230072969 + 3 ^ 40 * 6609656 * 2
def baseEnd_6609656 : Nat := 3393930488874096924202751

theorem tailTrace_6609656 : CollatzResearch.WordTrace tailWord_6609656 prefixEnd_6609656 3393930488874096924202751 := by
  unfold tailWord_6609656
  simp only [CollatzResearch.WordTrace]
  refine ⟨120536979671176313109208411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160715972894901750812277881 120536979671176313109208411)
  ·
    refine ⟨180805469506764469663812617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120536979671176313109208411 180805469506764469663812617)
    ·
      refine ⟨135604102130073352247859463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180805469506764469663812617 135604102130073352247859463)
      ·
        refine ⟨203406153195110028371789195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135604102130073352247859463 203406153195110028371789195)
        ·
          refine ⟨305109229792665042557683793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203406153195110028371789195 305109229792665042557683793)
          ·
            refine ⟨228831922344498781918262845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305109229792665042557683793 228831922344498781918262845)
            ·
              refine ⟨85811970879187043219348567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 228831922344498781918262845 85811970879187043219348567)
              ·
                refine ⟨128717956318780564829022851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85811970879187043219348567 128717956318780564829022851)
                ·
                  refine ⟨193076934478170847243534277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128717956318780564829022851 193076934478170847243534277)
                  ·
                    refine ⟨36201925214657033858162677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 193076934478170847243534277 36201925214657033858162677)
                    ·
                      refine ⟨3393930488874096924202751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 36201925214657033858162677 3393930488874096924202751)
                      ·
                        rfl

theorem cell23_6609656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_6609656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609656 prefixEnd_6609656 := by exact prefixLift 6609656
  have htrace : WordTrace (prefixWord ++ tailWord_6609656) baseStart_6609656 baseEnd_6609656 := by
    simpa [prefixWord, tailWord_6609656, baseEnd_6609656] using wordTrace_append hprefix tailTrace_6609656
  have hstable : (prefixWord ++ tailWord_6609656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609656).length < 2 ^ (prefixWord ++ tailWord_6609656).sum := by decide
  have hdescent : baseEnd_6609656 < baseStart_6609656 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609660 : List Nat := [2, 2, 2, 1, 3, 2, 1, 2, 4, 1, 3]
def baseStart_6609660 : Nat := 118140960795 + 6609660 * 2 ^ 59
def prefixEnd_6609660 : Nat := 4983230072969 + 3 ^ 40 * 6609660 * 2
def baseEnd_6609660 : Nat := 3393932542796714908552733

theorem tailTrace_6609660 : CollatzResearch.WordTrace tailWord_6609660 prefixEnd_6609660 3393932542796714908552733 := by
  unfold tailWord_6609660
  simp only [CollatzResearch.WordTrace]
  refine ⟨120537052617169067450781217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160716070156225423267708289 120537052617169067450781217)
  ·
    refine ⟨90402789462876800588085913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120537052617169067450781217 90402789462876800588085913)
    ·
      refine ⟨67802092097157600441064435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90402789462876800588085913 67802092097157600441064435)
      ·
        refine ⟨101703138145736400661596653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67802092097157600441064435 101703138145736400661596653)
        ·
          refine ⟨38138676804651150248098745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101703138145736400661596653 38138676804651150248098745)
          ·
            refine ⟨28604007603488362686074059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38138676804651150248098745 28604007603488362686074059)
            ·
              refine ⟨42906011405232544029111089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28604007603488362686074059 42906011405232544029111089)
              ·
                refine ⟨32179508553924408021833317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42906011405232544029111089 32179508553924408021833317)
                ·
                  refine ⟨6033657853860826504093747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32179508553924408021833317 6033657853860826504093747)
                  ·
                    refine ⟨9050486780791239756140621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6033657853860826504093747 9050486780791239756140621)
                    ·
                      refine ⟨3393932542796714908552733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9050486780791239756140621 3393932542796714908552733)
                      ·
                        rfl

theorem cell23_6609660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_6609660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609660 prefixEnd_6609660 := by exact prefixLift 6609660
  have htrace : WordTrace (prefixWord ++ tailWord_6609660) baseStart_6609660 baseEnd_6609660 := by
    simpa [prefixWord, tailWord_6609660, baseEnd_6609660] using wordTrace_append hprefix tailTrace_6609660
  have hstable : (prefixWord ++ tailWord_6609660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609660).length < 2 ^ (prefixWord ++ tailWord_6609660).sum := by decide
  have hdescent : baseEnd_6609660 < baseStart_6609660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609717 : List Nat := [1, 3, 3, 1, 3, 2, 1, 2, 1, 4, 2]
def baseStart_6609717 : Nat := 118140960795 + 6609717 * 2 ^ 59
def prefixEnd_6609717 : Nat := 4983230072969 + 3 ^ 40 * 6609717 * 2
def baseEnd_6609717 : Nat := 3393961811194021185539971

theorem tailTrace_6609717 : CollatzResearch.WordTrace tailWord_6609717 prefixEnd_6609717 3393961811194021185539971 := by
  unfold tailWord_6609717
  simp only [CollatzResearch.WordTrace]
  refine ⟨241076184195131633636387405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160717456130087755757591603 241076184195131633636387405)
  ·
    refine ⟨90403569073174362613645277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241076184195131633636387405 90403569073174362613645277)
    ·
      refine ⟨33901338402440385980116979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90403569073174362613645277 33901338402440385980116979)
      ·
        refine ⟨50852007603660578970175469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33901338402440385980116979 50852007603660578970175469)
        ·
          refine ⟨19069502851372717113815801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50852007603660578970175469 19069502851372717113815801)
          ·
            refine ⟨14302127138529537835361851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19069502851372717113815801 14302127138529537835361851)
            ·
              refine ⟨21453190707794306753042777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14302127138529537835361851 21453190707794306753042777)
              ·
                refine ⟨16089893030845730064782083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21453190707794306753042777 16089893030845730064782083)
                ·
                  refine ⟨24134839546268595097173125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16089893030845730064782083 24134839546268595097173125)
                  ·
                    refine ⟨4525282414925361580719961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24134839546268595097173125 4525282414925361580719961)
                    ·
                      refine ⟨3393961811194021185539971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4525282414925361580719961 3393961811194021185539971)
                      ·
                        rfl

theorem cell23_6609717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 4, 2].length) (baseStart_6609717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609717 prefixEnd_6609717 := by exact prefixLift 6609717
  have htrace : WordTrace (prefixWord ++ tailWord_6609717) baseStart_6609717 baseEnd_6609717 := by
    simpa [prefixWord, tailWord_6609717, baseEnd_6609717] using wordTrace_append hprefix tailTrace_6609717
  have hstable : (prefixWord ++ tailWord_6609717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609717).length < 2 ^ (prefixWord ++ tailWord_6609717).sum := by decide
  have hdescent : baseEnd_6609717 < baseStart_6609717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609760 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 2, 5, 2]
def baseStart_6609760 : Nat := 118140960795 + 6609760 * 2 ^ 59
def prefixEnd_6609760 : Nat := 4983230072969 + 3 ^ 40 * 6609760 * 2
def baseEnd_6609760 : Nat := 3393983890862164517302273

theorem tailTrace_6609760 : CollatzResearch.WordTrace tailWord_6609760 prefixEnd_6609760 3393983890862164517302273 := by
  unfold tailWord_6609760
  simp only [CollatzResearch.WordTrace]
  refine ⟨120538876266987925990101367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160718501689317234653468489 120538876266987925990101367)
  ·
    refine ⟨180808314400481888985152051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120538876266987925990101367 180808314400481888985152051)
    ·
      refine ⟨271212471600722833477728077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180808314400481888985152051 271212471600722833477728077)
      ·
        refine ⟨101704676850271062554148029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 271212471600722833477728077 101704676850271062554148029)
        ·
          refine ⟨38139253818851648457805511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101704676850271062554148029 38139253818851648457805511)
          ·
            refine ⟨57208880728277472686708267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38139253818851648457805511 57208880728277472686708267)
            ·
              refine ⟨85813321092416209030062401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57208880728277472686708267 85813321092416209030062401)
              ·
                refine ⟨64359990819312156772546801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 85813321092416209030062401 64359990819312156772546801)
                ·
                  refine ⟨48269993114484117579410101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 64359990819312156772546801 48269993114484117579410101)
                  ·
                    refine ⟨4525311854482886023069697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48269993114484117579410101 4525311854482886023069697)
                    ·
                      refine ⟨3393983890862164517302273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4525311854482886023069697 3393983890862164517302273)
                      ·
                        rfl

theorem cell23_6609760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 2, 5, 2].length) (baseStart_6609760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609760 prefixEnd_6609760 := by exact prefixLift 6609760
  have htrace : WordTrace (prefixWord ++ tailWord_6609760) baseStart_6609760 baseEnd_6609760 := by
    simpa [prefixWord, tailWord_6609760, baseEnd_6609760] using wordTrace_append hprefix tailTrace_6609760
  have hstable : (prefixWord ++ tailWord_6609760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609760).length < 2 ^ (prefixWord ++ tailWord_6609760).sum := by decide
  have hdescent : baseEnd_6609760 < baseStart_6609760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609774 : List Nat := [4, 1, 2, 3, 2, 1, 2, 3, 5]
def baseStart_6609774 : Nat := 118140960795 + 6609774 * 2 ^ 59
def prefixEnd_6609774 : Nat := 4983230072969 + 3 ^ 40 * 6609774 * 2
def baseEnd_6609774 : Nat := 377110119954591940280801

theorem tailTrace_6609774 : CollatzResearch.WordTrace tailWord_6609774 prefixEnd_6609774 377110119954591940280801 := by
  unfold tailWord_6609774
  simp only [CollatzResearch.WordTrace]
  refine ⟨30134782894490641546401547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 160718842103950088247474917 30134782894490641546401547)
  ·
    refine ⟨45202174341735962319602321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30134782894490641546401547 45202174341735962319602321)
    ·
      refine ⟨33901630756301971739701741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45202174341735962319602321 33901630756301971739701741)
      ·
        refine ⟨12713111533613239402388153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33901630756301971739701741 12713111533613239402388153)
        ·
          refine ⟨9534833650209929551791115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12713111533613239402388153 9534833650209929551791115)
          ·
            refine ⟨14302250475314894327686673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9534833650209929551791115 14302250475314894327686673)
            ·
              refine ⟨10726687856486170745765005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14302250475314894327686673 10726687856486170745765005)
              ·
                refine ⟨4022507946182314029661877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10726687856486170745765005 4022507946182314029661877)
                ·
                  refine ⟨377110119954591940280801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4022507946182314029661877 377110119954591940280801)
                  ·
                    rfl

theorem cell23_6609774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 2, 3, 5].length) (baseStart_6609774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609774 prefixEnd_6609774 := by exact prefixLift 6609774
  have htrace : WordTrace (prefixWord ++ tailWord_6609774) baseStart_6609774 baseEnd_6609774 := by
    simpa [prefixWord, tailWord_6609774, baseEnd_6609774] using wordTrace_append hprefix tailTrace_6609774
  have hstable : (prefixWord ++ tailWord_6609774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609774).length < 2 ^ (prefixWord ++ tailWord_6609774).sum := by decide
  have hdescent : baseEnd_6609774 < baseStart_6609774 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609844 : List Nat := [2, 5, 2, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_6609844 : Nat := 118140960795 + 6609844 * 2 ^ 59
def prefixEnd_6609844 : Nat := 4983230072969 + 3 ^ 40 * 6609844 * 2
def baseEnd_6609844 : Nat := 3394027023237142188651887

theorem tailTrace_6609844 : CollatzResearch.WordTrace tailWord_6609844 prefixEnd_6609844 3394027023237142188651887 := by
  unfold tailWord_6609844
  simp only [CollatzResearch.WordTrace]
  refine ⟨120540408132835767163130293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160720544177114356217507057 120540408132835767163130293)
  ·
    refine ⟨11300663262453353171543465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 120540408132835767163130293 11300663262453353171543465)
    ·
      refine ⟨8475497446840014878657599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11300663262453353171543465 8475497446840014878657599)
      ·
        refine ⟨12713246170260022317986399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8475497446840014878657599 12713246170260022317986399)
        ·
          refine ⟨19069869255390033476979599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12713246170260022317986399 19069869255390033476979599)
          ·
            refine ⟨28604803883085050215469399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19069869255390033476979599 28604803883085050215469399)
            ·
              refine ⟨42907205824627575323204099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28604803883085050215469399 42907205824627575323204099)
              ·
                refine ⟨64360808736941362984806149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42907205824627575323204099 64360808736941362984806149)
                ·
                  refine ⟨12067651638176505559651153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 64360808736941362984806149 12067651638176505559651153)
                  ·
                    refine ⟨9050738728632379169738365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12067651638176505559651153 9050738728632379169738365)
                    ·
                      refine ⟨3394027023237142188651887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9050738728632379169738365 3394027023237142188651887)
                      ·
                        rfl

theorem cell23_6609844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_6609844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609844 prefixEnd_6609844 := by exact prefixLift 6609844
  have htrace : WordTrace (prefixWord ++ tailWord_6609844) baseStart_6609844 baseEnd_6609844 := by
    simpa [prefixWord, tailWord_6609844, baseEnd_6609844] using wordTrace_append hprefix tailTrace_6609844
  have hstable : (prefixWord ++ tailWord_6609844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609844).length < 2 ^ (prefixWord ++ tailWord_6609844).sum := by decide
  have hdescent : baseEnd_6609844 < baseStart_6609844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609864 : List Nat := [2, 1, 3, 1, 5, 2, 2, 1, 6]
def baseStart_6609864 : Nat := 118140960795 + 6609864 * 2 ^ 59
def prefixEnd_6609864 : Nat := 4983230072969 + 3 ^ 40 * 6609864 * 2
def baseEnd_6609864 : Nat := 377115254761136901155755

theorem tailTrace_6609864 : CollatzResearch.WordTrace tailWord_6609864 prefixEnd_6609864 377115254761136901155755 := by
  unfold tailWord_6609864
  simp only [CollatzResearch.WordTrace]
  refine ⟨120540772862799538870994323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160721030483732718494659097 120540772862799538870994323)
  ·
    refine ⟨180811159294199308306491485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120540772862799538870994323 180811159294199308306491485)
    ·
      refine ⟨67804184735324740614934307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 180811159294199308306491485 67804184735324740614934307)
      ·
        refine ⟨101706277102987110922401461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67804184735324740614934307 101706277102987110922401461)
        ·
          refine ⟨9534963478405041648975137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 101706277102987110922401461 9534963478405041648975137)
          ·
            refine ⟨7151222608803781236731353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9534963478405041648975137 7151222608803781236731353)
            ·
              refine ⟨5363416956602835927548515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7151222608803781236731353 5363416956602835927548515)
              ·
                refine ⟨8045125434904253891322773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363416956602835927548515 8045125434904253891322773)
                ·
                  refine ⟨377115254761136901155755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8045125434904253891322773 377115254761136901155755)
                  ·
                    rfl

theorem cell23_6609864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 6].length) (baseStart_6609864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609864 prefixEnd_6609864 := by exact prefixLift 6609864
  have htrace : WordTrace (prefixWord ++ tailWord_6609864) baseStart_6609864 baseEnd_6609864 := by
    simpa [prefixWord, tailWord_6609864, baseEnd_6609864] using wordTrace_append hprefix tailTrace_6609864
  have hstable : (prefixWord ++ tailWord_6609864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609864).length < 2 ^ (prefixWord ++ tailWord_6609864).sum := by decide
  have hdescent : baseEnd_6609864 < baseStart_6609864 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609877 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 3, 5]
def baseStart_6609877 : Nat := 118140960795 + 6609877 * 2 ^ 59
def prefixEnd_6609877 : Nat := 4983230072969 + 3 ^ 40 * 6609877 * 2
def baseEnd_6609877 : Nat := 1131347989366246853179745

theorem tailTrace_6609877 : CollatzResearch.WordTrace tailWord_6609877 prefixEnd_6609877 1131347989366246853179745 := by
  unfold tailWord_6609877
  simp only [CollatzResearch.WordTrace]
  refine ⟨241082019874551980962211885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160721346583034653974807923 241082019874551980962211885)
  ·
    refine ⟨90405757452956992860829457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241082019874551980962211885 90405757452956992860829457)
    ·
      refine ⟨67804318089717744645622093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 90405757452956992860829457 67804318089717744645622093)
      ·
        refine ⟨25426619283644154242108285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67804318089717744645622093 25426619283644154242108285)
        ·
          refine ⟨9534982231366557840790607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25426619283644154242108285 9534982231366557840790607)
          ·
            refine ⟨14302473347049836761185911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9534982231366557840790607 14302473347049836761185911)
            ·
              refine ⟨21453710020574755141778867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14302473347049836761185911 21453710020574755141778867)
              ·
                refine ⟨32180565030862132712668301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21453710020574755141778867 32180565030862132712668301)
                ·
                  refine ⟨12067711886573299767250613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32180565030862132712668301 12067711886573299767250613)
                  ·
                    refine ⟨1131347989366246853179745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12067711886573299767250613 1131347989366246853179745)
                    ·
                      rfl

theorem cell23_6609877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 3, 5].length) (baseStart_6609877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609877 prefixEnd_6609877 := by exact prefixLift 6609877
  have htrace : WordTrace (prefixWord ++ tailWord_6609877) baseStart_6609877 baseEnd_6609877 := by
    simpa [prefixWord, tailWord_6609877, baseEnd_6609877] using wordTrace_append hprefix tailTrace_6609877
  have hstable : (prefixWord ++ tailWord_6609877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609877).length < 2 ^ (prefixWord ++ tailWord_6609877).sum := by decide
  have hdescent : baseEnd_6609877 < baseStart_6609877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609903 : List Nat := [1, 1, 2, 1, 4, 14]
def baseStart_6609903 : Nat := 118140960795 + 6609903 * 2 ^ 59
def prefixEnd_6609903 : Nat := 4983230072969 + 3 ^ 40 * 6609903 * 2
def baseEnd_6609903 : Nat := 13967314068295298180305

theorem tailTrace_6609903 : CollatzResearch.WordTrace tailWord_6609903 prefixEnd_6609903 13967314068295298180305 := by
  unfold tailWord_6609903
  simp only [CollatzResearch.WordTrace]
  refine ⟨241082968172457787402658363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160721978781638524935105575 241082968172457787402658363)
  ·
    refine ⟨361624452258686681103987545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241082968172457787402658363 361624452258686681103987545)
    ·
      refine ⟨271218339194015010827990659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361624452258686681103987545 271218339194015010827990659)
      ·
        refine ⟨406827508791022516241985989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271218339194015010827990659 406827508791022516241985989)
        ·
          refine ⟨76280157898316721795372373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 406827508791022516241985989 76280157898316721795372373)
          ·
            refine ⟨13967314068295298180305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 76280157898316721795372373 13967314068295298180305)
            ·
              rfl

theorem cell23_6609903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 14].length) (baseStart_6609903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609903 prefixEnd_6609903 := by exact prefixLift 6609903
  have htrace : WordTrace (prefixWord ++ tailWord_6609903) baseStart_6609903 baseEnd_6609903 := by
    simpa [prefixWord, tailWord_6609903, baseEnd_6609903] using wordTrace_append hprefix tailTrace_6609903
  have hstable : (prefixWord ++ tailWord_6609903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609903).length < 2 ^ (prefixWord ++ tailWord_6609903).sum := by decide
  have hdescent : baseEnd_6609903 < baseStart_6609903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609927 : List Nat := [1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_6609927 : Nat := 118140960795 + 6609927 * 2 ^ 59
def prefixEnd_6609927 : Nat := 4983230072969 + 3 ^ 40 * 6609927 * 2
def baseEnd_6609927 : Nat := 3394069642131465363914005

theorem tailTrace_6609927 : CollatzResearch.WordTrace tailWord_6609927 prefixEnd_6609927 3394069642131465363914005 := by
  unfold tailWord_6609927
  simp only [CollatzResearch.WordTrace]
  refine ⟨241083843524370839501532035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160722562349580559667688023 241083843524370839501532035)
  ·
    refine ⟨361625765286556259252298053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241083843524370839501532035 361625765286556259252298053)
    ·
      refine ⟨67804830991229298609805885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361625765286556259252298053 67804830991229298609805885)
      ·
        refine ⟨25426811621710986978677207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67804830991229298609805885 25426811621710986978677207)
        ·
          refine ⟨38140217432566480468015811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25426811621710986978677207 38140217432566480468015811)
          ·
            refine ⟨57210326148849720702023717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38140217432566480468015811 57210326148849720702023717)
            ·
              refine ⟨10726936152909322631629447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57210326148849720702023717 10726936152909322631629447)
              ·
                refine ⟨16090404229363983947444171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10726936152909322631629447 16090404229363983947444171)
                ·
                  refine ⟨24135606344045975921166257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16090404229363983947444171 24135606344045975921166257)
                  ·
                    refine ⟨18101704758034481940874693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24135606344045975921166257 18101704758034481940874693)
                    ·
                      refine ⟨3394069642131465363914005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18101704758034481940874693 3394069642131465363914005)
                      ·
                        rfl

theorem cell23_6609927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_6609927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609927 prefixEnd_6609927 := by exact prefixLift 6609927
  have htrace : WordTrace (prefixWord ++ tailWord_6609927) baseStart_6609927 baseEnd_6609927 := by
    simpa [prefixWord, tailWord_6609927, baseEnd_6609927] using wordTrace_append hprefix tailTrace_6609927
  have hstable : (prefixWord ++ tailWord_6609927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609927).length < 2 ^ (prefixWord ++ tailWord_6609927).sum := by decide
  have hdescent : baseEnd_6609927 < baseStart_6609927 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609948 : List Nat := [2, 2, 3, 1, 5, 1, 2, 1, 1, 1, 4]
def baseStart_6609948 : Nat := 118140960795 + 6609948 * 2 ^ 59
def prefixEnd_6609948 : Nat := 4983230072969 + 3 ^ 40 * 6609948 * 2
def baseEnd_6609948 : Nat := 3394080425225209781751409

theorem tailTrace_6609948 : CollatzResearch.WordTrace tailWord_6609948 prefixEnd_6609948 3394080425225209781751409 := by
  unfold tailWord_6609948
  simp only [CollatzResearch.WordTrace]
  refine ⟨120542304728647380044023249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160723072971529840058697665 120542304728647380044023249)
  ·
    refine ⟨90406728546485535033017437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 120542304728647380044023249 90406728546485535033017437)
    ·
      refine ⟨33902523204932075637381539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 90406728546485535033017437 33902523204932075637381539)
      ·
        refine ⟨50853784807398113456072309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33902523204932075637381539 50853784807398113456072309)
        ·
          refine ⟨4767542325693573136506779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50853784807398113456072309 4767542325693573136506779)
          ·
            refine ⟨7151313488540359704760169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767542325693573136506779 7151313488540359704760169)
            ·
              refine ⟨5363485116405269778570127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7151313488540359704760169 5363485116405269778570127)
              ·
                refine ⟨8045227674607904667855191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363485116405269778570127 8045227674607904667855191)
                ·
                  refine ⟨12067841511911857001782787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8045227674607904667855191 12067841511911857001782787)
                  ·
                    refine ⟨18101762267867785502674181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12067841511911857001782787 18101762267867785502674181)
                    ·
                      refine ⟨3394080425225209781751409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18101762267867785502674181 3394080425225209781751409)
                      ·
                        rfl

theorem cell23_6609948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 1, 1, 4].length) (baseStart_6609948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609948 prefixEnd_6609948 := by exact prefixLift 6609948
  have htrace : WordTrace (prefixWord ++ tailWord_6609948) baseStart_6609948 baseEnd_6609948 := by
    simpa [prefixWord, tailWord_6609948, baseEnd_6609948] using wordTrace_append hprefix tailTrace_6609948
  have hstable : (prefixWord ++ tailWord_6609948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609948).length < 2 ^ (prefixWord ++ tailWord_6609948).sum := by decide
  have hdescent : baseEnd_6609948 < baseStart_6609948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609951 : List Nat := [1, 1, 2, 4, 1, 5, 2, 1, 1, 2, 3]
def baseStart_6609951 : Nat := 118140960795 + 6609951 * 2 ^ 59
def prefixEnd_6609951 : Nat := 4983230072969 + 3 ^ 40 * 6609951 * 2
def baseEnd_6609951 : Nat := 3394081965667173270013895

theorem tailTrace_6609951 : CollatzResearch.WordTrace tailWord_6609951 prefixEnd_6609951 3394081965667173270013895 := by
  unfold tailWord_6609951
  simp only [CollatzResearch.WordTrace]
  refine ⟨241084718876283891600405707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160723145917522594400270471 241084718876283891600405707)
  ·
    refine ⟨361627078314425837400608561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241084718876283891600405707 361627078314425837400608561)
    ·
      refine ⟨271220308735819378050456421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361627078314425837400608561 271220308735819378050456421)
      ·
        refine ⟨50853807887966133384460579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 271220308735819378050456421 50853807887966133384460579)
        ·
          refine ⟨76280711831949200076690869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50853807887966133384460579 76280711831949200076690869)
          ·
            refine ⟨7151316734245237507189769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76280711831949200076690869 7151316734245237507189769)
            ·
              refine ⟨5363487550683928130392327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7151316734245237507189769 5363487550683928130392327)
              ·
                refine ⟨8045231326025892195588491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5363487550683928130392327 8045231326025892195588491)
                ·
                  refine ⟨12067846989038838293382737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8045231326025892195588491 12067846989038838293382737)
                  ·
                    refine ⟨9050885241779128720037053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12067846989038838293382737 9050885241779128720037053)
                    ·
                      refine ⟨3394081965667173270013895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9050885241779128720037053 3394081965667173270013895)
                      ·
                        rfl

theorem cell23_6609951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_6609951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609951 prefixEnd_6609951 := by exact prefixLift 6609951
  have htrace : WordTrace (prefixWord ++ tailWord_6609951) baseStart_6609951 baseEnd_6609951 := by
    simpa [prefixWord, tailWord_6609951, baseEnd_6609951] using wordTrace_append hprefix tailTrace_6609951
  have hstable : (prefixWord ++ tailWord_6609951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609951).length < 2 ^ (prefixWord ++ tailWord_6609951).sum := by decide
  have hdescent : baseEnd_6609951 < baseStart_6609951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6609991 : List Nat := [1, 1, 4, 1, 3, 3, 2, 2, 1, 3, 2]
def baseStart_6609991 : Nat := 118140960795 + 6609991 * 2 ^ 59
def prefixEnd_6609991 : Nat := 4983230072969 + 3 ^ 40 * 6609991 * 2
def baseEnd_6609991 : Nat := 3394102504893353113513711

theorem tailTrace_6609991 : CollatzResearch.WordTrace tailWord_6609991 prefixEnd_6609991 3394102504893353113513711 := by
  unfold tailWord_6609991
  simp only [CollatzResearch.WordTrace]
  refine ⟨241086177796138978431861827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160724118530759318954574551 241086177796138978431861827)
  ·
    refine ⟨361629266694208467647792741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241086177796138978431861827 361629266694208467647792741)
    ·
      refine ⟨67805487505164087683961139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 361629266694208467647792741 67805487505164087683961139)
      ·
        refine ⟨101708231257746131525941709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67805487505164087683961139 101708231257746131525941709)
        ·
          refine ⟨38140586721654799322228141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 101708231257746131525941709 38140586721654799322228141)
          ·
            refine ⟨14302720020620549745835553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38140586721654799322228141 14302720020620549745835553)
            ·
              refine ⟨10727040015465412309376665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14302720020620549745835553 10727040015465412309376665)
              ·
                refine ⟨8045280011599059232032499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10727040015465412309376665 8045280011599059232032499)
                ·
                  refine ⟨12067920017398588848048749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8045280011599059232032499 12067920017398588848048749)
                  ·
                    refine ⟨4525470006524470818018281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12067920017398588848048749 4525470006524470818018281)
                    ·
                      refine ⟨3394102504893353113513711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4525470006524470818018281 3394102504893353113513711)
                      ·
                        rfl

theorem cell23_6609991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_6609991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6609991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6609991 prefixEnd_6609991 := by exact prefixLift 6609991
  have htrace : WordTrace (prefixWord ++ tailWord_6609991) baseStart_6609991 baseEnd_6609991 := by
    simpa [prefixWord, tailWord_6609991, baseEnd_6609991] using wordTrace_append hprefix tailTrace_6609991
  have hstable : (prefixWord ++ tailWord_6609991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6609991).length < 2 ^ (prefixWord ++ tailWord_6609991).sum := by decide
  have hdescent : baseEnd_6609991 < baseStart_6609991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6609991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610000 : List Nat := [2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 4]
def baseStart_6610000 : Nat := 118140960795 + 6610000 * 2 ^ 59
def prefixEnd_6610000 : Nat := 4983230072969 + 3 ^ 40 * 6610000 * 2
def baseEnd_6610000 : Nat := 3394107126219243578301169

theorem tailTrace_6610000 : CollatzResearch.WordTrace tailWord_6610000 prefixEnd_6610000 3394107126219243578301169 := by
  unfold tailWord_6610000
  simp only [CollatzResearch.WordTrace]
  refine ⟨120543253026553186484469727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160724337368737581979292969 120543253026553186484469727)
  ·
    refine ⟨180814879539829779726704591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120543253026553186484469727 180814879539829779726704591)
    ·
      refine ⟨271222319309744669590056887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180814879539829779726704591 271222319309744669590056887)
      ·
        refine ⟨406833478964617004385085331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271222319309744669590056887 406833478964617004385085331)
        ·
          refine ⟨610250218446925506577627997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406833478964617004385085331 610250218446925506577627997)
          ·
            refine ⟨228843831917597064966610499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 610250218446925506577627997 228843831917597064966610499)
            ·
              refine ⟨343265747876395597449915749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228843831917597064966610499 343265747876395597449915749)
              ·
                refine ⟨64362327726824174521859203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 343265747876395597449915749 64362327726824174521859203)
                ·
                  refine ⟨96543491590236261782788805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 64362327726824174521859203 96543491590236261782788805)
                  ·
                    refine ⟨18101904673169299084272901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 96543491590236261782788805 18101904673169299084272901)
                    ·
                      refine ⟨3394107126219243578301169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18101904673169299084272901 3394107126219243578301169)
                      ·
                        rfl

theorem cell23_6610000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 4].length) (baseStart_6610000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610000 prefixEnd_6610000 := by exact prefixLift 6610000
  have htrace : WordTrace (prefixWord ++ tailWord_6610000) baseStart_6610000 baseEnd_6610000 := by
    simpa [prefixWord, tailWord_6610000, baseEnd_6610000] using wordTrace_append hprefix tailTrace_6610000
  have hstable : (prefixWord ++ tailWord_6610000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610000).length < 2 ^ (prefixWord ++ tailWord_6610000).sum := by decide
  have hdescent : baseEnd_6610000 < baseStart_6610000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610004 : List Nat := [2, 4, 1, 1, 1, 1, 2, 4, 1, 4, 2]
def baseStart_6610004 : Nat := 118140960795 + 6610004 * 2 ^ 59
def prefixEnd_6610004 : Nat := 4983230072969 + 3 ^ 40 * 6610004 * 2
def baseEnd_6610004 : Nat := 3394109180141861562651151

theorem tailTrace_6610004 : CollatzResearch.WordTrace tailWord_6610004 prefixEnd_6610004 3394109180141861562651151 := by
  unfold tailWord_6610004
  simp only [CollatzResearch.WordTrace]
  refine ⟨120543325972545940826042533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160724434630061254434723377 120543325972545940826042533)
  ·
    refine ⟨22601873619852363904882975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 120543325972545940826042533 22601873619852363904882975)
    ·
      refine ⟨33902810429778545857324463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22601873619852363904882975 33902810429778545857324463)
      ·
        refine ⟨50854215644667818785986695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33902810429778545857324463 50854215644667818785986695)
        ·
          refine ⟨76281323467001728178980043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50854215644667818785986695 76281323467001728178980043)
          ·
            refine ⟨114421985200502592268470065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76281323467001728178980043 114421985200502592268470065)
            ·
              refine ⟨85816488900376944201352549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 114421985200502592268470065 85816488900376944201352549)
              ·
                refine ⟨16090591668820677037753603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 85816488900376944201352549 16090591668820677037753603)
                ·
                  refine ⟨24135887503231015556630405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16090591668820677037753603 24135887503231015556630405)
                  ·
                    refine ⟨4525478906855815416868201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24135887503231015556630405 4525478906855815416868201)
                    ·
                      refine ⟨3394109180141861562651151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4525478906855815416868201 3394109180141861562651151)
                      ·
                        rfl

theorem cell23_6610004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_6610004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610004 prefixEnd_6610004 := by exact prefixLift 6610004
  have htrace : WordTrace (prefixWord ++ tailWord_6610004) baseStart_6610004 baseEnd_6610004 := by
    simpa [prefixWord, tailWord_6610004, baseEnd_6610004] using wordTrace_append hprefix tailTrace_6610004
  have hstable : (prefixWord ++ tailWord_6610004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610004).length < 2 ^ (prefixWord ++ tailWord_6610004).sum := by decide
  have hdescent : baseEnd_6610004 < baseStart_6610004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610020 : List Nat := [2, 3, 1, 1, 2, 1, 1, 1, 1, 1, 9]
def baseStart_6610020 : Nat := 118140960795 + 6610020 * 2 ^ 59
def prefixEnd_6610020 : Nat := 4983230072969 + 3 ^ 40 * 6610020 * 2
def baseEnd_6610020 : Nat := 3394117395832333500051077

theorem tailTrace_6610020 : CollatzResearch.WordTrace tailWord_6610020 prefixEnd_6610020 3394117395832333500051077 := by
  unfold tailWord_6610020
  simp only [CollatzResearch.WordTrace]
  refine ⟨120543617756516958192333757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160724823675355944256445009 120543617756516958192333757)
  ·
    refine ⟨45203856658693859322125159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 120543617756516958192333757 45203856658693859322125159)
    ·
      refine ⟨67805784988040788983187739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45203856658693859322125159 67805784988040788983187739)
      ·
        refine ⟨101708677482061183474781609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67805784988040788983187739 101708677482061183474781609)
        ·
          refine ⟨76281508111545887606086207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 101708677482061183474781609 76281508111545887606086207)
          ·
            refine ⟨114422262167318831409129311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76281508111545887606086207 114422262167318831409129311)
            ·
              refine ⟨171633393250978247113693967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114422262167318831409129311 171633393250978247113693967)
              ·
                refine ⟨257450089876467370670540951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 171633393250978247113693967 257450089876467370670540951)
                ·
                  refine ⟨386175134814701056005811427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 257450089876467370670540951 386175134814701056005811427)
                  ·
                    refine ⟨579262702222051584008717141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 386175134814701056005811427 579262702222051584008717141)
                    ·
                      refine ⟨3394117395832333500051077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 579262702222051584008717141 3394117395832333500051077)
                      ·
                        rfl

theorem cell23_6610020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 1, 1, 1, 9].length) (baseStart_6610020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610020 prefixEnd_6610020 := by exact prefixLift 6610020
  have htrace : WordTrace (prefixWord ++ tailWord_6610020) baseStart_6610020 baseEnd_6610020 := by
    simpa [prefixWord, tailWord_6610020, baseEnd_6610020] using wordTrace_append hprefix tailTrace_6610020
  have hstable : (prefixWord ++ tailWord_6610020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610020).length < 2 ^ (prefixWord ++ tailWord_6610020).sum := by decide
  have hdescent : baseEnd_6610020 < baseStart_6610020 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610021 : List Nat := [1, 3, 1, 3, 2, 1, 2, 4, 2, 2, 2]
def baseStart_6610021 : Nat := 118140960795 + 6610021 * 2 ^ 59
def prefixEnd_6610021 : Nat := 4983230072969 + 3 ^ 40 * 6610021 * 2
def baseEnd_6610021 : Nat := 3394117909312987996138573

theorem tailTrace_6610021 : CollatzResearch.WordTrace tailWord_6610021 prefixEnd_6610021 3394117909312987996138573 := by
  unfold tailWord_6610021
  simp only [CollatzResearch.WordTrace]
  refine ⟨241087271986030293555453917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160724847990686862370302611 241087271986030293555453917)
  ·
    refine ⟨90407726994761360083295219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 241087271986030293555453917 90407726994761360083295219)
    ·
      refine ⟨135611590492142040124942829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 90407726994761360083295219 135611590492142040124942829)
      ·
        refine ⟨50854346434553265046853561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 135611590492142040124942829 50854346434553265046853561)
        ·
          refine ⟨38140759825914948785140171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50854346434553265046853561 38140759825914948785140171)
          ·
            refine ⟨57211139738872423177710257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38140759825914948785140171 57211139738872423177710257)
            ·
              refine ⟨42908354804154317383282693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57211139738872423177710257 42908354804154317383282693)
              ·
                refine ⟨8045316525778934509365505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42908354804154317383282693 8045316525778934509365505)
                ·
                  refine ⟨6033987394334200882024129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8045316525778934509365505 6033987394334200882024129)
                  ·
                    refine ⟨4525490545750650661518097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6033987394334200882024129 4525490545750650661518097)
                    ·
                      refine ⟨3394117909312987996138573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4525490545750650661518097 3394117909312987996138573)
                      ·
                        rfl

theorem cell23_6610021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_6610021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610021 prefixEnd_6610021 := by exact prefixLift 6610021
  have htrace : WordTrace (prefixWord ++ tailWord_6610021) baseStart_6610021 baseEnd_6610021 := by
    simpa [prefixWord, tailWord_6610021, baseEnd_6610021] using wordTrace_append hprefix tailTrace_6610021
  have hstable : (prefixWord ++ tailWord_6610021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610021).length < 2 ^ (prefixWord ++ tailWord_6610021).sum := by decide
  have hdescent : baseEnd_6610021 < baseStart_6610021 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610038 : List Nat := [5, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_6610038 : Nat := 118140960795 + 6610038 * 2 ^ 59
def prefixEnd_6610038 : Nat := 4983230072969 + 3 ^ 40 * 6610038 * 2
def baseEnd_6610038 : Nat := 3394126638484114429625995

theorem tailTrace_6610038 : CollatzResearch.WordTrace tailWord_6610038 prefixEnd_6610038 3394126638484114429625995 := by
  unfold tailWord_6610038
  simp only [CollatzResearch.WordTrace]
  refine ⟨15067993251685544091176423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 160725261351312470305881845 15067993251685544091176423)
  ·
    refine ⟨22601989877528316136764635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15067993251685544091176423 22601989877528316136764635)
    ·
      refine ⟨33902984816292474205146953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22601989877528316136764635 33902984816292474205146953)
      ·
        refine ⟨25427238612219355653860215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33902984816292474205146953 25427238612219355653860215)
        ·
          refine ⟨38140857918329033480790323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25427238612219355653860215 38140857918329033480790323)
          ·
            refine ⟨57211286877493550221185485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38140857918329033480790323 57211286877493550221185485)
            ·
              refine ⟨21454232579060081332944557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57211286877493550221185485 21454232579060081332944557)
              ·
                refine ⟨8045337217147530499854209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21454232579060081332944557 8045337217147530499854209)
                ·
                  refine ⟨6034002912860647874890657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8045337217147530499854209 6034002912860647874890657)
                  ·
                    refine ⟨4525502184645485906167993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6034002912860647874890657 4525502184645485906167993)
                    ·
                      refine ⟨3394126638484114429625995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4525502184645485906167993 3394126638484114429625995)
                      ·
                        rfl

theorem cell23_6610038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_6610038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610038 prefixEnd_6610038 := by exact prefixLift 6610038
  have htrace : WordTrace (prefixWord ++ tailWord_6610038) baseStart_6610038 baseEnd_6610038 := by
    simpa [prefixWord, tailWord_6610038, baseEnd_6610038] using wordTrace_append hprefix tailTrace_6610038
  have hstable : (prefixWord ++ tailWord_6610038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610038).length < 2 ^ (prefixWord ++ tailWord_6610038).sum := by decide
  have hdescent : baseEnd_6610038 < baseStart_6610038 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610040 : List Nat := [2, 1, 2, 1, 1, 1, 4, 1, 3, 7]
def baseStart_6610040 : Nat := 118140960795 + 6610040 * 2 ^ 59
def prefixEnd_6610040 : Nat := 4983230072969 + 3 ^ 40 * 6610040 * 2
def baseEnd_6610040 : Nat := 1131375888481807807266995

theorem tailTrace_6610040 : CollatzResearch.WordTrace tailWord_6610040 prefixEnd_6610040 1131375888481807807266995 := by
  unfold tailWord_6610040
  simp only [CollatzResearch.WordTrace]
  refine ⟨120543982486480729900197787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 160725309981974306533597049 120543982486480729900197787)
  ·
    refine ⟨180815973729721094850296681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 120543982486480729900197787 180815973729721094850296681)
    ·
      refine ⟨135611980297290821137722511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 180815973729721094850296681 135611980297290821137722511)
      ·
        refine ⟨203417970445936231706583767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135611980297290821137722511 203417970445936231706583767)
        ·
          refine ⟨305126955668904347559875651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203417970445936231706583767 305126955668904347559875651)
          ·
            refine ⟨457690433503356521339813477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 305126955668904347559875651 457690433503356521339813477)
            ·
              refine ⟨85816956281879347751215027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 457690433503356521339813477 85816956281879347751215027)
              ·
                refine ⟨128725434422819021626822541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85816956281879347751215027 128725434422819021626822541)
                ·
                  refine ⟨48272037908557133110058453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 128725434422819021626822541 48272037908557133110058453)
                  ·
                    refine ⟨1131375888481807807266995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 48272037908557133110058453 1131375888481807807266995)
                    ·
                      rfl

theorem cell23_6610040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_6610040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610040 prefixEnd_6610040 := by exact prefixLift 6610040
  have htrace : WordTrace (prefixWord ++ tailWord_6610040) baseStart_6610040 baseEnd_6610040 := by
    simpa [prefixWord, tailWord_6610040, baseEnd_6610040] using wordTrace_append hprefix tailTrace_6610040
  have hstable : (prefixWord ++ tailWord_6610040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610040).length < 2 ^ (prefixWord ++ tailWord_6610040).sum := by decide
  have hdescent : baseEnd_6610040 < baseStart_6610040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6610057 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 2, 5]
def baseStart_6610057 : Nat := 118140960795 + 6610057 * 2 ^ 59
def prefixEnd_6610057 : Nat := 4983230072969 + 3 ^ 40 * 6610057 * 2
def baseEnd_6610057 : Nat := 1131378798205516618429469

theorem tailTrace_6610057 : CollatzResearch.WordTrace tailWord_6610057 prefixEnd_6610057 1131378798205516618429469 := by
  unfold tailWord_6610057
  simp only [CollatzResearch.WordTrace]
  refine ⟨241088585013899871703764425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 160725723342599914469176283 241088585013899871703764425)
  ·
    refine ⟨180816438760424903777823319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 241088585013899871703764425 180816438760424903777823319)
    ·
      refine ⟨271224658140637355666734979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 180816438760424903777823319 271224658140637355666734979)
      ·
        refine ⟨406836987210956033500102469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 271224658140637355666734979 406836987210956033500102469)
        ·
          refine ⟨76281935102054256281269213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 406836987210956033500102469 76281935102054256281269213)
          ·
            refine ⟨28605725663270346105475955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76281935102054256281269213 28605725663270346105475955)
            ·
              refine ⟨42908588494905519158213933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28605725663270346105475955 42908588494905519158213933)
              ·
                refine ⟨16090720685589569684330225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42908588494905519158213933 16090720685589569684330225)
                ·
                  refine ⟨12068040514192177263247669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16090720685589569684330225 12068040514192177263247669)
                  ·
                    refine ⟨1131378798205516618429469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12068040514192177263247669 1131378798205516618429469)
                    ·
                      rfl

theorem cell23_6610057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 2, 5].length) (baseStart_6610057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6610057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6610057 prefixEnd_6610057 := by exact prefixLift 6610057
  have htrace : WordTrace (prefixWord ++ tailWord_6610057) baseStart_6610057 baseEnd_6610057 := by
    simpa [prefixWord, tailWord_6610057, baseEnd_6610057] using wordTrace_append hprefix tailTrace_6610057
  have hstable : (prefixWord ++ tailWord_6610057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6610057).length < 2 ^ (prefixWord ++ tailWord_6610057).sum := by decide
  have hdescent : baseEnd_6610057 < baseStart_6610057 := by decide
  rcases family_descends (prefixWord ++ tailWord_6610057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
