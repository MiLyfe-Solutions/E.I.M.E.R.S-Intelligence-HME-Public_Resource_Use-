import V185TrunkScan23Chunk1099

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6513850 : List Nat := [3, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3]
def baseStart_6513850 : Nat := 118140960795 + 6513850 * 2 ^ 59
def prefixEnd_6513850 : Nat := 4983230072969 + 3 ^ 40 * 6513850 * 2
def baseEnd_6513850 : Nat := 3344735961289444765618355

theorem tailTrace_6513850 : CollatzResearch.WordTrace tailWord_6513850 prefixEnd_6513850 3344735961289444765618355 := by
  unfold tailWord_6513850
  simp only [CollatzResearch.WordTrace]
  refine ⟨59394906862860350464072751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158386418300960934570860669 59394906862860350464072751)
  ·
    refine ⟨89092360294290525696109127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59394906862860350464072751 89092360294290525696109127)
    ·
      refine ⟨133638540441435788544163691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89092360294290525696109127 133638540441435788544163691)
      ·
        refine ⟨200457810662153682816245537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133638540441435788544163691 200457810662153682816245537)
        ·
          refine ⟨150343357996615262112184153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200457810662153682816245537 150343357996615262112184153)
          ·
            refine ⟨112757518497461446584138115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150343357996615262112184153 112757518497461446584138115)
            ·
              refine ⟨169136277746192169876207173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112757518497461446584138115 169136277746192169876207173)
              ·
                refine ⟨31713052077411031851788845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169136277746192169876207173 31713052077411031851788845)
                ·
                  refine ⟨11892394529029136944420817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31713052077411031851788845 11892394529029136944420817)
                  ·
                    refine ⟨8919295896771852708315613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11892394529029136944420817 8919295896771852708315613)
                    ·
                      refine ⟨3344735961289444765618355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8919295896771852708315613 3344735961289444765618355)
                      ·
                        rfl

theorem cell23_6513850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 4, 3, 2, 3].length) (baseStart_6513850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513850 prefixEnd_6513850 := by exact prefixLift 6513850
  have htrace : WordTrace (prefixWord ++ tailWord_6513850) baseStart_6513850 baseEnd_6513850 := by
    simpa [prefixWord, tailWord_6513850, baseEnd_6513850] using wordTrace_append hprefix tailTrace_6513850
  have hstable : (prefixWord ++ tailWord_6513850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513850).length < 2 ^ (prefixWord ++ tailWord_6513850).sum := by decide
  have hdescent : baseEnd_6513850 < baseStart_6513850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513853 : List Nat := [1, 4, 1, 2, 1, 1, 3, 10]
def baseStart_6513853 : Nat := 118140960795 + 6513853 * 2 ^ 59
def prefixEnd_6513853 : Nat := 4983230072969 + 3 ^ 40 * 6513853 * 2
def baseEnd_6513853 : Nat := 123879166730792898291883

theorem tailTrace_6513853 : CollatzResearch.WordTrace tailWord_6513853 prefixEnd_6513853 123879166730792898291883 := by
  unfold tailWord_6513853
  simp only [CollatzResearch.WordTrace]
  refine ⟨237579736870430533368650213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158386491246953688912433475 237579736870430533368650213)
  ·
    refine ⟨44546200663205725006621915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237579736870430533368650213 44546200663205725006621915)
    ·
      refine ⟨66819300994808587509932873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44546200663205725006621915 66819300994808587509932873)
      ·
        refine ⟨50114475746106440632449655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66819300994808587509932873 50114475746106440632449655)
        ·
          refine ⟨75171713619159660948674483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50114475746106440632449655 75171713619159660948674483)
          ·
            refine ⟨112757570428739491423011725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75171713619159660948674483 112757570428739491423011725)
            ·
              refine ⟨42284088910777309283629397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112757570428739491423011725 42284088910777309283629397)
              ·
                refine ⟨123879166730792898291883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42284088910777309283629397 123879166730792898291883)
                ·
                  rfl

theorem cell23_6513853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 10].length) (baseStart_6513853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513853 prefixEnd_6513853 := by exact prefixLift 6513853
  have htrace : WordTrace (prefixWord ++ tailWord_6513853) baseStart_6513853 baseEnd_6513853 := by
    simpa [prefixWord, tailWord_6513853, baseEnd_6513853] using wordTrace_append hprefix tailTrace_6513853
  have hstable : (prefixWord ++ tailWord_6513853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513853).length < 2 ^ (prefixWord ++ tailWord_6513853).sum := by decide
  have hdescent : baseEnd_6513853 < baseStart_6513853 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513877 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_6513877 : Nat := 118140960795 + 6513877 * 2 ^ 59
def prefixEnd_6513877 : Nat := 4983230072969 + 3 ^ 40 * 6513877 * 2
def baseEnd_6513877 : Nat := 3344749825267116159980731

theorem tailTrace_6513877 : CollatzResearch.WordTrace tailWord_6513877 prefixEnd_6513877 3344749825267116159980731 := by
  unfold tailWord_6513877
  simp only [CollatzResearch.WordTrace]
  refine ⟨237580612222343585467523885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158387074814895723645015923 237580612222343585467523885)
  ·
    refine ⟨89092729583378844550321457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237580612222343585467523885 89092729583378844550321457)
    ·
      refine ⟨66819547187534133412741093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89092729583378844550321457 66819547187534133412741093)
      ·
        refine ⟨12528665097662650014888955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66819547187534133412741093 12528665097662650014888955)
        ·
          refine ⟨18792997646493975022333433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12528665097662650014888955 18792997646493975022333433)
          ·
            refine ⟨14094748234870481266750075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18792997646493975022333433 14094748234870481266750075)
            ·
              refine ⟨21142122352305721900125113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14094748234870481266750075 21142122352305721900125113)
              ·
                refine ⟨15856591764229291425093835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21142122352305721900125113 15856591764229291425093835)
                ·
                  refine ⟨23784887646343937137640753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15856591764229291425093835 23784887646343937137640753)
                  ·
                    refine ⟨17838665734757952853230565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23784887646343937137640753 17838665734757952853230565)
                    ·
                      refine ⟨3344749825267116159980731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17838665734757952853230565 3344749825267116159980731)
                      ·
                        rfl

theorem cell23_6513877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_6513877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513877 prefixEnd_6513877 := by exact prefixLift 6513877
  have htrace : WordTrace (prefixWord ++ tailWord_6513877) baseStart_6513877 baseEnd_6513877 := by
    simpa [prefixWord, tailWord_6513877, baseEnd_6513877] using wordTrace_append hprefix tailTrace_6513877
  have hstable : (prefixWord ++ tailWord_6513877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513877).length < 2 ^ (prefixWord ++ tailWord_6513877).sum := by decide
  have hdescent : baseEnd_6513877 < baseStart_6513877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513898 : List Nat := [3, 1, 3, 1, 1, 3, 4, 2, 1, 2, 2]
def baseStart_6513898 : Nat := 118140960795 + 6513898 * 2 ^ 59
def prefixEnd_6513898 : Nat := 4983230072969 + 3 ^ 40 * 6513898 * 2
def baseEnd_6513898 : Nat := 3344760608360860577818135

theorem tailTrace_6513898 : CollatzResearch.WordTrace tailWord_6513898 prefixEnd_6513898 3344760608360860577818135 := by
  unfold tailWord_6513898
  simp only [CollatzResearch.WordTrace]
  refine ⟨59395344538816876513509587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158387585436845004036025565 59395344538816876513509587)
  ·
    refine ⟨89093016808225314770264381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59395344538816876513509587 89093016808225314770264381)
    ·
      refine ⟨33409881303084493038849143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89093016808225314770264381 33409881303084493038849143)
      ·
        refine ⟨50114821954626739558273715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33409881303084493038849143 50114821954626739558273715)
        ·
          refine ⟨75172232931940109337410573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50114821954626739558273715 75172232931940109337410573)
          ·
            refine ⟨28189587349477541001528965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75172232931940109337410573 28189587349477541001528965)
            ·
              refine ⟨5285547628027038937786681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28189587349477541001528965 5285547628027038937786681)
              ·
                refine ⟨3964160721020279203340011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5285547628027038937786681 3964160721020279203340011)
                ·
                  refine ⟨5946241081530418805010017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3964160721020279203340011 5946241081530418805010017)
                  ·
                    refine ⟨4459680811147814103757513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5946241081530418805010017 4459680811147814103757513)
                    ·
                      refine ⟨3344760608360860577818135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4459680811147814103757513 3344760608360860577818135)
                      ·
                        rfl

theorem cell23_6513898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 4, 2, 1, 2, 2].length) (baseStart_6513898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513898 prefixEnd_6513898 := by exact prefixLift 6513898
  have htrace : WordTrace (prefixWord ++ tailWord_6513898) baseStart_6513898 baseEnd_6513898 := by
    simpa [prefixWord, tailWord_6513898, baseEnd_6513898] using wordTrace_append hprefix tailTrace_6513898
  have hstable : (prefixWord ++ tailWord_6513898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513898).length < 2 ^ (prefixWord ++ tailWord_6513898).sum := by decide
  have hdescent : baseEnd_6513898 < baseStart_6513898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513907 : List Nat := [1, 1, 1, 2, 2, 5, 1, 2, 3, 3, 2]
def baseStart_6513907 : Nat := 118140960795 + 6513907 * 2 ^ 59
def prefixEnd_6513907 : Nat := 4983230072969 + 3 ^ 40 * 6513907 * 2
def baseEnd_6513907 : Nat := 3344765229686751042605593

theorem tailTrace_6513907 : CollatzResearch.WordTrace tailWord_6513907 prefixEnd_6513907 3344765229686751042605593 := by
  unfold tailWord_6513907
  simp only [CollatzResearch.WordTrace]
  refine ⟨237581706412234900591115975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158387804274823267060743983 237581706412234900591115975)
  ·
    refine ⟨356372559618352350886673963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237581706412234900591115975 356372559618352350886673963)
    ·
      refine ⟨534558839427528526330010945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356372559618352350886673963 534558839427528526330010945)
      ·
        refine ⟨400919129570646394747508209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534558839427528526330010945 400919129570646394747508209)
        ·
          refine ⟨300689347177984796060631157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400919129570646394747508209 300689347177984796060631157)
          ·
            refine ⟨28189626297936074630684171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 300689347177984796060631157 28189626297936074630684171)
            ·
              refine ⟨42284439446904111946026257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28189626297936074630684171 42284439446904111946026257)
              ·
                refine ⟨31713329585178083959519693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42284439446904111946026257 31713329585178083959519693)
                ·
                  refine ⟨11892498594441781484819885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31713329585178083959519693 11892498594441781484819885)
                  ·
                    refine ⟨4459686972915668056807457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11892498594441781484819885 4459686972915668056807457)
                    ·
                      refine ⟨3344765229686751042605593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4459686972915668056807457 3344765229686751042605593)
                      ·
                        rfl

theorem cell23_6513907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 2, 3, 3, 2].length) (baseStart_6513907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513907 prefixEnd_6513907 := by exact prefixLift 6513907
  have htrace : WordTrace (prefixWord ++ tailWord_6513907) baseStart_6513907 baseEnd_6513907 := by
    simpa [prefixWord, tailWord_6513907, baseEnd_6513907] using wordTrace_append hprefix tailTrace_6513907
  have hstable : (prefixWord ++ tailWord_6513907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513907).length < 2 ^ (prefixWord ++ tailWord_6513907).sum := by decide
  have hdescent : baseEnd_6513907 < baseStart_6513907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513910 : List Nat := [5, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5]
def baseStart_6513910 : Nat := 118140960795 + 6513910 * 2 ^ 59
def prefixEnd_6513910 : Nat := 4983230072969 + 3 ^ 40 * 6513910 * 2
def baseEnd_6513910 : Nat := 3344766770128714530868079

theorem tailTrace_6513910 : CollatzResearch.WordTrace tailWord_6513910 prefixEnd_6513910 3344766770128714530868079 := by
  unfold tailWord_6513910
  simp only [CollatzResearch.WordTrace]
  refine ⟨14848863489451502006467199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158387877220816021402316789 14848863489451502006467199)
  ·
    refine ⟨22273295234177253009700799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14848863489451502006467199 22273295234177253009700799)
    ·
      refine ⟨33409942851265879514551199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22273295234177253009700799 33409942851265879514551199)
      ·
        refine ⟨50114914276898819271826799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33409942851265879514551199 50114914276898819271826799)
        ·
          refine ⟨75172371415348228907740199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50114914276898819271826799 75172371415348228907740199)
          ·
            refine ⟨112758557123022343361610299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75172371415348228907740199 112758557123022343361610299)
            ·
              refine ⟨169137835684533515042415449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112758557123022343361610299 169137835684533515042415449)
              ·
                refine ⟨126853376763400136281811587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169137835684533515042415449 126853376763400136281811587)
                ·
                  refine ⟨190280065145100204422717381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126853376763400136281811587 190280065145100204422717381)
                  ·
                    refine ⟨35677512214706288329259509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 190280065145100204422717381 35677512214706288329259509)
                    ·
                      refine ⟨3344766770128714530868079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35677512214706288329259509 3344766770128714530868079)
                      ·
                        rfl

theorem cell23_6513910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_6513910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513910 prefixEnd_6513910 := by exact prefixLift 6513910
  have htrace : WordTrace (prefixWord ++ tailWord_6513910) baseStart_6513910 baseEnd_6513910 := by
    simpa [prefixWord, tailWord_6513910, baseEnd_6513910] using wordTrace_append hprefix tailTrace_6513910
  have hstable : (prefixWord ++ tailWord_6513910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513910).length < 2 ^ (prefixWord ++ tailWord_6513910).sum := by decide
  have hdescent : baseEnd_6513910 < baseStart_6513910 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513924 : List Nat := [2, 3, 2, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_6513924 : Nat := 118140960795 + 6513924 * 2 ^ 59
def prefixEnd_6513924 : Nat := 4983230072969 + 3 ^ 40 * 6513924 * 2
def baseEnd_6513924 : Nat := 3344773958857877476093015

theorem tailTrace_6513924 : CollatzResearch.WordTrace tailWord_6513924 prefixEnd_6513924 3344773958857877476093015 := by
  unfold tailWord_6513924
  simp only [CollatzResearch.WordTrace]
  refine ⟨118791163226586656247242413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158388217635448874996323217 118791163226586656247242413)
  ·
    refine ⟨44546686209969996092715905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118791163226586656247242413 44546686209969996092715905)
    ·
      refine ⟨33410014657477497069536929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44546686209969996092715905 33410014657477497069536929)
      ·
        refine ⟨25057510993108122802152697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33410014657477497069536929 25057510993108122802152697)
        ·
          refine ⟨18793133244831092101614523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25057510993108122802152697 18793133244831092101614523)
          ·
            refine ⟨28189699867246638152421785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18793133244831092101614523 28189699867246638152421785)
            ·
              refine ⟨21142274900434978614316339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28189699867246638152421785 21142274900434978614316339)
              ·
                refine ⟨31713412350652467921474509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21142274900434978614316339 31713412350652467921474509)
                ·
                  refine ⟨11892529631494675470552941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31713412350652467921474509 11892529631494675470552941)
                  ·
                    refine ⟨4459698611810503301457353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11892529631494675470552941 4459698611810503301457353)
                    ·
                      refine ⟨3344773958857877476093015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4459698611810503301457353 3344773958857877476093015)
                      ·
                        rfl

theorem cell23_6513924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_6513924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513924 prefixEnd_6513924 := by exact prefixLift 6513924
  have htrace : WordTrace (prefixWord ++ tailWord_6513924) baseStart_6513924 baseEnd_6513924 := by
    simpa [prefixWord, tailWord_6513924, baseEnd_6513924] using wordTrace_append hprefix tailTrace_6513924
  have hstable : (prefixWord ++ tailWord_6513924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513924).length < 2 ^ (prefixWord ++ tailWord_6513924).sum := by decide
  have hdescent : baseEnd_6513924 < baseStart_6513924 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6513937 : List Nat := [1, 2, 2, 1, 1, 4, 1, 4, 1, 4, 2]
def baseStart_6513937 : Nat := 118140960795 + 6513937 * 2 ^ 59
def prefixEnd_6513937 : Nat := 4983230072969 + 3 ^ 40 * 6513937 * 2
def baseEnd_6513937 : Nat := 3344780634106385925230455

theorem tailTrace_6513937 : CollatzResearch.WordTrace tailWord_6513937 prefixEnd_6513937 3344780634106385925230455 := by
  unfold tailWord_6513937
  simp only [CollatzResearch.WordTrace]
  refine ⟨237582800602126215714708065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158388533734750810476472043 237582800602126215714708065)
  ·
    refine ⟨178187100451594661786031049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237582800602126215714708065 178187100451594661786031049)
    ·
      refine ⟨133640325338695996339523287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178187100451594661786031049 133640325338695996339523287)
      ·
        refine ⟨200460488008043994509284931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133640325338695996339523287 200460488008043994509284931)
        ·
          refine ⟨300690732012065991763927397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200460488008043994509284931 300690732012065991763927397)
          ·
            refine ⟨56379512252262373455736387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300690732012065991763927397 56379512252262373455736387)
            ·
              refine ⟨84569268378393560183604581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56379512252262373455736387 84569268378393560183604581)
              ·
                refine ⟨15856737820948792534425859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84569268378393560183604581 15856737820948792534425859)
                ·
                  refine ⟨23785106731423188801638789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15856737820948792534425859 23785106731423188801638789)
                  ·
                    refine ⟨4459707512141847900307273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23785106731423188801638789 4459707512141847900307273)
                    ·
                      refine ⟨3344780634106385925230455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4459707512141847900307273 3344780634106385925230455)
                      ·
                        rfl

theorem cell23_6513937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 4, 2].length) (baseStart_6513937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6513937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6513937 prefixEnd_6513937 := by exact prefixLift 6513937
  have htrace : WordTrace (prefixWord ++ tailWord_6513937) baseStart_6513937 baseEnd_6513937 := by
    simpa [prefixWord, tailWord_6513937, baseEnd_6513937] using wordTrace_append hprefix tailTrace_6513937
  have hstable : (prefixWord ++ tailWord_6513937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6513937).length < 2 ^ (prefixWord ++ tailWord_6513937).sum := by decide
  have hdescent : baseEnd_6513937 < baseStart_6513937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6513937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514000 : List Nat := [2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 5]
def baseStart_6514000 : Nat := 118140960795 + 6514000 * 2 ^ 59
def prefixEnd_6514000 : Nat := 4983230072969 + 3 ^ 40 * 6514000 * 2
def baseEnd_6514000 : Nat := 3344812983387619178742665

theorem tailTrace_6514000 : CollatzResearch.WordTrace tailWord_6514000 prefixEnd_6514000 3344812983387619178742665 := by
  unfold tailWord_6514000
  simp only [CollatzResearch.WordTrace]
  refine ⟨118792549200448988737125727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158390065600598651649500969 118792549200448988737125727)
  ·
    refine ⟨178188823800673483105688591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118792549200448988737125727 178188823800673483105688591)
    ·
      refine ⟨267283235701010224658532887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178188823800673483105688591 267283235701010224658532887)
      ·
        refine ⟨400924853551515336987799331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267283235701010224658532887 400924853551515336987799331)
        ·
          refine ⟨601387280327273005481698997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 400924853551515336987799331 601387280327273005481698997)
          ·
            refine ⟨56380057530681844263909281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 601387280327273005481698997 56380057530681844263909281)
            ·
              refine ⟨42285043148011383197931961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56380057530681844263909281 42285043148011383197931961)
              ·
                refine ⟨31713782361008537398448971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42285043148011383197931961 31713782361008537398448971)
                ·
                  refine ⟨47570673541512806097673457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31713782361008537398448971 47570673541512806097673457)
                  ·
                    refine ⟨35678005156134604573255093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47570673541512806097673457 35678005156134604573255093)
                    ·
                      refine ⟨3344812983387619178742665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35678005156134604573255093 3344812983387619178742665)
                      ·
                        rfl

theorem cell23_6514000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_6514000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514000 prefixEnd_6514000 := by exact prefixLift 6514000
  have htrace : WordTrace (prefixWord ++ tailWord_6514000) baseStart_6514000 baseEnd_6514000 := by
    simpa [prefixWord, tailWord_6514000, baseEnd_6514000] using wordTrace_append hprefix tailTrace_6514000
  have hstable : (prefixWord ++ tailWord_6514000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514000).length < 2 ^ (prefixWord ++ tailWord_6514000).sum := by decide
  have hdescent : baseEnd_6514000 < baseStart_6514000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514007 : List Nat := [1, 1, 3, 2, 3, 3, 1, 2, 2, 5]
def baseStart_6514007 : Nat := 118140960795 + 6514007 * 2 ^ 59
def prefixEnd_6514007 : Nat := 4983230072969 + 3 ^ 40 * 6514007 * 2
def baseEnd_6514007 : Nat := 1114938859250733550451711

theorem tailTrace_6514007 : CollatzResearch.WordTrace tailWord_6514007 prefixEnd_6514007 1114938859250733550451711 := by
  unfold tailWord_6514007
  simp only [CollatzResearch.WordTrace]
  refine ⟨237585353711872617669756275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158390235807915078446504183 237585353711872617669756275)
  ·
    refine ⟨356378030567808926504634413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237585353711872617669756275 356378030567808926504634413)
    ·
      refine ⟨133641761462928347439237905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356378030567808926504634413 133641761462928347439237905)
      ·
        refine ⟨100231321097196260579428429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133641761462928347439237905 100231321097196260579428429)
        ·
          refine ⟨37586745411448597717285661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100231321097196260579428429 37586745411448597717285661)
          ·
            refine ⟨14095029529293224143982123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37586745411448597717285661 14095029529293224143982123)
            ·
              refine ⟨21142544293939836215973185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14095029529293224143982123 21142544293939836215973185)
              ·
                refine ⟨15856908220454877161979889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21142544293939836215973185 15856908220454877161979889)
                ·
                  refine ⟨11892681165341157871484917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15856908220454877161979889 11892681165341157871484917)
                  ·
                    refine ⟨1114938859250733550451711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11892681165341157871484917 1114938859250733550451711)
                    ·
                      rfl

theorem cell23_6514007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_6514007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514007 prefixEnd_6514007 := by exact prefixLift 6514007
  have htrace : WordTrace (prefixWord ++ tailWord_6514007) baseStart_6514007 baseEnd_6514007 := by
    simpa [prefixWord, tailWord_6514007, baseEnd_6514007] using wordTrace_append hprefix tailTrace_6514007
  have hstable : (prefixWord ++ tailWord_6514007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514007).length < 2 ^ (prefixWord ++ tailWord_6514007).sum := by decide
  have hdescent : baseEnd_6514007 < baseStart_6514007 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514078 : List Nat := [4, 3, 1, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_6514078 : Nat := 118140960795 + 6514078 * 2 ^ 59
def prefixEnd_6514078 : Nat := 4983230072969 + 3 ^ 40 * 6514078 * 2
def baseEnd_6514078 : Nat := 3344853034878669873567307

theorem tailTrace_6514078 : CollatzResearch.WordTrace tailWord_6514078 prefixEnd_6514078 3344853034878669873567307 := by
  unfold tailWord_6514078
  simp only [CollatzResearch.WordTrace]
  refine ⟨29698492911826924599448861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158391962196410264530393925 29698492911826924599448861)
  ·
    refine ⟨11136934841935096724793323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29698492911826924599448861 11136934841935096724793323)
    ·
      refine ⟨16705402262902645087189985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11136934841935096724793323 16705402262902645087189985)
      ·
        refine ⟨12529051697176983815392489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16705402262902645087189985 12529051697176983815392489)
        ·
          refine ⟨9396788772882737861544367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12529051697176983815392489 9396788772882737861544367)
          ·
            refine ⟨14095183159324106792316551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9396788772882737861544367 14095183159324106792316551)
            ·
              refine ⟨21142774738986160188474827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14095183159324106792316551 21142774738986160188474827)
              ·
                refine ⟨31714162108479240282712241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21142774738986160188474827 31714162108479240282712241)
                ·
                  refine ⟨23785621581359430212034181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31714162108479240282712241 23785621581359430212034181)
                  ·
                    refine ⟨4459804046504893164756409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23785621581359430212034181 4459804046504893164756409)
                    ·
                      refine ⟨3344853034878669873567307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4459804046504893164756409 3344853034878669873567307)
                      ·
                        rfl

theorem cell23_6514078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_6514078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514078 prefixEnd_6514078 := by exact prefixLift 6514078
  have htrace : WordTrace (prefixWord ++ tailWord_6514078) baseStart_6514078 baseEnd_6514078 := by
    simpa [prefixWord, tailWord_6514078, baseEnd_6514078] using wordTrace_append hprefix tailTrace_6514078
  have hstable : (prefixWord ++ tailWord_6514078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514078).length < 2 ^ (prefixWord ++ tailWord_6514078).sum := by decide
  have hdescent : baseEnd_6514078 < baseStart_6514078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514097 : List Nat := [1, 2, 2, 4, 1, 1, 1, 3, 3, 5]
def baseStart_6514097 : Nat := 118140960795 + 6514097 * 2 ^ 59
def prefixEnd_6514097 : Nat := 4983230072969 + 3 ^ 40 * 6514097 * 2
def baseEnd_6514097 : Nat := 1114954263670368433076573

theorem tailTrace_6514097 : CollatzResearch.WordTrace tailWord_6514097 prefixEnd_6514097 1114954263670368433076573 := by
  unfold tailWord_6514097
  simp only [CollatzResearch.WordTrace]
  refine ⟨237588636281546563040532545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158392424187697708693688363 237588636281546563040532545)
  ·
    refine ⟨178191477211159922280399409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237588636281546563040532545 178191477211159922280399409)
    ·
      refine ⟨133643607908369941710299557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178191477211159922280399409 133643607908369941710299557)
      ·
        refine ⟨25058176482819364070681167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133643607908369941710299557 25058176482819364070681167)
        ·
          refine ⟨37587264724229046106021751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25058176482819364070681167 37587264724229046106021751)
          ·
            refine ⟨56380897086343569159032627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37587264724229046106021751 56380897086343569159032627)
            ·
              refine ⟨84571345629515353738548941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56380897086343569159032627 84571345629515353738548941)
              ·
                refine ⟨31714254611068257651955853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84571345629515353738548941 31714254611068257651955853)
                ·
                  refine ⟨11892845479150596619483445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31714254611068257651955853 11892845479150596619483445)
                  ·
                    refine ⟨1114954263670368433076573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11892845479150596619483445 1114954263670368433076573)
                    ·
                      rfl

theorem cell23_6514097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 3, 5].length) (baseStart_6514097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514097 prefixEnd_6514097 := by exact prefixLift 6514097
  have htrace : WordTrace (prefixWord ++ tailWord_6514097) baseStart_6514097 baseEnd_6514097 := by
    simpa [prefixWord, tailWord_6514097, baseEnd_6514097] using wordTrace_append hprefix tailTrace_6514097
  have hstable : (prefixWord ++ tailWord_6514097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514097).length < 2 ^ (prefixWord ++ tailWord_6514097).sum := by decide
  have hdescent : baseEnd_6514097 < baseStart_6514097 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514137 : List Nat := [1, 2, 1, 2, 4, 2, 1, 1, 3, 1, 5]
def baseStart_6514137 : Nat := 118140960795 + 6514137 * 2 ^ 59
def prefixEnd_6514137 : Nat := 4983230072969 + 3 ^ 40 * 6514137 * 2
def baseEnd_6514137 : Nat := 3344883330237285142729535

theorem tailTrace_6514137 : CollatzResearch.WordTrace tailWord_6514137 prefixEnd_6514137 3344883330237285142729535 := by
  unfold tailWord_6514137
  simp only [CollatzResearch.WordTrace]
  refine ⟨237590095201401649871988665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158393396800934433247992443 237590095201401649871988665)
  ·
    refine ⟨178192571401051237403991499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237590095201401649871988665 178192571401051237403991499)
    ·
      refine ⟨267288857101576856105987249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178192571401051237403991499 267288857101576856105987249)
      ·
        refine ⟨200466642826182642079490437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267288857101576856105987249 200466642826182642079490437)
        ·
          refine ⟨37587495529909245389904457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200466642826182642079490437 37587495529909245389904457)
          ·
            refine ⟨28190621647431934042428343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37587495529909245389904457 28190621647431934042428343)
            ·
              refine ⟨42285932471147901063642515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28190621647431934042428343 42285932471147901063642515)
              ·
                refine ⟨63428898706721851595463773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42285932471147901063642515 63428898706721851595463773)
                ·
                  refine ⟨23785837015020694348298915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63428898706721851595463773 23785837015020694348298915)
                  ·
                    refine ⟨35678755522531041522448373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23785837015020694348298915 35678755522531041522448373)
                    ·
                      refine ⟨3344883330237285142729535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35678755522531041522448373 3344883330237285142729535)
                      ·
                        rfl

theorem cell23_6514137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 1, 3, 1, 5].length) (baseStart_6514137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514137 prefixEnd_6514137 := by exact prefixLift 6514137
  have htrace : WordTrace (prefixWord ++ tailWord_6514137) baseStart_6514137 baseEnd_6514137 := by
    simpa [prefixWord, tailWord_6514137, baseEnd_6514137] using wordTrace_append hprefix tailTrace_6514137
  have hstable : (prefixWord ++ tailWord_6514137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514137).length < 2 ^ (prefixWord ++ tailWord_6514137).sum := by decide
  have hdescent : baseEnd_6514137 < baseStart_6514137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514151 : List Nat := [1, 1, 5, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_6514151 : Nat := 118140960795 + 6514151 * 2 ^ 59
def prefixEnd_6514151 : Nat := 4983230072969 + 3 ^ 40 * 6514151 * 2
def baseEnd_6514151 : Nat := 3344890518966448087954471

theorem tailTrace_6514151 : CollatzResearch.WordTrace tailWord_6514151 prefixEnd_6514151 3344890518966448087954471 := by
  unfold tailWord_6514151
  simp only [CollatzResearch.WordTrace]
  refine ⟨237590605823350930262998307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158393737215567286841998871 237590605823350930262998307)
  ·
    refine ⟨356385908735026395394497461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237590605823350930262998307 356385908735026395394497461)
    ·
      refine ⟨33411178943908724568234137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 356385908735026395394497461 33411178943908724568234137)
      ·
        refine ⟨25058384207931543426175603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33411178943908724568234137 25058384207931543426175603)
        ·
          refine ⟨37587576311897315139263405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25058384207931543426175603 37587576311897315139263405)
          ·
            refine ⟨14095341116961493177223777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37587576311897315139263405 14095341116961493177223777)
            ·
              refine ⟨10571505837721119882917833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14095341116961493177223777 10571505837721119882917833)
              ·
                refine ⟨7928629378290839912188375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10571505837721119882917833 7928629378290839912188375)
                ·
                  refine ⟨11892944067436259868282563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7928629378290839912188375 11892944067436259868282563)
                  ·
                    refine ⟨17839416101154389802423845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11892944067436259868282563 17839416101154389802423845)
                    ·
                      refine ⟨3344890518966448087954471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17839416101154389802423845 3344890518966448087954471)
                      ·
                        rfl

theorem cell23_6514151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_6514151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514151 prefixEnd_6514151 := by exact prefixLift 6514151
  have htrace : WordTrace (prefixWord ++ tailWord_6514151) baseStart_6514151 baseEnd_6514151 := by
    simpa [prefixWord, tailWord_6514151, baseEnd_6514151] using wordTrace_append hprefix tailTrace_6514151
  have hstable : (prefixWord ++ tailWord_6514151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514151).length < 2 ^ (prefixWord ++ tailWord_6514151).sum := by decide
  have hdescent : baseEnd_6514151 < baseStart_6514151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514185 : List Nat := [1, 2, 1, 1, 3, 1, 7, 2, 1, 2, 2]
def baseStart_6514185 : Nat := 118140960795 + 6514185 * 2 ^ 59
def prefixEnd_6514185 : Nat := 4983230072969 + 3 ^ 40 * 6514185 * 2
def baseEnd_6514185 : Nat := 3344907977308700954929315

theorem tailTrace_6514185 : CollatzResearch.WordTrace tailWord_6514185 prefixEnd_6514185 3344907977308700954929315 := by
  unfold tailWord_6514185
  simp only [CollatzResearch.WordTrace]
  refine ⟨237591845905227754069736009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158394563936818502713157339 237591845905227754069736009)
  ·
    refine ⟨178193884428920815552302007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237591845905227754069736009 178193884428920815552302007)
    ·
      refine ⟨267290826643381223328453011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178193884428920815552302007 267290826643381223328453011)
      ·
        refine ⟨400936239965071834992679517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267290826643381223328453011 400936239965071834992679517)
        ·
          refine ⟨150351089986901938122254819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 400936239965071834992679517 150351089986901938122254819)
          ·
            refine ⟨225526634980352907183382229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150351089986901938122254819 225526634980352907183382229)
            ·
              refine ⟨5285780507352021262110521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 225526634980352907183382229 5285780507352021262110521)
              ·
                refine ⟨3964335380514015946582891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5285780507352021262110521 3964335380514015946582891)
                ·
                  refine ⟨5946503070771023919874337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3964335380514015946582891 5946503070771023919874337)
                  ·
                    refine ⟨4459877303078267939905753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5946503070771023919874337 4459877303078267939905753)
                    ·
                      refine ⟨3344907977308700954929315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4459877303078267939905753 3344907977308700954929315)
                      ·
                        rfl

theorem cell23_6514185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 1, 2, 2].length) (baseStart_6514185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514185 prefixEnd_6514185 := by exact prefixLift 6514185
  have htrace : WordTrace (prefixWord ++ tailWord_6514185) baseStart_6514185 baseEnd_6514185 := by
    simpa [prefixWord, tailWord_6514185, baseEnd_6514185] using wordTrace_append hprefix tailTrace_6514185
  have hstable : (prefixWord ++ tailWord_6514185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514185).length < 2 ^ (prefixWord ++ tailWord_6514185).sum := by decide
  have hdescent : baseEnd_6514185 < baseStart_6514185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514241 : List Nat := [1, 2, 5, 1, 1, 1, 1, 2, 3, 4, 2]
def baseStart_6514241 : Nat := 118140960795 + 6514241 * 2 ^ 59
def prefixEnd_6514241 : Nat := 4983230072969 + 3 ^ 40 * 6514241 * 2
def baseEnd_6514241 : Nat := 3344936732225352735829057

theorem tailTrace_6514241 : CollatzResearch.WordTrace tailWord_6514241 prefixEnd_6514241 3344936732225352735829057 := by
  unfold tailWord_6514241
  simp only [CollatzResearch.WordTrace]
  refine ⟨237593888393024875633774577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158395925595349917089183051 237593888393024875633774577)
  ·
    refine ⟨178195416294768656725330933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237593888393024875633774577 178195416294768656725330933)
    ·
      refine ⟨16705820277634561567999775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178195416294768656725330933 16705820277634561567999775)
      ·
        refine ⟨25058730416451842351999663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16705820277634561567999775 25058730416451842351999663)
        ·
          refine ⟨37588095624677763527999495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25058730416451842351999663 37588095624677763527999495)
          ·
            refine ⟨56382143437016645291999243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37588095624677763527999495 56382143437016645291999243)
            ·
              refine ⟨84573215155524967937998865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56382143437016645291999243 84573215155524967937998865)
              ·
                refine ⟨63429911366643725953499149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84573215155524967937998865 63429911366643725953499149)
                ·
                  refine ⟨23786216762491397232562181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63429911366643725953499149 23786216762491397232562181)
                  ·
                    refine ⟨4459915642967136981105409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23786216762491397232562181 4459915642967136981105409)
                    ·
                      refine ⟨3344936732225352735829057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4459915642967136981105409 3344936732225352735829057)
                      ·
                        rfl

theorem cell23_6514241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_6514241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514241 prefixEnd_6514241 := by exact prefixLift 6514241
  have htrace : WordTrace (prefixWord ++ tailWord_6514241) baseStart_6514241 baseEnd_6514241 := by
    simpa [prefixWord, tailWord_6514241, baseEnd_6514241] using wordTrace_append hprefix tailTrace_6514241
  have hstable : (prefixWord ++ tailWord_6514241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514241).length < 2 ^ (prefixWord ++ tailWord_6514241).sum := by decide
  have hdescent : baseEnd_6514241 < baseStart_6514241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514258 : List Nat := [3, 2, 2, 1, 2, 3, 2, 1, 1, 4, 2]
def baseStart_6514258 : Nat := 118140960795 + 6514258 * 2 ^ 59
def prefixEnd_6514258 : Nat := 4983230072969 + 3 ^ 40 * 6514258 * 2
def baseEnd_6514258 : Nat := 3344945461396479169316479

theorem tailTrace_6514258 : CollatzResearch.WordTrace tailWord_6514258 prefixEnd_6514258 3344945461396479169316479 := by
  unfold tailWord_6514258
  simp only [CollatzResearch.WordTrace]
  refine ⟨59398627108490821884285857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158396338955975525024762285 59398627108490821884285857)
  ·
    refine ⟨44548970331368116413214393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59398627108490821884285857 44548970331368116413214393)
    ·
      refine ⟨33411727748526087309910795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44548970331368116413214393 33411727748526087309910795)
      ·
        refine ⟨50117591622789130964866193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33411727748526087309910795 50117591622789130964866193)
        ·
          refine ⟨37588193717091848223649645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50117591622789130964866193 37588193717091848223649645)
          ·
            refine ⟨14095572643909443083868617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37588193717091848223649645 14095572643909443083868617)
            ·
              refine ⟨10571679482932082312901463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14095572643909443083868617 10571679482932082312901463)
              ·
                refine ⟨15857519224398123469352195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10571679482932082312901463 15857519224398123469352195)
                ·
                  refine ⟨23786278836597185204028293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15857519224398123469352195 23786278836597185204028293)
                  ·
                    refine ⟨4459927281861972225755305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23786278836597185204028293 4459927281861972225755305)
                    ·
                      refine ⟨3344945461396479169316479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4459927281861972225755305 3344945461396479169316479)
                      ·
                        rfl

theorem cell23_6514258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 1, 4, 2].length) (baseStart_6514258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514258 prefixEnd_6514258 := by exact prefixLift 6514258
  have htrace : WordTrace (prefixWord ++ tailWord_6514258) baseStart_6514258 baseEnd_6514258 := by
    simpa [prefixWord, tailWord_6514258, baseEnd_6514258] using wordTrace_append hprefix tailTrace_6514258
  have hstable : (prefixWord ++ tailWord_6514258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514258).length < 2 ^ (prefixWord ++ tailWord_6514258).sum := by decide
  have hdescent : baseEnd_6514258 < baseStart_6514258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514351 : List Nat := [1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 3]
def baseStart_6514351 : Nat := 118140960795 + 6514351 * 2 ^ 59
def prefixEnd_6514351 : Nat := 4983230072969 + 3 ^ 40 * 6514351 * 2
def baseEnd_6514351 : Nat := 3344993215097347305453551

theorem tailTrace_6514351 : CollatzResearch.WordTrace tailWord_6514351 prefixEnd_6514351 3344993215097347305453551 := by
  unfold tailWord_6514351
  simp only [CollatzResearch.WordTrace]
  refine ⟨237597900422626364420278907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158398600281750909613519271 237597900422626364420278907)
  ·
    refine ⟨356396850633939546630418361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237597900422626364420278907 356396850633939546630418361)
    ·
      refine ⟨267297637975454659972813771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356396850633939546630418361 267297637975454659972813771)
      ·
        refine ⟨400946456963181989959220657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267297637975454659972813771 400946456963181989959220657)
        ·
          refine ⟨300709842722386492469415493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400946456963181989959220657 300709842722386492469415493)
          ·
            refine ⟨56383095510447467338015405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300709842722386492469415493 56383095510447467338015405)
            ·
              refine ⟨21143660816417800251755777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56383095510447467338015405 21143660816417800251755777)
              ·
                refine ⟨15857745612313350188816833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21143660816417800251755777 15857745612313350188816833)
                ·
                  refine ⟨11893309209235012641612625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15857745612313350188816833 11893309209235012641612625)
                  ·
                    refine ⟨8919981906926259481209469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11893309209235012641612625 8919981906926259481209469)
                    ·
                      refine ⟨3344993215097347305453551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8919981906926259481209469 3344993215097347305453551)
                      ·
                        rfl

theorem cell23_6514351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 2, 2, 3].length) (baseStart_6514351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514351 prefixEnd_6514351 := by exact prefixLift 6514351
  have htrace : WordTrace (prefixWord ++ tailWord_6514351) baseStart_6514351 baseEnd_6514351 := by
    simpa [prefixWord, tailWord_6514351, baseEnd_6514351] using wordTrace_append hprefix tailTrace_6514351
  have hstable : (prefixWord ++ tailWord_6514351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514351).length < 2 ^ (prefixWord ++ tailWord_6514351).sum := by decide
  have hdescent : baseEnd_6514351 < baseStart_6514351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514354 : List Nat := [3, 2, 1, 1, 1, 2, 4, 1, 8]
def baseStart_6514354 : Nat := 118140960795 + 6514354 * 2 ^ 59
def prefixEnd_6514354 : Nat := 4983230072969 + 3 ^ 40 * 6514354 * 2
def baseEnd_6514354 : Nat := 371666083948812310412893

theorem tailTrace_6514354 : CollatzResearch.WordTrace tailWord_6514354 prefixEnd_6514354 371666083948812310412893 := by
  unfold tailWord_6514354
  simp only [CollatzResearch.WordTrace]
  refine ⟨59399502460403873983159529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158398673227743663955092077 59399502460403873983159529)
  ·
    refine ⟨44549626845302905487369647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59399502460403873983159529 44549626845302905487369647)
    ·
      refine ⟨66824440267954358231054471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44549626845302905487369647 66824440267954358231054471)
      ·
        refine ⟨100236660401931537346581707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66824440267954358231054471 100236660401931537346581707)
        ·
          refine ⟨150354990602897306019872561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100236660401931537346581707 150354990602897306019872561)
          ·
            refine ⟨112766242952172979514904421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150354990602897306019872561 112766242952172979514904421)
            ·
              refine ⟨21143670553532433659044579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112766242952172979514904421 21143670553532433659044579)
              ·
                refine ⟨31715505830298650488566869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21143670553532433659044579 31715505830298650488566869)
                ·
                  refine ⟨371666083948812310412893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31715505830298650488566869 371666083948812310412893)
                  ·
                    rfl

theorem cell23_6514354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_6514354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514354 prefixEnd_6514354 := by exact prefixLift 6514354
  have htrace : WordTrace (prefixWord ++ tailWord_6514354) baseStart_6514354 baseEnd_6514354 := by
    simpa [prefixWord, tailWord_6514354, baseEnd_6514354] using wordTrace_append hprefix tailTrace_6514354
  have hstable : (prefixWord ++ tailWord_6514354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514354).length < 2 ^ (prefixWord ++ tailWord_6514354).sum := by decide
  have hdescent : baseEnd_6514354 < baseStart_6514354 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514415 : List Nat := [1, 1, 2, 1, 5, 1, 3, 4, 1, 1, 3]
def baseStart_6514415 : Nat := 118140960795 + 6514415 * 2 ^ 59
def prefixEnd_6514415 : Nat := 4983230072969 + 3 ^ 40 * 6514415 * 2
def baseEnd_6514415 : Nat := 3345026077859235055053257

theorem tailTrace_6514415 : CollatzResearch.WordTrace tailWord_6514415 prefixEnd_6514415 3345026077859235055053257 := by
  unfold tailWord_6514415
  simp only [CollatzResearch.WordTrace]
  refine ⟨237600234694394503350608699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158400156462929668900405799 237600234694394503350608699)
  ·
    refine ⟨356400352041591755025913049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237600234694394503350608699 356400352041591755025913049)
    ·
      refine ⟨267300264031193816269434787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356400352041591755025913049 267300264031193816269434787)
      ·
        refine ⟨400950396046790724404152181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267300264031193816269434787 400950396046790724404152181)
        ·
          refine ⟨37589099629386630412889267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 400950396046790724404152181 37589099629386630412889267)
          ·
            refine ⟨56383649444079945619333901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37589099629386630412889267 56383649444079945619333901)
            ·
              refine ⟨21143868541529979607250213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56383649444079945619333901 21143868541529979607250213)
              ·
                refine ⟨3964475351536871176359415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21143868541529979607250213 3964475351536871176359415)
                ·
                  refine ⟨5946713027305306764539123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3964475351536871176359415 5946713027305306764539123)
                  ·
                    refine ⟨8920069540957960146808685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5946713027305306764539123 8920069540957960146808685)
                    ·
                      refine ⟨3345026077859235055053257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8920069540957960146808685 3345026077859235055053257)
                      ·
                        rfl

theorem cell23_6514415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 4, 1, 1, 3].length) (baseStart_6514415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514415 prefixEnd_6514415 := by exact prefixLift 6514415
  have htrace : WordTrace (prefixWord ++ tailWord_6514415) baseStart_6514415 baseEnd_6514415 := by
    simpa [prefixWord, tailWord_6514415, baseEnd_6514415] using wordTrace_append hprefix tailTrace_6514415
  have hstable : (prefixWord ++ tailWord_6514415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514415).length < 2 ^ (prefixWord ++ tailWord_6514415).sum := by decide
  have hdescent : baseEnd_6514415 < baseStart_6514415 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514444 : List Nat := [2, 2, 1, 2, 2, 1, 2, 11]
def baseStart_6514444 : Nat := 118140960795 + 6514444 * 2 ^ 59
def prefixEnd_6514444 : Nat := 4983230072969 + 3 ^ 40 * 6514444 * 2
def baseEnd_6514444 : Nat := 123890406251785757095949

theorem tailTrace_6514444 : CollatzResearch.WordTrace tailWord_6514444 prefixEnd_6514444 123890406251785757095949 := by
  unfold tailWord_6514444
  simp only [CollatzResearch.WordTrace]
  refine ⟨118800646205644720651707193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158400861607526294202276257 118800646205644720651707193)
  ·
    refine ⟨89100484654233540488780395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118800646205644720651707193 89100484654233540488780395)
    ·
      refine ⟨133650726981350310733170593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89100484654233540488780395 133650726981350310733170593)
      ·
        refine ⟨100238045236012733049877945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133650726981350310733170593 100238045236012733049877945)
        ·
          refine ⟨75178533927009549787408459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100238045236012733049877945 75178533927009549787408459)
          ·
            refine ⟨112767800890514324681112689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75178533927009549787408459 112767800890514324681112689)
            ·
              refine ⟨84575850667885743510834517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112767800890514324681112689 84575850667885743510834517)
              ·
                refine ⟨123890406251785757095949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 84575850667885743510834517 123890406251785757095949)
                ·
                  rfl

theorem cell23_6514444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 11].length) (baseStart_6514444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514444 prefixEnd_6514444 := by exact prefixLift 6514444
  have htrace : WordTrace (prefixWord ++ tailWord_6514444) baseStart_6514444 baseEnd_6514444 := by
    simpa [prefixWord, tailWord_6514444, baseEnd_6514444] using wordTrace_append hprefix tailTrace_6514444
  have hstable : (prefixWord ++ tailWord_6514444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514444).length < 2 ^ (prefixWord ++ tailWord_6514444).sum := by decide
  have hdescent : baseEnd_6514444 < baseStart_6514444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514455 : List Nat := [1, 1, 3, 4, 2, 1, 4, 1, 1, 1, 4]
def baseStart_6514455 : Nat := 118140960795 + 6514455 * 2 ^ 59
def prefixEnd_6514455 : Nat := 4983230072969 + 3 ^ 40 * 6514455 * 2
def baseEnd_6514455 : Nat := 3345046617085414898553073

theorem tailTrace_6514455 : CollatzResearch.WordTrace tailWord_6514455 prefixEnd_6514455 3345046617085414898553073 := by
  unfold tailWord_6514455
  simp only [CollatzResearch.WordTrace]
  refine ⟨237601693614249590182064819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158401129076166393454709879 237601693614249590182064819)
  ·
    refine ⟨356402540421374385273097229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237601693614249590182064819 356402540421374385273097229)
    ·
      refine ⟨133650952658015394477411461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356402540421374385273097229 133650952658015394477411461)
      ·
        refine ⟨25059553623377886464514649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133650952658015394477411461 25059553623377886464514649)
        ·
          refine ⟨18794665217533414848385987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25059553623377886464514649 18794665217533414848385987)
          ·
            refine ⟨28191997826300122272578981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18794665217533414848385987 28191997826300122272578981)
            ·
              refine ⟨5285999592431272926108559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28191997826300122272578981 5285999592431272926108559)
              ·
                refine ⟨7928999388646909389162839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5285999592431272926108559 7928999388646909389162839)
                ·
                  refine ⟨11893499082970364083744259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7928999388646909389162839 11893499082970364083744259)
                  ·
                    refine ⟨17840248624455546125616389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11893499082970364083744259 17840248624455546125616389)
                    ·
                      refine ⟨3345046617085414898553073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17840248624455546125616389 3345046617085414898553073)
                      ·
                        rfl

theorem cell23_6514455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_6514455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514455 prefixEnd_6514455 := by exact prefixLift 6514455
  have htrace : WordTrace (prefixWord ++ tailWord_6514455) baseStart_6514455 baseEnd_6514455 := by
    simpa [prefixWord, tailWord_6514455, baseEnd_6514455] using wordTrace_append hprefix tailTrace_6514455
  have hstable : (prefixWord ++ tailWord_6514455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514455).length < 2 ^ (prefixWord ++ tailWord_6514455).sum := by decide
  have hdescent : baseEnd_6514455 < baseStart_6514455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514465 : List Nat := [1, 2, 3, 2, 1, 5, 1, 2, 2, 4]
def baseStart_6514465 : Nat := 118140960795 + 6514465 * 2 ^ 59
def prefixEnd_6514465 : Nat := 4983230072969 + 3 ^ 40 * 6514465 * 2
def baseEnd_6514465 : Nat := 1115017250630653286476009

theorem tailTrace_6514465 : CollatzResearch.WordTrace tailWord_6514465 prefixEnd_6514465 1115017250630653286476009 := by
  unfold tailWord_6514465
  simp only [CollatzResearch.WordTrace]
  refine ⟨237602058344213361889928849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158401372229475574593285899 237602058344213361889928849)
  ·
    refine ⟨178201543758160021417446637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237602058344213361889928849 178201543758160021417446637)
    ·
      refine ⟨66825578909310008031542489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178201543758160021417446637 66825578909310008031542489)
      ·
        refine ⟨50119184181982506023656867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66825578909310008031542489 50119184181982506023656867)
        ·
          refine ⟨75178776272973759035485301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50119184181982506023656867 75178776272973759035485301)
          ·
            refine ⟨7048010275591289909576747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75178776272973759035485301 7048010275591289909576747)
            ·
              refine ⟨10572015413386934864365121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7048010275591289909576747 10572015413386934864365121)
              ·
                refine ⟨7929011560040201148273841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10572015413386934864365121 7929011560040201148273841)
                ·
                  refine ⟨5946758670030150861205381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7929011560040201148273841 5946758670030150861205381)
                  ·
                    refine ⟨1115017250630653286476009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5946758670030150861205381 1115017250630653286476009)
                    ·
                      rfl

theorem cell23_6514465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_6514465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514465 prefixEnd_6514465 := by exact prefixLift 6514465
  have htrace : WordTrace (prefixWord ++ tailWord_6514465) baseStart_6514465 baseEnd_6514465 := by
    simpa [prefixWord, tailWord_6514465, baseEnd_6514465] using wordTrace_append hprefix tailTrace_6514465
  have hstable : (prefixWord ++ tailWord_6514465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514465).length < 2 ^ (prefixWord ++ tailWord_6514465).sum := by decide
  have hdescent : baseEnd_6514465 < baseStart_6514465 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514472 : List Nat := [2, 1, 5, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_6514472 : Nat := 118140960795 + 6514472 * 2 ^ 59
def prefixEnd_6514472 : Nat := 4983230072969 + 3 ^ 40 * 6514472 * 2
def baseEnd_6514472 : Nat := 3345055346256541332040495

theorem tailTrace_6514472 : CollatzResearch.WordTrace tailWord_6514472 prefixEnd_6514472 3345055346256541332040495 := by
  unfold tailWord_6514472
  simp only [CollatzResearch.WordTrace]
  refine ⟨118801156827594001042716835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158401542436792001390289113 118801156827594001042716835)
  ·
    refine ⟨178201735241391001564075253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118801156827594001042716835 178201735241391001564075253)
    ·
      refine ⟨16706412678880406396632055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178201735241391001564075253 16706412678880406396632055)
      ·
        refine ⟨25059619018320609594948083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16706412678880406396632055 25059619018320609594948083)
        ·
          refine ⟨37589428527480914392422125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25059619018320609594948083 37589428527480914392422125)
          ·
            refine ⟨14096035697805342897158297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37589428527480914392422125 14096035697805342897158297)
            ·
              refine ⟨10572026773354007172868723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14096035697805342897158297 10572026773354007172868723)
              ·
                refine ⟨15858040160031010759303085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10572026773354007172868723 15858040160031010759303085)
                ·
                  refine ⟨5946765060011629034738657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15858040160031010759303085 5946765060011629034738657)
                  ·
                    refine ⟨4460073795008721776053993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5946765060011629034738657 4460073795008721776053993)
                    ·
                      refine ⟨3345055346256541332040495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4460073795008721776053993 3345055346256541332040495)
                      ·
                        rfl

theorem cell23_6514472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_6514472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514472 prefixEnd_6514472 := by exact prefixLift 6514472
  have htrace : WordTrace (prefixWord ++ tailWord_6514472) baseStart_6514472 baseEnd_6514472 := by
    simpa [prefixWord, tailWord_6514472, baseEnd_6514472] using wordTrace_append hprefix tailTrace_6514472
  have hstable : (prefixWord ++ tailWord_6514472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514472).length < 2 ^ (prefixWord ++ tailWord_6514472).sum := by decide
  have hdescent : baseEnd_6514472 < baseStart_6514472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514485 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_6514485 : Nat := 118140960795 + 6514485 * 2 ^ 59
def prefixEnd_6514485 : Nat := 4983230072969 + 3 ^ 40 * 6514485 * 2
def baseEnd_6514485 : Nat := 3345062021505049781177935

theorem tailTrace_6514485 : CollatzResearch.WordTrace tailWord_6514485 prefixEnd_6514485 3345062021505049781177935 := by
  unfold tailWord_6514485
  simp only [CollatzResearch.WordTrace]
  refine ⟨237602787804140905305656909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158401858536093936870437939 237602787804140905305656909)
  ·
    refine ⟨89101045426552839489621341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237602787804140905305656909 89101045426552839489621341)
    ·
      refine ⟨33412892034957314808608003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89101045426552839489621341 33412892034957314808608003)
      ·
        refine ⟨50119338052435972212912005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33412892034957314808608003 50119338052435972212912005)
        ·
          refine ⟨9397375884831744789921001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50119338052435972212912005 9397375884831744789921001)
          ·
            refine ⟨7048031913623808592440751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9397375884831744789921001 7048031913623808592440751)
            ·
              refine ⟨10572047870435712888661127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7048031913623808592440751 10572047870435712888661127)
              ·
                refine ⟨15858071805653569332991691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10572047870435712888661127 15858071805653569332991691)
                ·
                  refine ⟨23787107708480353999487537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15858071805653569332991691 23787107708480353999487537)
                  ·
                    refine ⟨17840330781360265499615653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23787107708480353999487537 17840330781360265499615653)
                    ·
                      refine ⟨3345062021505049781177935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17840330781360265499615653 3345062021505049781177935)
                      ·
                        rfl

theorem cell23_6514485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_6514485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514485 prefixEnd_6514485 := by exact prefixLift 6514485
  have htrace : WordTrace (prefixWord ++ tailWord_6514485) baseStart_6514485 baseEnd_6514485 := by
    simpa [prefixWord, tailWord_6514485, baseEnd_6514485] using wordTrace_append hprefix tailTrace_6514485
  have hstable : (prefixWord ++ tailWord_6514485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514485).length < 2 ^ (prefixWord ++ tailWord_6514485).sum := by decide
  have hdescent : baseEnd_6514485 < baseStart_6514485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514488 : List Nat := [2, 1, 2, 1, 3, 3, 3, 1, 1, 3, 3]
def baseStart_6514488 : Nat := 118140960795 + 6514488 * 2 ^ 59
def prefixEnd_6514488 : Nat := 4983230072969 + 3 ^ 40 * 6514488 * 2
def baseEnd_6514488 : Nat := 3345063561947013269440421

theorem tailTrace_6514488 : CollatzResearch.WordTrace tailWord_6514488 prefixEnd_6514488 3345063561947013269440421 := by
  unfold tailWord_6514488
  simp only [CollatzResearch.WordTrace]
  refine ⟨118801448611565018409008059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158401931482086691212010745 118801448611565018409008059)
  ·
    refine ⟨178202172917347527613512089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118801448611565018409008059 178202172917347527613512089)
    ·
      refine ⟨133651629688010645710134067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178202172917347527613512089 133651629688010645710134067)
      ·
        refine ⟨200477444532015968565201101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133651629688010645710134067 200477444532015968565201101)
        ·
          refine ⟨75179041699505988211950413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200477444532015968565201101 75179041699505988211950413)
          ·
            refine ⟨28192140637314745579481405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75179041699505988211950413 28192140637314745579481405)
            ·
              refine ⟨10572052738993029592305527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28192140637314745579481405 10572052738993029592305527)
              ·
                refine ⟨15858079108489544388458291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10572052738993029592305527 15858079108489544388458291)
                ·
                  refine ⟨23787118662734316582687437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15858079108489544388458291 23787118662734316582687437)
                  ·
                    refine ⟨8920169498525368718507789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23787118662734316582687437 8920169498525368718507789)
                    ·
                      refine ⟨3345063561947013269440421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8920169498525368718507789 3345063561947013269440421)
                      ·
                        rfl

theorem cell23_6514488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 1, 1, 3, 3].length) (baseStart_6514488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514488 prefixEnd_6514488 := by exact prefixLift 6514488
  have htrace : WordTrace (prefixWord ++ tailWord_6514488) baseStart_6514488 baseEnd_6514488 := by
    simpa [prefixWord, tailWord_6514488, baseEnd_6514488] using wordTrace_append hprefix tailTrace_6514488
  have hstable : (prefixWord ++ tailWord_6514488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514488).length < 2 ^ (prefixWord ++ tailWord_6514488).sum := by decide
  have hdescent : baseEnd_6514488 < baseStart_6514488 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514495 : List Nat := [1, 1, 2, 2, 7, 1, 2, 7]
def baseStart_6514495 : Nat := 118140960795 + 6514495 * 2 ^ 59
def prefixEnd_6514495 : Nat := 4983230072969 + 3 ^ 40 * 6514495 * 2
def baseEnd_6514495 : Nat := 123891376159688694150107

theorem tailTrace_6514495 : CollatzResearch.WordTrace tailWord_6514495 prefixEnd_6514495 123891376159688694150107 := by
  unfold tailWord_6514495
  simp only [CollatzResearch.WordTrace]
  refine ⟨237603152534104677013520939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158402101689403118009013959 237603152534104677013520939)
  ·
    refine ⟨356404728801157015520281409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237603152534104677013520939 356404728801157015520281409)
    ·
      refine ⟨267303546600867761640211057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356404728801157015520281409 267303546600867761640211057)
      ·
        refine ⟨200477659950650821230158293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267303546600867761640211057 200477659950650821230158293)
        ·
          refine ⟨4698695155093378622581835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 200477659950650821230158293 4698695155093378622581835)
          ·
            refine ⟨7048042732640067933872753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4698695155093378622581835 7048042732640067933872753)
            ·
              refine ⟨5286032049480050950404565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7048042732640067933872753 5286032049480050950404565)
              ·
                refine ⟨123891376159688694150107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5286032049480050950404565 123891376159688694150107)
                ·
                  rfl

theorem cell23_6514495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 2, 7].length) (baseStart_6514495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514495 prefixEnd_6514495 := by exact prefixLift 6514495
  have htrace : WordTrace (prefixWord ++ tailWord_6514495) baseStart_6514495 baseEnd_6514495 := by
    simpa [prefixWord, tailWord_6514495, baseEnd_6514495] using wordTrace_append hprefix tailTrace_6514495
  have hstable : (prefixWord ++ tailWord_6514495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514495).length < 2 ^ (prefixWord ++ tailWord_6514495).sum := by decide
  have hdescent : baseEnd_6514495 < baseStart_6514495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514585 : List Nat := [1, 2, 1, 2, 1, 3, 6, 2, 5]
def baseStart_6514585 : Nat := 118140960795 + 6514585 * 2 ^ 59
def prefixEnd_6514585 : Nat := 4983230072969 + 3 ^ 40 * 6514585 * 2
def baseEnd_6514585 : Nat := 371679263285611043325275

theorem tailTrace_6514585 : CollatzResearch.WordTrace tailWord_6514585 prefixEnd_6514585 371679263285611043325275 := by
  unfold tailWord_6514585
  simp only [CollatzResearch.WordTrace]
  refine ⟨237606435103778622384297209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158404290069185748256198139 237606435103778622384297209)
  ·
    refine ⟨178204826327833966788222907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237606435103778622384297209 178204826327833966788222907)
    ·
      refine ⟨267307239491750950182334361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178204826327833966788222907 267307239491750950182334361)
      ·
        refine ⟨200480429618813212636750771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267307239491750950182334361 200480429618813212636750771)
        ·
          refine ⟨300720644428219818955126157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200480429618813212636750771 300720644428219818955126157)
          ·
            refine ⟨112770241660582432108172309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300720644428219818955126157 112770241660582432108172309)
            ·
              refine ⟨5286105077839801505070577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112770241660582432108172309 5286105077839801505070577)
              ·
                refine ⟨3964578808379851128802933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5286105077839801505070577 3964578808379851128802933)
                ·
                  refine ⟨371679263285611043325275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3964578808379851128802933 371679263285611043325275)
                  ·
                    rfl

theorem cell23_6514585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 6, 2, 5].length) (baseStart_6514585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514585 prefixEnd_6514585 := by exact prefixLift 6514585
  have htrace : WordTrace (prefixWord ++ tailWord_6514585) baseStart_6514585 baseEnd_6514585 := by
    simpa [prefixWord, tailWord_6514585, baseEnd_6514585] using wordTrace_append hprefix tailTrace_6514585
  have hstable : (prefixWord ++ tailWord_6514585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514585).length < 2 ^ (prefixWord ++ tailWord_6514585).sum := by decide
  have hdescent : baseEnd_6514585 < baseStart_6514585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514618 : List Nat := [3, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4]
def baseStart_6514618 : Nat := 118140960795 + 6514618 * 2 ^ 59
def prefixEnd_6514618 : Nat := 4983230072969 + 3 ^ 40 * 6514618 * 2
def baseEnd_6514618 : Nat := 3345130314432097760814823

theorem tailTrace_6514618 : CollatzResearch.WordTrace tailWord_6514618 prefixEnd_6514618 3345130314432097760814823 := by
  unfold tailWord_6514618
  simp only [CollatzResearch.WordTrace]
  refine ⟨59401909678164767255062127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158405092475106046013499005 59401909678164767255062127)
  ·
    refine ⟨89102864517247150882593191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59401909678164767255062127 89102864517247150882593191)
    ·
      refine ⟨133654296775870726323889787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89102864517247150882593191 133654296775870726323889787)
      ·
        refine ⟨200481445163806089485834681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133654296775870726323889787 200481445163806089485834681)
        ·
          refine ⟨150361083872854567114376011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200481445163806089485834681 150361083872854567114376011)
          ·
            refine ⟨225541625809281850671564017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150361083872854567114376011 225541625809281850671564017)
            ·
              refine ⟨169156219356961388003673013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225541625809281850671564017 169156219356961388003673013)
              ·
                refine ⟨15858395564715130125344345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169156219356961388003673013 15858395564715130125344345)
                ·
                  refine ⟨11893796673536347594008259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15858395564715130125344345 11893796673536347594008259)
                  ·
                    refine ⟨17840695010304521391012389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11893796673536347594008259 17840695010304521391012389)
                    ·
                      refine ⟨3345130314432097760814823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17840695010304521391012389 3345130314432097760814823)
                      ·
                        rfl

theorem cell23_6514618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4].length) (baseStart_6514618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514618 prefixEnd_6514618 := by exact prefixLift 6514618
  have htrace : WordTrace (prefixWord ++ tailWord_6514618) baseStart_6514618 baseEnd_6514618 := by
    simpa [prefixWord, tailWord_6514618, baseEnd_6514618] using wordTrace_append hprefix tailTrace_6514618
  have hstable : (prefixWord ++ tailWord_6514618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514618).length < 2 ^ (prefixWord ++ tailWord_6514618).sum := by decide
  have hdescent : baseEnd_6514618 < baseStart_6514618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514645 : List Nat := [1, 3, 2, 3, 2, 1, 1, 3, 3, 4]
def baseStart_6514645 : Nat := 118140960795 + 6514645 * 2 ^ 59
def prefixEnd_6514645 : Nat := 4983230072969 + 3 ^ 40 * 6514645 * 2
def baseEnd_6514645 : Nat := 1115048059469923051725733

theorem tailTrace_6514645 : CollatzResearch.WordTrace tailWord_6514645 prefixEnd_6514645 1115048059469923051725733 := by
  unfold tailWord_6514645
  simp only [CollatzResearch.WordTrace]
  refine ⟨237608623483561252631481389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158405748989040835087654259 237608623483561252631481389)
  ·
    refine ⟨89103233806335469736805521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237608623483561252631481389 89103233806335469736805521)
    ·
      refine ⟨66827425354751602302604141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89103233806335469736805521 66827425354751602302604141)
      ·
        refine ⟨25060284508031850863476553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66827425354751602302604141 25060284508031850863476553)
        ·
          refine ⟨18795213381023888147607415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25060284508031850863476553 18795213381023888147607415)
          ·
            refine ⟨28192820071535832221411123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18795213381023888147607415 28192820071535832221411123)
            ·
              refine ⟨42289230107303748332116685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28192820071535832221411123 42289230107303748332116685)
              ·
                refine ⟨15858461290238905624543757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42289230107303748332116685 15858461290238905624543757)
                ·
                  refine ⟨5946922983839589609203909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15858461290238905624543757 5946922983839589609203909)
                  ·
                    refine ⟨1115048059469923051725733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5946922983839589609203909 1115048059469923051725733)
                    ·
                      rfl

theorem cell23_6514645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_6514645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514645 prefixEnd_6514645 := by exact prefixLift 6514645
  have htrace : WordTrace (prefixWord ++ tailWord_6514645) baseStart_6514645 baseEnd_6514645 := by
    simpa [prefixWord, tailWord_6514645, baseEnd_6514645] using wordTrace_append hprefix tailTrace_6514645
  have hstable : (prefixWord ++ tailWord_6514645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514645).length < 2 ^ (prefixWord ++ tailWord_6514645).sum := by decide
  have hdescent : baseEnd_6514645 < baseStart_6514645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514685 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 5, 1, 3]
def baseStart_6514685 : Nat := 118140960795 + 6514685 * 2 ^ 59
def prefixEnd_6514685 : Nat := 4983230072969 + 3 ^ 40 * 6514685 * 2
def baseEnd_6514685 : Nat := 3345164717635948998677015

theorem tailTrace_6514685 : CollatzResearch.WordTrace tailWord_6514685 prefixEnd_6514685 3345164717635948998677015 := by
  unfold tailWord_6514685
  simp only [CollatzResearch.WordTrace]
  refine ⟨237610082403416339462937509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158406721602277559641958339 237610082403416339462937509)
  ·
    refine ⟨44551890450640563649300783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237610082403416339462937509 44551890450640563649300783)
    ·
      refine ⟨66827835675960845473951175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44551890450640563649300783 66827835675960845473951175)
      ·
        refine ⟨100241753513941268210926763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66827835675960845473951175 100241753513941268210926763)
        ·
          refine ⟨150362630270911902316390145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100241753513941268210926763 150362630270911902316390145)
          ·
            refine ⟨112771972703183926737292609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150362630270911902316390145 112771972703183926737292609)
            ·
              refine ⟨84578979527387945052969457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112771972703183926737292609 84578979527387945052969457)
              ·
                refine ⟨63434234645540958789727093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84578979527387945052969457 63434234645540958789727093)
                ·
                  refine ⟨5946959498019464886536915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63434234645540958789727093 5946959498019464886536915)
                  ·
                    refine ⟨8920439247029197329805373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5946959498019464886536915 8920439247029197329805373)
                    ·
                      refine ⟨3345164717635948998677015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8920439247029197329805373 3345164717635948998677015)
                      ·
                        rfl

theorem cell23_6514685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_6514685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514685 prefixEnd_6514685 := by exact prefixLift 6514685
  have htrace : WordTrace (prefixWord ++ tailWord_6514685) baseStart_6514685 baseEnd_6514685 := by
    simpa [prefixWord, tailWord_6514685, baseEnd_6514685] using wordTrace_append hprefix tailTrace_6514685
  have hstable : (prefixWord ++ tailWord_6514685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514685).length < 2 ^ (prefixWord ++ tailWord_6514685).sum := by decide
  have hdescent : baseEnd_6514685 < baseStart_6514685 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514709 : List Nat := [1, 3, 2, 1, 6, 1, 2, 1, 6]
def baseStart_6514709 : Nat := 118140960795 + 6514709 * 2 ^ 59
def prefixEnd_6514709 : Nat := 4983230072969 + 3 ^ 40 * 6514709 * 2
def baseEnd_6514709 : Nat := 371686337907961878308545

theorem tailTrace_6514709 : CollatzResearch.WordTrace tailWord_6514709 prefixEnd_6514709 371686337907961878308545 := by
  unfold tailWord_6514709
  simp only [CollatzResearch.WordTrace]
  refine ⟨237610957755329391561811181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158407305170219594374540787 237610957755329391561811181)
  ·
    refine ⟨89104109158248521835679193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237610957755329391561811181 89104109158248521835679193)
    ·
      refine ⟨66828081868686391376759395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89104109158248521835679193 66828081868686391376759395)
      ·
        refine ⟨100242122803029587065139093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66828081868686391376759395 100242122803029587065139093)
        ·
          refine ⟨4698849506392011893678395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100242122803029587065139093 4698849506392011893678395)
          ·
            refine ⟨7048274259588017840517593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4698849506392011893678395 7048274259588017840517593)
            ·
              refine ⟨5286205694691013380388195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7048274259588017840517593 5286205694691013380388195)
              ·
                refine ⟨7929308542036520070582293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5286205694691013380388195 7929308542036520070582293)
                ·
                  refine ⟨371686337907961878308545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7929308542036520070582293 371686337907961878308545)
                  ·
                    rfl

theorem cell23_6514709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 2, 1, 6].length) (baseStart_6514709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514709 prefixEnd_6514709 := by exact prefixLift 6514709
  have htrace : WordTrace (prefixWord ++ tailWord_6514709) baseStart_6514709 baseEnd_6514709 := by
    simpa [prefixWord, tailWord_6514709, baseEnd_6514709] using wordTrace_append hprefix tailTrace_6514709
  have hstable : (prefixWord ++ tailWord_6514709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514709).length < 2 ^ (prefixWord ++ tailWord_6514709).sum := by decide
  have hdescent : baseEnd_6514709 < baseStart_6514709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514725 : List Nat := [1, 3, 1, 2, 2, 4, 1, 1, 3, 1, 4]
def baseStart_6514725 : Nat := 118140960795 + 6514725 * 2 ^ 59
def prefixEnd_6514725 : Nat := 4983230072969 + 3 ^ 40 * 6514725 * 2
def baseEnd_6514725 : Nat := 3345185256862128842176831

theorem tailTrace_6514725 : CollatzResearch.WordTrace tailWord_6514725 prefixEnd_6514725 3345185256862128842176831 := by
  unfold tailWord_6514725
  simp only [CollatzResearch.WordTrace]
  refine ⟨237611541323271426294393629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158407694215514284196262419 237611541323271426294393629)
  ·
    refine ⟨89104327996226784860397611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237611541323271426294393629 89104327996226784860397611)
    ·
      refine ⟨133656491994340177290596417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89104327996226784860397611 133656491994340177290596417)
      ·
        refine ⟨100242368995755132967947313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133656491994340177290596417 100242368995755132967947313)
        ·
          refine ⟨75181776746816349725960485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100242368995755132967947313 75181776746816349725960485)
          ·
            refine ⟨14096583140028065573617591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75181776746816349725960485 14096583140028065573617591)
            ·
              refine ⟨21144874710042098360426387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14096583140028065573617591 21144874710042098360426387)
              ·
                refine ⟨31717312065063147540639581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21144874710042098360426387 31717312065063147540639581)
                ·
                  refine ⟨11893992024398680327739843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31717312065063147540639581 11893992024398680327739843)
                  ·
                    refine ⟨17840988036598020491609765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11893992024398680327739843 17840988036598020491609765)
                    ·
                      refine ⟨3345185256862128842176831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17840988036598020491609765 3345185256862128842176831)
                      ·
                        rfl

theorem cell23_6514725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_6514725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514725 prefixEnd_6514725 := by exact prefixLift 6514725
  have htrace : WordTrace (prefixWord ++ tailWord_6514725) baseStart_6514725 baseEnd_6514725 := by
    simpa [prefixWord, tailWord_6514725, baseEnd_6514725] using wordTrace_append hprefix tailTrace_6514725
  have hstable : (prefixWord ++ tailWord_6514725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514725).length < 2 ^ (prefixWord ++ tailWord_6514725).sum := by decide
  have hdescent : baseEnd_6514725 < baseStart_6514725 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514752 : List Nat := [2, 1, 1, 2, 2, 5, 2, 2, 2, 4]
def baseStart_6514752 : Nat := 118140960795 + 6514752 * 2 ^ 59
def prefixEnd_6514752 : Nat := 4983230072969 + 3 ^ 40 * 6514752 * 2
def baseEnd_6514752 : Nat := 1115066373613266745513069

theorem tailTrace_6514752 : CollatzResearch.WordTrace tailWord_6514752 prefixEnd_6514752 1115066373613266745513069 := by
  unfold tailWord_6514752
  simp only [CollatzResearch.WordTrace]
  refine ⟨118806263047086804952813255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158408350729449073270417673 118806263047086804952813255)
  ·
    refine ⟨178209394570630207429219883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118806263047086804952813255 178209394570630207429219883)
    ·
      refine ⟨267314091855945311143829825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178209394570630207429219883 267314091855945311143829825)
      ·
        refine ⟨200485568891958983357872369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267314091855945311143829825 200485568891958983357872369)
        ·
          refine ⟨150364176668969237518404277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200485568891958983357872369 150364176668969237518404277)
          ·
            refine ⟨14096641562715866017350401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150364176668969237518404277 14096641562715866017350401)
            ·
              refine ⟨10572481172036899513012801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14096641562715866017350401 10572481172036899513012801)
              ·
                refine ⟨7929360879027674634759601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10572481172036899513012801 7929360879027674634759601)
                ·
                  refine ⟨5947020659270755976069701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7929360879027674634759601 5947020659270755976069701)
                  ·
                    refine ⟨1115066373613266745513069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5947020659270755976069701 1115066373613266745513069)
                    ·
                      rfl

theorem cell23_6514752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 2, 2, 2, 4].length) (baseStart_6514752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514752 prefixEnd_6514752 := by exact prefixLift 6514752
  have htrace : WordTrace (prefixWord ++ tailWord_6514752) baseStart_6514752 baseEnd_6514752 := by
    simpa [prefixWord, tailWord_6514752, baseEnd_6514752] using wordTrace_append hprefix tailTrace_6514752
  have hstable : (prefixWord ++ tailWord_6514752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514752).length < 2 ^ (prefixWord ++ tailWord_6514752).sum := by decide
  have hdescent : baseEnd_6514752 < baseStart_6514752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514753 : List Nat := [1, 2, 5, 1, 2, 3, 2, 2, 1, 1, 3]
def baseStart_6514753 : Nat := 118140960795 + 6514753 * 2 ^ 59
def prefixEnd_6514753 : Nat := 4983230072969 + 3 ^ 40 * 6514753 * 2
def baseEnd_6514753 : Nat := 3345199634320454732626703

theorem tailTrace_6514753 : CollatzResearch.WordTrace tailWord_6514753 prefixEnd_6514753 3345199634320454732626703 := by
  unfold tailWord_6514753
  simp only [CollatzResearch.WordTrace]
  refine ⟨237612562567169987076412913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158408375044779991384275275 237612562567169987076412913)
  ·
    refine ⟨178209421925377490307309685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237612562567169987076412913 178209421925377490307309685)
    ·
      refine ⟨16707133305504139716310283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178209421925377490307309685 16707133305504139716310283)
      ·
        refine ⟨25060699958256209574465425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16707133305504139716310283 25060699958256209574465425)
        ·
          refine ⟨18795524968692157180849069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25060699958256209574465425 18795524968692157180849069)
          ·
            refine ⟨7048321863259558942818401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18795524968692157180849069 7048321863259558942818401)
            ·
              refine ⟨5286241397444669207113801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7048321863259558942818401 5286241397444669207113801)
              ·
                refine ⟨3964681048083501905335351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5286241397444669207113801 3964681048083501905335351)
                ·
                  refine ⟨5947021572125252858003027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3964681048083501905335351 5947021572125252858003027)
                  ·
                    refine ⟨8920532358187879287004541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5947021572125252858003027 8920532358187879287004541)
                    ·
                      refine ⟨3345199634320454732626703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8920532358187879287004541 3345199634320454732626703)
                      ·
                        rfl

theorem cell23_6514753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_6514753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514753 prefixEnd_6514753 := by exact prefixLift 6514753
  have htrace : WordTrace (prefixWord ++ tailWord_6514753) baseStart_6514753 baseEnd_6514753 := by
    simpa [prefixWord, tailWord_6514753, baseEnd_6514753] using wordTrace_append hprefix tailTrace_6514753
  have hstable : (prefixWord ++ tailWord_6514753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514753).length < 2 ^ (prefixWord ++ tailWord_6514753).sum := by decide
  have hdescent : baseEnd_6514753 < baseStart_6514753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514775 : List Nat := [1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 3]
def baseStart_6514775 : Nat := 118140960795 + 6514775 * 2 ^ 59
def prefixEnd_6514775 : Nat := 4983230072969 + 3 ^ 40 * 6514775 * 2
def baseEnd_6514775 : Nat := 3345210930894853646551601

theorem tailTrace_6514775 : CollatzResearch.WordTrace tailWord_6514775 prefixEnd_6514775 3345210930894853646551601 := by
  unfold tailWord_6514775
  simp only [CollatzResearch.WordTrace]
  refine ⟨237613364973090284833713779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158408909982060189889142519 237613364973090284833713779)
  ·
    refine ⟨356420047459635427250570669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237613364973090284833713779 356420047459635427250570669)
    ·
      refine ⟨133657517797363285218964001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356420047459635427250570669 133657517797363285218964001)
      ·
        refine ⟨100243138348022463914223001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133657517797363285218964001 100243138348022463914223001)
        ·
          refine ⟨75182353761016847935667251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100243138348022463914223001 75182353761016847935667251)
          ·
            refine ⟨112773530641525271903500877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75182353761016847935667251 112773530641525271903500877)
            ·
              refine ⟨42290073990571976963812829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112773530641525271903500877 42290073990571976963812829)
              ·
                refine ⟨15858777746464491361429811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42290073990571976963812829 15858777746464491361429811)
                ·
                  refine ⟨23788166619696737042144717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15858777746464491361429811 23788166619696737042144717)
                  ·
                    refine ⟨8920562482386276390804269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23788166619696737042144717 8920562482386276390804269)
                    ·
                      refine ⟨3345210930894853646551601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8920562482386276390804269 3345210930894853646551601)
                      ·
                        rfl

theorem cell23_6514775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_6514775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514775 prefixEnd_6514775 := by exact prefixLift 6514775
  have htrace : WordTrace (prefixWord ++ tailWord_6514775) baseStart_6514775 baseEnd_6514775 := by
    simpa [prefixWord, tailWord_6514775, baseEnd_6514775] using wordTrace_append hprefix tailTrace_6514775
  have hstable : (prefixWord ++ tailWord_6514775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514775).length < 2 ^ (prefixWord ++ tailWord_6514775).sum := by decide
  have hdescent : baseEnd_6514775 < baseStart_6514775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514778 : List Nat := [3, 1, 1, 2, 1, 1, 3, 2, 2, 7]
def baseStart_6514778 : Nat := 118140960795 + 6514778 * 2 ^ 59
def prefixEnd_6514778 : Nat := 4983230072969 + 3 ^ 40 * 6514778 * 2
def baseEnd_6514778 : Nat := 1115070823778939044938029

theorem tailTrace_6514778 : CollatzResearch.WordTrace tailWord_6514778 prefixEnd_6514778 1115070823778939044938029 := by
  unfold tailWord_6514778
  simp only [CollatzResearch.WordTrace]
  refine ⟨59403368598019854086518247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158408982928052944230715325 59403368598019854086518247)
  ·
    refine ⟨89105052897029781129777371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59403368598019854086518247 89105052897029781129777371)
    ·
      refine ⟨133657579345544671694666057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89105052897029781129777371 133657579345544671694666057)
      ·
        refine ⟨100243184509158503770999543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133657579345544671694666057 100243184509158503770999543)
        ·
          refine ⟨150364776763737755656499315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100243184509158503770999543 150364776763737755656499315)
          ·
            refine ⟨225547165145606633484748973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150364776763737755656499315 225547165145606633484748973)
            ·
              refine ⟨84580186929602487556780865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225547165145606633484748973 84580186929602487556780865)
              ·
                refine ⟨63435140197201865667585649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84580186929602487556780865 63435140197201865667585649)
                ·
                  refine ⟨47576355147901399250689237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63435140197201865667585649 47576355147901399250689237)
                  ·
                    refine ⟨1115070823778939044938029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47576355147901399250689237 1115070823778939044938029)
                    ·
                      rfl

theorem cell23_6514778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_6514778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514778 prefixEnd_6514778 := by exact prefixLift 6514778
  have htrace : WordTrace (prefixWord ++ tailWord_6514778) baseStart_6514778 baseEnd_6514778 := by
    simpa [prefixWord, tailWord_6514778, baseEnd_6514778] using wordTrace_append hprefix tailTrace_6514778
  have hstable : (prefixWord ++ tailWord_6514778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514778).length < 2 ^ (prefixWord ++ tailWord_6514778).sum := by decide
  have hdescent : baseEnd_6514778 < baseStart_6514778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514809 : List Nat := [1, 2, 1, 3, 4, 1, 3, 2, 2, 1, 3]
def baseStart_6514809 : Nat := 118140960795 + 6514809 * 2 ^ 59
def prefixEnd_6514809 : Nat := 4983230072969 + 3 ^ 40 * 6514809 * 2
def baseEnd_6514809 : Nat := 3345228389237106513526445

theorem tailTrace_6514809 : CollatzResearch.WordTrace tailWord_6514809 prefixEnd_6514809 3345228389237106513526445 := by
  unfold tailWord_6514809
  simp only [CollatzResearch.WordTrace]
  refine ⟨237614605054967108640451481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158409736703311405760300987 237614605054967108640451481)
  ·
    refine ⟨178210953791225331480338611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237614605054967108640451481 178210953791225331480338611)
    ·
      refine ⟨267316430686837997220507917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178210953791225331480338611 267316430686837997220507917)
      ·
        refine ⟨100243661507564248957690469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267316430686837997220507917 100243661507564248957690469)
        ·
          refine ⟨18795686532668296679566963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100243661507564248957690469 18795686532668296679566963)
          ·
            refine ⟨28193529799002445019350445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18795686532668296679566963 28193529799002445019350445)
            ·
              refine ⟨10572573674625916882256417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28193529799002445019350445 10572573674625916882256417)
              ·
                refine ⟨7929430255969437661692313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10572573674625916882256417 7929430255969437661692313)
                ·
                  refine ⟨5947072691977078246269235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7929430255969437661692313 5947072691977078246269235)
                  ·
                    refine ⟨8920609037965617369403853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5947072691977078246269235 8920609037965617369403853)
                    ·
                      refine ⟨3345228389237106513526445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8920609037965617369403853 3345228389237106513526445)
                      ·
                        rfl

theorem cell23_6514809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 1, 3].length) (baseStart_6514809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514809 prefixEnd_6514809 := by exact prefixLift 6514809
  have htrace : WordTrace (prefixWord ++ tailWord_6514809) baseStart_6514809 baseEnd_6514809 := by
    simpa [prefixWord, tailWord_6514809, baseEnd_6514809] using wordTrace_append hprefix tailTrace_6514809
  have hstable : (prefixWord ++ tailWord_6514809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514809).length < 2 ^ (prefixWord ++ tailWord_6514809).sum := by decide
  have hdescent : baseEnd_6514809 < baseStart_6514809 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514815 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 1, 10, 2]
def baseStart_6514815 : Nat := 118140960795 + 6514815 * 2 ^ 59
def prefixEnd_6514815 : Nat := 4983230072969 + 3 ^ 40 * 6514815 * 2
def baseEnd_6514815 : Nat := 3345231470121033490051417

theorem tailTrace_6514815 : CollatzResearch.WordTrace tailWord_6514815 prefixEnd_6514815 3345231470121033490051417 := by
  unfold tailWord_6514815
  simp only [CollatzResearch.WordTrace]
  refine ⟨237614823892945371665169899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158409882595296914443446599 237614823892945371665169899)
  ·
    refine ⟨356422235839418057497754849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237614823892945371665169899 356422235839418057497754849)
    ·
      refine ⟨267316676879563543123316137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356422235839418057497754849 267316676879563543123316137)
      ·
        refine ⟨200487507659672657342487103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267316676879563543123316137 200487507659672657342487103)
        ·
          refine ⟨300731261489508986013730655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200487507659672657342487103 300731261489508986013730655)
          ·
            refine ⟨451096892234263479020595983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300731261489508986013730655 451096892234263479020595983)
            ·
              refine ⟨676645338351395218530893975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451096892234263479020595983 676645338351395218530893975)
              ·
                refine ⟨1014968007527092827796340963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676645338351395218530893975 1014968007527092827796340963)
                ·
                  refine ⟨1522452011290639241694511445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014968007527092827796340963 1522452011290639241694511445)
                  ·
                    refine ⟨4460308626828044653401889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 1522452011290639241694511445 4460308626828044653401889)
                    ·
                      refine ⟨3345231470121033490051417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4460308626828044653401889 3345231470121033490051417)
                      ·
                        rfl

theorem cell23_6514815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 10, 2].length) (baseStart_6514815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514815 prefixEnd_6514815 := by exact prefixLift 6514815
  have htrace : WordTrace (prefixWord ++ tailWord_6514815) baseStart_6514815 baseEnd_6514815 := by
    simpa [prefixWord, tailWord_6514815, baseEnd_6514815] using wordTrace_append hprefix tailTrace_6514815
  have hstable : (prefixWord ++ tailWord_6514815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514815).length < 2 ^ (prefixWord ++ tailWord_6514815).sum := by decide
  have hdescent : baseEnd_6514815 < baseStart_6514815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514826 : List Nat := [3, 1, 2, 3, 1, 3, 3, 1, 2, 1, 3]
def baseStart_6514826 : Nat := 118140960795 + 6514826 * 2 ^ 59
def prefixEnd_6514826 : Nat := 4983230072969 + 3 ^ 40 * 6514826 * 2
def baseEnd_6514826 : Nat := 3345237118408232947013867

theorem tailTrace_6514826 : CollatzResearch.WordTrace tailWord_6514826 prefixEnd_6514826 3345237118408232947013867 := by
  unfold tailWord_6514826
  simp only [CollatzResearch.WordTrace]
  refine ⟨59403806273976380135955083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158410150063937013695880221 59403806273976380135955083)
  ·
    refine ⟨89105709410964570203932625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59403806273976380135955083 89105709410964570203932625)
    ·
      refine ⟨66829282058223427652949469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89105709410964570203932625 66829282058223427652949469)
      ·
        refine ⟨25060980771833785369856051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66829282058223427652949469 25060980771833785369856051)
        ·
          refine ⟨37591471157750678054784077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25060980771833785369856051 37591471157750678054784077)
          ·
            refine ⟨14096801684156504270544029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37591471157750678054784077 14096801684156504270544029)
            ·
              refine ⟨5286300631558689101454011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14096801684156504270544029 5286300631558689101454011)
              ·
                refine ⟨7929450947338033652181017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5286300631558689101454011 7929450947338033652181017)
                ·
                  refine ⟨5947088210503525239135763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7929450947338033652181017 5947088210503525239135763)
                  ·
                    refine ⟨8920632315755287858703645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5947088210503525239135763 8920632315755287858703645)
                    ·
                      refine ⟨3345237118408232947013867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8920632315755287858703645 3345237118408232947013867)
                      ·
                        rfl

theorem cell23_6514826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_6514826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514826 prefixEnd_6514826 := by exact prefixLift 6514826
  have htrace : WordTrace (prefixWord ++ tailWord_6514826) baseStart_6514826 baseEnd_6514826 := by
    simpa [prefixWord, tailWord_6514826, baseEnd_6514826] using wordTrace_append hprefix tailTrace_6514826
  have hstable : (prefixWord ++ tailWord_6514826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514826).length < 2 ^ (prefixWord ++ tailWord_6514826).sum := by decide
  have hdescent : baseEnd_6514826 < baseStart_6514826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514849 : List Nat := [1, 2, 3, 3, 1, 2, 1, 2, 4, 2, 2]
def baseStart_6514849 : Nat := 118140960795 + 6514849 * 2 ^ 59
def prefixEnd_6514849 : Nat := 4983230072969 + 3 ^ 40 * 6514849 * 2
def baseEnd_6514849 : Nat := 3345248928463286357026261

theorem tailTrace_6514849 : CollatzResearch.WordTrace tailWord_6514849 prefixEnd_6514849 3345248928463286357026261 := by
  unfold tailWord_6514849
  simp only [CollatzResearch.WordTrace]
  refine ⟨237616063974822195471907601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158410709316548130314605067 237616063974822195471907601)
  ·
    refine ⟨178212047981116646603930701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237616063974822195471907601 178212047981116646603930701)
    ·
      refine ⟨66829517992918742476474013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178212047981116646603930701 66829517992918742476474013)
      ·
        refine ⟨25061069247344528428677755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66829517992918742476474013 25061069247344528428677755)
        ·
          refine ⟨37591603871016792643016633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25061069247344528428677755 37591603871016792643016633)
          ·
            refine ⟨28193702903262594482262475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37591603871016792643016633 28193702903262594482262475)
            ·
              refine ⟨42290554354893891723393713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28193702903262594482262475 42290554354893891723393713)
              ·
                refine ⟨31717915766170418792545285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42290554354893891723393713 31717915766170418792545285)
                ·
                  refine ⟨5947109206156953523602241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31717915766170418792545285 5947109206156953523602241)
                  ·
                    refine ⟨4460331904617715142701681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5947109206156953523602241 4460331904617715142701681)
                    ·
                      refine ⟨3345248928463286357026261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4460331904617715142701681 3345248928463286357026261)
                      ·
                        rfl

theorem cell23_6514849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_6514849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514849 prefixEnd_6514849 := by exact prefixLift 6514849
  have htrace : WordTrace (prefixWord ++ tailWord_6514849) baseStart_6514849 baseEnd_6514849 := by
    simpa [prefixWord, tailWord_6514849, baseEnd_6514849] using wordTrace_append hprefix tailTrace_6514849
  have hstable : (prefixWord ++ tailWord_6514849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514849).length < 2 ^ (prefixWord ++ tailWord_6514849).sum := by decide
  have hdescent : baseEnd_6514849 < baseStart_6514849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514852 : List Nat := [2, 3, 1, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_6514852 : Nat := 118140960795 + 6514852 * 2 ^ 59
def prefixEnd_6514852 : Nat := 4983230072969 + 3 ^ 40 * 6514852 * 2
def baseEnd_6514852 : Nat := 3345250468905249845288747

theorem tailTrace_6514852 : CollatzResearch.WordTrace tailWord_6514852 prefixEnd_6514852 3345250468905249845288747 := by
  unfold tailWord_6514852
  simp only [CollatzResearch.WordTrace]
  refine ⟨118808086696905663492133405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158410782262540884656177873 118808086696905663492133405)
  ·
    refine ⟨44553032511339623809550027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118808086696905663492133405 44553032511339623809550027)
    ·
      refine ⟨66829548767009435714325041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44553032511339623809550027 66829548767009435714325041)
      ·
        refine ⟨50122161575257076785743781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66829548767009435714325041 50122161575257076785743781)
        ·
          refine ⟨9397905295360701897326959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50122161575257076785743781 9397905295360701897326959)
          ·
            refine ⟨14096857943041052845990439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9397905295360701897326959 14096857943041052845990439)
            ·
              refine ⟨21145286914561579268985659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14096857943041052845990439 21145286914561579268985659)
              ·
                refine ⟨31717930371842368903478489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21145286914561579268985659 31717930371842368903478489)
                ·
                  refine ⟨23788447778881776677608867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31717930371842368903478489 23788447778881776677608867)
                  ·
                    refine ⟨35682671668322665016413301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23788447778881776677608867 35682671668322665016413301)
                    ·
                      refine ⟨3345250468905249845288747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35682671668322665016413301 3345250468905249845288747)
                      ·
                        rfl

theorem cell23_6514852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_6514852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514852 prefixEnd_6514852 := by exact prefixLift 6514852
  have htrace : WordTrace (prefixWord ++ tailWord_6514852) baseStart_6514852 baseEnd_6514852 := by
    simpa [prefixWord, tailWord_6514852, baseEnd_6514852] using wordTrace_append hprefix tailTrace_6514852
  have hstable : (prefixWord ++ tailWord_6514852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514852).length < 2 ^ (prefixWord ++ tailWord_6514852).sum := by decide
  have hdescent : baseEnd_6514852 < baseStart_6514852 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514905 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 4]
def baseStart_6514905 : Nat := 118140960795 + 6514905 * 2 ^ 59
def prefixEnd_6514905 : Nat := 4983230072969 + 3 ^ 40 * 6514905 * 2
def baseEnd_6514905 : Nat := 3345277683379938137926003

theorem tailTrace_6514905 : CollatzResearch.WordTrace tailWord_6514905 prefixEnd_6514905 3345277683379938137926003 := by
  unfold tailWord_6514905
  simp only [CollatzResearch.WordTrace]
  refine ⟨237618106462619317035946169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158412070975079544690630779 237618106462619317035946169)
  ·
    refine ⟨178213579846964487776959627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237618106462619317035946169 178213579846964487776959627)
    ·
      refine ⟨267320369770446731665439441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178213579846964487776959627 267320369770446731665439441)
      ·
        refine ⟨200490277327835048749079581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267320369770446731665439441 200490277327835048749079581)
        ·
          refine ⟨75183853997938143280904843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200490277327835048749079581 75183853997938143280904843)
          ·
            refine ⟨112775780996907214921357265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75183853997938143280904843 112775780996907214921357265)
            ·
              refine ⟨84581835747680411191017949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112775780996907214921357265 84581835747680411191017949)
              ·
                refine ⟨31718188405380154196631731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84581835747680411191017949 31718188405380154196631731)
                ·
                  refine ⟨47577282608070231294947597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31718188405380154196631731 47577282608070231294947597)
                  ·
                    refine ⟨17841480978026336735605349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47577282608070231294947597 17841480978026336735605349)
                    ·
                      refine ⟨3345277683379938137926003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17841480978026336735605349 3345277683379938137926003)
                      ·
                        rfl

theorem cell23_6514905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 1, 3, 4].length) (baseStart_6514905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514905 prefixEnd_6514905 := by exact prefixLift 6514905
  have htrace : WordTrace (prefixWord ++ tailWord_6514905) baseStart_6514905 baseEnd_6514905 := by
    simpa [prefixWord, tailWord_6514905, baseEnd_6514905] using wordTrace_append hprefix tailTrace_6514905
  have hstable : (prefixWord ++ tailWord_6514905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514905).length < 2 ^ (prefixWord ++ tailWord_6514905).sum := by decide
  have hdescent : baseEnd_6514905 < baseStart_6514905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514922 : List Nat := [3, 1, 3, 1, 1, 2, 1, 4, 2, 1, 4]
def baseStart_6514922 : Nat := 118140960795 + 6514922 * 2 ^ 59
def prefixEnd_6514922 : Nat := 4983230072969 + 3 ^ 40 * 6514922 * 2
def baseEnd_6514922 : Nat := 3345286412551064571413425

theorem tailTrace_6514922 : CollatzResearch.WordTrace tailWord_6514922 prefixEnd_6514922 3345286412551064571413425 := by
  unfold tailWord_6514922
  simp only [CollatzResearch.WordTrace]
  refine ⟨59404681625889432234828755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158412484335705152626210013 59404681625889432234828755)
  ·
    refine ⟨89107022438834148352243133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59404681625889432234828755 89107022438834148352243133)
    ·
      refine ⟨33415133414562805632091175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89107022438834148352243133 33415133414562805632091175)
      ·
        refine ⟨50122700121844208448136763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33415133414562805632091175 50122700121844208448136763)
        ·
          refine ⟨75184050182766312672205145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50122700121844208448136763 75184050182766312672205145)
          ·
            refine ⟨56388037637074734504153859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75184050182766312672205145 56388037637074734504153859)
            ·
              refine ⟨84582056455612101756230789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56388037637074734504153859 84582056455612101756230789)
              ·
                refine ⟨15859135585427269079293273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84582056455612101756230789 15859135585427269079293273)
                ·
                  refine ⟨11894351689070451809469955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15859135585427269079293273 11894351689070451809469955)
                  ·
                    refine ⟨17841527533605677714204933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11894351689070451809469955 17841527533605677714204933)
                    ·
                      refine ⟨3345286412551064571413425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17841527533605677714204933 3345286412551064571413425)
                      ·
                        rfl

theorem cell23_6514922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 2, 1, 4].length) (baseStart_6514922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514922 prefixEnd_6514922 := by exact prefixLift 6514922
  have htrace : WordTrace (prefixWord ++ tailWord_6514922) baseStart_6514922 baseEnd_6514922 := by
    simpa [prefixWord, tailWord_6514922, baseEnd_6514922] using wordTrace_append hprefix tailTrace_6514922
  have hstable : (prefixWord ++ tailWord_6514922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514922).length < 2 ^ (prefixWord ++ tailWord_6514922).sum := by decide
  have hdescent : baseEnd_6514922 < baseStart_6514922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6514996 : List Nat := [2, 5, 1, 1, 1, 3, 3, 1, 6]
def baseStart_6514996 : Nat := 118140960795 + 6514996 * 2 ^ 59
def prefixEnd_6514996 : Nat := 4983230072969 + 3 ^ 40 * 6514996 * 2
def baseEnd_6514996 : Nat := 371702712235499697987565

theorem tailTrace_6514996 : CollatzResearch.WordTrace tailWord_6514996 prefixEnd_6514996 371702712235499697987565 := by
  unfold tailWord_6514996
  simp only [CollatzResearch.WordTrace]
  refine ⟨118810712752644819788754421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158414283670193093051672561 118810712752644819788754421)
  ·
    refine ⟨11138504320560451855195727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 118810712752644819788754421 11138504320560451855195727)
    ·
      refine ⟨16707756480840677782793591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11138504320560451855195727 16707756480840677782793591)
      ·
        refine ⟨25061634721261016674190387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16707756480840677782793591 25061634721261016674190387)
        ·
          refine ⟨37592452081891525011285581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25061634721261016674190387 37592452081891525011285581)
          ·
            refine ⟨14097169530709321879232093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37592452081891525011285581 14097169530709321879232093)
            ·
              refine ⟨5286438574015995704712035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14097169530709321879232093 5286438574015995704712035)
              ·
                refine ⟨7929657861023993557068053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5286438574015995704712035 7929657861023993557068053)
                ·
                  refine ⟨371702712235499697987565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7929657861023993557068053 371702712235499697987565)
                  ·
                    rfl

theorem cell23_6514996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_6514996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6514996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6514996 prefixEnd_6514996 := by exact prefixLift 6514996
  have htrace : WordTrace (prefixWord ++ tailWord_6514996) baseStart_6514996 baseEnd_6514996 := by
    simpa [prefixWord, tailWord_6514996, baseEnd_6514996] using wordTrace_append hprefix tailTrace_6514996
  have hstable : (prefixWord ++ tailWord_6514996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6514996).length < 2 ^ (prefixWord ++ tailWord_6514996).sum := by decide
  have hdescent : baseEnd_6514996 < baseStart_6514996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6514996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515006 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_6515006 : Nat := 118140960795 + 6515006 * 2 ^ 59
def prefixEnd_6515006 : Nat := 4983230072969 + 3 ^ 40 * 6515006 * 2
def baseEnd_6515006 : Nat := 3345329544926042242763039

theorem tailTrace_6515006 : CollatzResearch.WordTrace tailWord_6515006 prefixEnd_6515006 3345329544926042242763039 := by
  unfold tailWord_6515006
  simp only [CollatzResearch.WordTrace]
  refine ⟨29702723779406676410671609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158414526823502274190248581 29702723779406676410671609)
  ·
    refine ⟨22277042834555007308003707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29702723779406676410671609 22277042834555007308003707)
    ·
      refine ⟨33415564251832510962005561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22277042834555007308003707 33415564251832510962005561)
      ·
        refine ⟨25061673188874383221504171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33415564251832510962005561 25061673188874383221504171)
        ·
          refine ⟨37592509783311574832256257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25061673188874383221504171 37592509783311574832256257)
          ·
            refine ⟨28194382337483681124192193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37592509783311574832256257 28194382337483681124192193)
            ·
              refine ⟨21145786753112760843144145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28194382337483681124192193 21145786753112760843144145)
              ·
                refine ⟨15859340064834570632358109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21145786753112760843144145 15859340064834570632358109)
                ·
                  refine ⟨5947252524312963987134291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15859340064834570632358109 5947252524312963987134291)
                  ·
                    refine ⟨8920878786469445980701437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5947252524312963987134291 8920878786469445980701437)
                    ·
                      refine ⟨3345329544926042242763039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8920878786469445980701437 3345329544926042242763039)
                      ·
                        rfl

theorem cell23_6515006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_6515006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515006 prefixEnd_6515006 := by exact prefixLift 6515006
  have htrace : WordTrace (prefixWord ++ tailWord_6515006) baseStart_6515006 baseEnd_6515006 := by
    simpa [prefixWord, tailWord_6515006, baseEnd_6515006] using wordTrace_append hprefix tailTrace_6515006
  have hstable : (prefixWord ++ tailWord_6515006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515006).length < 2 ^ (prefixWord ++ tailWord_6515006).sum := by decide
  have hdescent : baseEnd_6515006 < baseStart_6515006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515040 : List Nat := [2, 1, 1, 3, 5, 1, 3, 2, 1, 1, 3]
def baseStart_6515040 : Nat := 118140960795 + 6515040 * 2 ^ 59
def prefixEnd_6515040 : Nat := 4983230072969 + 3 ^ 40 * 6515040 * 2
def baseEnd_6515040 : Nat := 3345347003268295109737883

theorem tailTrace_6515040 : CollatzResearch.WordTrace tailWord_6515040 prefixEnd_6515040 3345347003268295109737883 := by
  unfold tailWord_6515040
  simp only [CollatzResearch.WordTrace]
  refine ⟨118811515158565117546055287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158415353544753490061407049 118811515158565117546055287)
  ·
    refine ⟨178217272737847676319082931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118811515158565117546055287 178217272737847676319082931)
    ·
      refine ⟨267325909106771514478624397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178217272737847676319082931 267325909106771514478624397)
      ·
        refine ⟨100247215915039317929484149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267325909106771514478624397 100247215915039317929484149)
        ·
          refine ⟨9398176492034936055889139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100247215915039317929484149 9398176492034936055889139)
          ·
            refine ⟨14097264738052404083833709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9398176492034936055889139 14097264738052404083833709)
            ·
              refine ⟨5286474276769651531437641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14097264738052404083833709 5286474276769651531437641)
              ·
                refine ⟨3964855707577238648578231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5286474276769651531437641 3964855707577238648578231)
                ·
                  refine ⟨5947283561365857972867347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3964855707577238648578231 5947283561365857972867347)
                  ·
                    refine ⟨8920925342048786959301021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5947283561365857972867347 8920925342048786959301021)
                    ·
                      refine ⟨3345347003268295109737883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8920925342048786959301021 3345347003268295109737883)
                      ·
                        rfl

theorem cell23_6515040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_6515040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515040 prefixEnd_6515040 := by exact prefixLift 6515040
  have htrace : WordTrace (prefixWord ++ tailWord_6515040) baseStart_6515040 baseEnd_6515040 := by
    simpa [prefixWord, tailWord_6515040, baseEnd_6515040] using wordTrace_append hprefix tailTrace_6515040
  have hstable : (prefixWord ++ tailWord_6515040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515040).length < 2 ^ (prefixWord ++ tailWord_6515040).sum := by decide
  have hdescent : baseEnd_6515040 < baseStart_6515040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515056 : List Nat := [2, 1, 1, 1, 4, 3, 4, 1, 2, 4]
def baseStart_6515056 : Nat := 118140960795 + 6515056 * 2 ^ 59
def prefixEnd_6515056 : Nat := 4983230072969 + 3 ^ 40 * 6515056 * 2
def baseEnd_6515056 : Nat := 1115118406319589015712603

theorem tailTrace_6515056 : CollatzResearch.WordTrace tailWord_6515056 prefixEnd_6515056 1115118406319589015712603 := by
  unfold tailWord_6515056
  simp only [CollatzResearch.WordTrace]
  refine ⟨118811806942536134912346511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158415742590048179883128681 118811806942536134912346511)
  ·
    refine ⟨178217710413804202368519767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118811806942536134912346511 178217710413804202368519767)
    ·
      refine ⟨267326565620706303552779651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178217710413804202368519767 267326565620706303552779651)
      ·
        refine ⟨400989848431059455329169477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267326565620706303552779651 400989848431059455329169477)
        ·
          refine ⟨75185596580823647874219277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 400989848431059455329169477 75185596580823647874219277)
          ·
            refine ⟨28194598717808867952832229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75185596580823647874219277 28194598717808867952832229)
            ·
              refine ⟨5286487259589162741156043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28194598717808867952832229 5286487259589162741156043)
              ·
                refine ⟨7929730889383744111734065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5286487259589162741156043 7929730889383744111734065)
                ·
                  refine ⟨5947298167037808083800549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7929730889383744111734065 5947298167037808083800549)
                  ·
                    refine ⟨1115118406319589015712603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5947298167037808083800549 1115118406319589015712603)
                    ·
                      rfl

theorem cell23_6515056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 4, 1, 2, 4].length) (baseStart_6515056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515056 prefixEnd_6515056 := by exact prefixLift 6515056
  have htrace : WordTrace (prefixWord ++ tailWord_6515056) baseStart_6515056 baseEnd_6515056 := by
    simpa [prefixWord, tailWord_6515056, baseEnd_6515056] using wordTrace_append hprefix tailTrace_6515056
  have hstable : (prefixWord ++ tailWord_6515056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515056).length < 2 ^ (prefixWord ++ tailWord_6515056).sum := by decide
  have hdescent : baseEnd_6515056 < baseStart_6515056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515079 : List Nat := [1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_6515079 : Nat := 118140960795 + 6515079 * 2 ^ 59
def prefixEnd_6515079 : Nat := 4983230072969 + 3 ^ 40 * 6515079 * 2
def baseEnd_6515079 : Nat := 3345367029013820457150203

theorem tailTrace_6515079 : CollatzResearch.WordTrace tailWord_6515079 prefixEnd_6515079 3345367029013820457150203 := by
  unfold tailWord_6515079
  simp only [CollatzResearch.WordTrace]
  refine ⟨237624452763988944752780291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158416301842659296501853527 237624452763988944752780291)
  ·
    refine ⟨356436679145983417129170437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237624452763988944752780291 356436679145983417129170437)
    ·
      refine ⟨66831877339871890711719457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 356436679145983417129170437 66831877339871890711719457)
      ·
        refine ⟨50123908004903918033789593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66831877339871890711719457 50123908004903918033789593)
        ·
          refine ⟨37592931003677938525342195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50123908004903918033789593 37592931003677938525342195)
          ·
            refine ⟨56389396505516907788013293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37592931003677938525342195 56389396505516907788013293)
            ·
              refine ⟨21146023689568840420504985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56389396505516907788013293 21146023689568840420504985)
              ·
                refine ⟨15859517767176630315378739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21146023689568840420504985 15859517767176630315378739)
                ·
                  refine ⟨23789276650764945473068109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15859517767176630315378739 23789276650764945473068109)
                  ·
                    refine ⟨8920978744036854552400541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23789276650764945473068109 8920978744036854552400541)
                    ·
                      refine ⟨3345367029013820457150203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8920978744036854552400541 3345367029013820457150203)
                      ·
                        rfl

theorem cell23_6515079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_6515079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515079 prefixEnd_6515079 := by exact prefixLift 6515079
  have htrace : WordTrace (prefixWord ++ tailWord_6515079) baseStart_6515079 baseEnd_6515079 := by
    simpa [prefixWord, tailWord_6515079, baseEnd_6515079] using wordTrace_append hprefix tailTrace_6515079
  have hstable : (prefixWord ++ tailWord_6515079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515079).length < 2 ^ (prefixWord ++ tailWord_6515079).sum := by decide
  have hdescent : baseEnd_6515079 < baseStart_6515079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515089 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 7, 3, 2]
def baseStart_6515089 : Nat := 118140960795 + 6515089 * 2 ^ 59
def prefixEnd_6515089 : Nat := 4983230072969 + 3 ^ 40 * 6515089 * 2
def baseEnd_6515089 : Nat := 3345372163820365418025157

theorem tailTrace_6515089 : CollatzResearch.WordTrace tailWord_6515089 prefixEnd_6515089 3345372163820365418025157 := by
  unfold tailWord_6515089
  simp only [CollatzResearch.WordTrace]
  refine ⟨237624817493952716460644321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158416544995968477640429547 237624817493952716460644321)
  ·
    refine ⟨178218613120464537345483241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237624817493952716460644321 178218613120464537345483241)
    ·
      refine ⟨133663959840348403009112431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178218613120464537345483241 133663959840348403009112431)
      ·
        refine ⟨200495939760522604513668647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133663959840348403009112431 200495939760522604513668647)
        ·
          refine ⟨300743909640783906770502971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200495939760522604513668647 300743909640783906770502971)
          ·
            refine ⟨451115864461175860155754457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300743909640783906770502971 451115864461175860155754457)
            ·
              refine ⟨338336898345881895116815843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451115864461175860155754457 338336898345881895116815843)
              ·
                refine ⟨507505347518822842675223765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338336898345881895116815843 507505347518822842675223765)
                ·
                  refine ⟨11894656582472410375200557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 507505347518822842675223765 11894656582472410375200557)
                  ·
                    refine ⟨4460496218427153890700209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11894656582472410375200557 4460496218427153890700209)
                    ·
                      refine ⟨3345372163820365418025157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4460496218427153890700209 3345372163820365418025157)
                      ·
                        rfl

theorem cell23_6515089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 3, 2].length) (baseStart_6515089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515089 prefixEnd_6515089 := by exact prefixLift 6515089
  have htrace : WordTrace (prefixWord ++ tailWord_6515089) baseStart_6515089 baseEnd_6515089 := by
    simpa [prefixWord, tailWord_6515089, baseEnd_6515089] using wordTrace_append hprefix tailTrace_6515089
  have hstable : (prefixWord ++ tailWord_6515089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515089).length < 2 ^ (prefixWord ++ tailWord_6515089).sum := by decide
  have hdescent : baseEnd_6515089 < baseStart_6515089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515106 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 5, 3, 2]
def baseStart_6515106 : Nat := 118140960795 + 6515106 * 2 ^ 59
def prefixEnd_6515106 : Nat := 4983230072969 + 3 ^ 40 * 6515106 * 2
def baseEnd_6515106 : Nat := 3345380892991491851512579

theorem tailTrace_6515106 : CollatzResearch.WordTrace tailWord_6515106 prefixEnd_6515106 3345380892991491851512579 := by
  unfold tailWord_6515106
  simp only [CollatzResearch.WordTrace]
  refine ⟨59406359383722782091003293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158416958356594085576008781 59406359383722782091003293)
  ·
    refine ⟨22277384768896043284126235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59406359383722782091003293 22277384768896043284126235)
    ·
      refine ⟨33416077153344064926189353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22277384768896043284126235 33416077153344064926189353)
      ·
        refine ⟨25062057865008048694642015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33416077153344064926189353 25062057865008048694642015)
        ·
          refine ⟨37593086797512073041963023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25062057865008048694642015 37593086797512073041963023)
          ·
            refine ⟨56389630196268109562944535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37593086797512073041963023 56389630196268109562944535)
            ·
              refine ⟨84584445294402164344416803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56389630196268109562944535 84584445294402164344416803)
              ·
                refine ⟨126876667941603246516625205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84584445294402164344416803 126876667941603246516625205)
                ·
                  refine ⟨11894687619525304360933613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 126876667941603246516625205 11894687619525304360933613)
                  ·
                    refine ⟨4460507857321989135350105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11894687619525304360933613 4460507857321989135350105)
                    ·
                      refine ⟨3345380892991491851512579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4460507857321989135350105 3345380892991491851512579)
                      ·
                        rfl

theorem cell23_6515106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_6515106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515106 prefixEnd_6515106 := by exact prefixLift 6515106
  have htrace : WordTrace (prefixWord ++ tailWord_6515106) baseStart_6515106 baseEnd_6515106 := by
    simpa [prefixWord, tailWord_6515106, baseEnd_6515106] using wordTrace_append hprefix tailTrace_6515106
  have hstable : (prefixWord ++ tailWord_6515106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515106).length < 2 ^ (prefixWord ++ tailWord_6515106).sum := by decide
  have hdescent : baseEnd_6515106 < baseStart_6515106 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515136 : List Nat := [2, 1, 1, 2, 3, 1, 1, 4, 4, 2, 2]
def baseStart_6515136 : Nat := 118140960795 + 6515136 * 2 ^ 59
def prefixEnd_6515136 : Nat := 4983230072969 + 3 ^ 40 * 6515136 * 2
def baseEnd_6515136 : Nat := 3345396297411126734137441

theorem tailTrace_6515136 : CollatzResearch.WordTrace tailWord_6515136 prefixEnd_6515136 3345396297411126734137441 := by
  unfold tailWord_6515136
  simp only [CollatzResearch.WordTrace]
  refine ⟨118813265862391221743802631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158417687816521628991736841 118813265862391221743802631)
  ·
    refine ⟨178219898793586832615703947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118813265862391221743802631 178219898793586832615703947)
    ·
      refine ⟨267329848190380248923555921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178219898793586832615703947 267329848190380248923555921)
      ·
        refine ⟨200497386142785186692666941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267329848190380248923555921 200497386142785186692666941)
        ·
          refine ⟨75186519803544445009750103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200497386142785186692666941 75186519803544445009750103)
          ·
            refine ⟨112779779705316667514625155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75186519803544445009750103 112779779705316667514625155)
            ·
              refine ⟨169169669557975001271937733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112779779705316667514625155 169169669557975001271937733)
              ·
                refine ⟨31719313042120312738488325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169169669557975001271937733 31719313042120312738488325)
                ·
                  refine ⟨5947371195397558638466561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31719313042120312738488325 5947371195397558638466561)
                  ·
                    refine ⟨4460528396548168978849921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5947371195397558638466561 4460528396548168978849921)
                    ·
                      refine ⟨3345396297411126734137441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4460528396548168978849921 3345396297411126734137441)
                      ·
                        rfl

theorem cell23_6515136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 4, 4, 2, 2].length) (baseStart_6515136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515136 prefixEnd_6515136 := by exact prefixLift 6515136
  have htrace : WordTrace (prefixWord ++ tailWord_6515136) baseStart_6515136 baseEnd_6515136 := by
    simpa [prefixWord, tailWord_6515136, baseEnd_6515136] using wordTrace_append hprefix tailTrace_6515136
  have hstable : (prefixWord ++ tailWord_6515136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515136).length < 2 ^ (prefixWord ++ tailWord_6515136).sum := by decide
  have hdescent : baseEnd_6515136 < baseStart_6515136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515140 : List Nat := [2, 3, 3, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_6515140 : Nat := 118140960795 + 6515140 * 2 ^ 59
def prefixEnd_6515140 : Nat := 4983230072969 + 3 ^ 40 * 6515140 * 2
def baseEnd_6515140 : Nat := 3345398351333744718487423

theorem tailTrace_6515140 : CollatzResearch.WordTrace tailWord_6515140 prefixEnd_6515140 3345398351333744718487423 := by
  unfold tailWord_6515140
  simp only [CollatzResearch.WordTrace]
  refine ⟨118813338808383976085375437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158417785077845301447167249 118813338808383976085375437)
  ·
    refine ⟨44555002053143991032015789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118813338808383976085375437 44555002053143991032015789)
    ·
      refine ⟨16708125769928996637005921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44555002053143991032015789 16708125769928996637005921)
      ·
        refine ⟨12531094327446747477754441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16708125769928996637005921 12531094327446747477754441)
        ·
          refine ⟨9398320745585060608315831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12531094327446747477754441 9398320745585060608315831)
          ·
            refine ⟨14097481118377590912473747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9398320745585060608315831 14097481118377590912473747)
            ·
              refine ⟨21146221677566386368710621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14097481118377590912473747 21146221677566386368710621)
              ·
                refine ⟨7929833129087394888266483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21146221677566386368710621 7929833129087394888266483)
                ·
                  refine ⟨11894749693631092332399725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7929833129087394888266483 11894749693631092332399725)
                  ·
                    refine ⟨4460531135111659624649897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11894749693631092332399725 4460531135111659624649897)
                    ·
                      refine ⟨3345398351333744718487423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4460531135111659624649897 3345398351333744718487423)
                      ·
                        rfl

theorem cell23_6515140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_6515140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515140 prefixEnd_6515140 := by exact prefixLift 6515140
  have htrace : WordTrace (prefixWord ++ tailWord_6515140) baseStart_6515140 baseEnd_6515140 := by
    simpa [prefixWord, tailWord_6515140, baseEnd_6515140] using wordTrace_append hprefix tailTrace_6515140
  have hstable : (prefixWord ++ tailWord_6515140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515140).length < 2 ^ (prefixWord ++ tailWord_6515140).sum := by decide
  have hdescent : baseEnd_6515140 < baseStart_6515140 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515169 : List Nat := [1, 2, 3, 1, 2, 2, 1, 3, 2, 3, 3]
def baseStart_6515169 : Nat := 118140960795 + 6515169 * 2 ^ 59
def prefixEnd_6515169 : Nat := 4983230072969 + 3 ^ 40 * 6515169 * 2
def baseEnd_6515169 : Nat := 3345413242272725105024789

theorem tailTrace_6515169 : CollatzResearch.WordTrace tailWord_6515169 prefixEnd_6515169 3345413242272725105024789 := by
  unfold tailWord_6515169
  simp only [CollatzResearch.WordTrace]
  refine ⟨237627735333662890123556561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158418490222441926749037707 237627735333662890123556561)
  ·
    refine ⟨178220801500247167592667421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237627735333662890123556561 178220801500247167592667421)
    ·
      refine ⟨66832800562592687847250283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178220801500247167592667421 66832800562592687847250283)
      ·
        refine ⟨100249200843889031770875425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66832800562592687847250283 100249200843889031770875425)
        ·
          refine ⟨75186900632916773828156569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100249200843889031770875425 75186900632916773828156569)
          ·
            refine ⟨56390175474687580371117427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75186900632916773828156569 56390175474687580371117427)
            ·
              refine ⟨84585263212031370556676141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56390175474687580371117427 84585263212031370556676141)
              ·
                refine ⟨31719473704511763958753553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84585263212031370556676141 31719473704511763958753553)
                ·
                  refine ⟨23789605278383822969065165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31719473704511763958753553 23789605278383822969065165)
                  ·
                    refine ⟨8921101979393933613399437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23789605278383822969065165 8921101979393933613399437)
                    ·
                      refine ⟨3345413242272725105024789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8921101979393933613399437 3345413242272725105024789)
                      ·
                        rfl

theorem cell23_6515169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 3, 3].length) (baseStart_6515169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515169 prefixEnd_6515169 := by exact prefixLift 6515169
  have htrace : WordTrace (prefixWord ++ tailWord_6515169) baseStart_6515169 baseEnd_6515169 := by
    simpa [prefixWord, tailWord_6515169, baseEnd_6515169] using wordTrace_append hprefix tailTrace_6515169
  have hstable : (prefixWord ++ tailWord_6515169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515169).length < 2 ^ (prefixWord ++ tailWord_6515169).sum := by decide
  have hdescent : baseEnd_6515169 < baseStart_6515169 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515226 : List Nat := [3, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2]
def baseStart_6515226 : Nat := 118140960795 + 6515226 * 2 ^ 59
def prefixEnd_6515226 : Nat := 4983230072969 + 3 ^ 40 * 6515226 * 2
def baseEnd_6515226 : Nat := 3345442510670031382012027

theorem tailTrace_6515226 : CollatzResearch.WordTrace tailWord_6515226 prefixEnd_6515226 3345442510670031382012027 := by
  unfold tailWord_6515226
  simp only [CollatzResearch.WordTrace]
  refine ⟨59407453573614097214595383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158419876196304259238921021 59407453573614097214595383)
  ·
    refine ⟨89111180360421145821893075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59407453573614097214595383 89111180360421145821893075)
    ·
      refine ⟨133666770540631718732839613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89111180360421145821893075 133666770540631718732839613)
      ·
        refine ⟨50125038952736894524814855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133666770540631718732839613 50125038952736894524814855)
        ·
          refine ⟨75187558429105341787222283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50125038952736894524814855 75187558429105341787222283)
          ·
            refine ⟨112781337643658012680833425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75187558429105341787222283 112781337643658012680833425)
            ·
              refine ⟨84586003232743509510625069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112781337643658012680833425 84586003232743509510625069)
              ·
                refine ⟨31719751212278816066484401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84586003232743509510625069 31719751212278816066484401)
                ·
                  refine ⟨23789813409209112049863301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31719751212278816066484401 23789813409209112049863301)
                  ·
                    refine ⟨4460590014226708509349369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23789813409209112049863301 4460590014226708509349369)
                    ·
                      refine ⟨3345442510670031382012027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4460590014226708509349369 3345442510670031382012027)
                      ·
                        rfl

theorem cell23_6515226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3, 2, 4, 2].length) (baseStart_6515226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515226 prefixEnd_6515226 := by exact prefixLift 6515226
  have htrace : WordTrace (prefixWord ++ tailWord_6515226) baseStart_6515226 baseEnd_6515226 := by
    simpa [prefixWord, tailWord_6515226, baseEnd_6515226] using wordTrace_append hprefix tailTrace_6515226
  have hstable : (prefixWord ++ tailWord_6515226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515226).length < 2 ^ (prefixWord ++ tailWord_6515226).sum := by decide
  have hdescent : baseEnd_6515226 < baseStart_6515226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515253 : List Nat := [1, 3, 3, 1, 1, 2, 2, 5, 1, 4]
def baseStart_6515253 : Nat := 118140960795 + 6515253 * 2 ^ 59
def prefixEnd_6515253 : Nat := 4983230072969 + 3 ^ 40 * 6515253 * 2
def baseEnd_6515253 : Nat := 1115152124882567592124801

theorem tailTrace_6515253 : CollatzResearch.WordTrace tailWord_6515253 prefixEnd_6515253 1115152124882567592124801 := by
  unfold tailWord_6515253
  simp only [CollatzResearch.WordTrace]
  refine ⟨237630799065358572469614413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158420532710239048313076275 237630799065358572469614413)
  ·
    refine ⟨89111549649509464676105405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237630799065358572469614413 89111549649509464676105405)
    ·
      refine ⟨33416831118566049253539527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89111549649509464676105405 33416831118566049253539527)
      ·
        refine ⟨50125246677849073880309291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33416831118566049253539527 50125246677849073880309291)
        ·
          refine ⟨75187870016773610820463937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50125246677849073880309291 75187870016773610820463937)
          ·
            refine ⟨56390902512580208115347953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75187870016773610820463937 56390902512580208115347953)
            ·
              refine ⟨42293176884435156086510965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56390902512580208115347953 42293176884435156086510965)
              ·
                refine ⟨3964985332915795883110403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42293176884435156086510965 3964985332915795883110403)
                ·
                  refine ⟨5947477999373693824665605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3964985332915795883110403 5947477999373693824665605)
                  ·
                    refine ⟨1115152124882567592124801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5947477999373693824665605 1115152124882567592124801)
                    ·
                      rfl

theorem cell23_6515253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_6515253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515253 prefixEnd_6515253 := by exact prefixLift 6515253
  have htrace : WordTrace (prefixWord ++ tailWord_6515253) baseStart_6515253 baseEnd_6515253 := by
    simpa [prefixWord, tailWord_6515253, baseEnd_6515253] using wordTrace_append hprefix tailTrace_6515253
  have hstable : (prefixWord ++ tailWord_6515253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515253).length < 2 ^ (prefixWord ++ tailWord_6515253).sum := by decide
  have hdescent : baseEnd_6515253 < baseStart_6515253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515279 : List Nat := [1, 1, 2, 1, 1, 2, 5, 2, 3, 5]
def baseStart_6515279 : Nat := 118140960795 + 6515279 * 2 ^ 59
def prefixEnd_6515279 : Nat := 4983230072969 + 3 ^ 40 * 6515279 * 2
def baseEnd_6515279 : Nat := 1115156575048239891549761

theorem tailTrace_6515279 : CollatzResearch.WordTrace tailWord_6515279 prefixEnd_6515279 1115156575048239891549761 := by
  unfold tailWord_6515279
  simp only [CollatzResearch.WordTrace]
  refine ⟨237631747363264378910060891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158421164908842919273373927 237631747363264378910060891)
  ·
    refine ⟨356447621044896568365091337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237631747363264378910060891 356447621044896568365091337)
    ·
      refine ⟨267335715783672426273818503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356447621044896568365091337 267335715783672426273818503)
      ·
        refine ⟨401003573675508639410727755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267335715783672426273818503 401003573675508639410727755)
        ·
          refine ⟨601505360513262959116091633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401003573675508639410727755 601505360513262959116091633)
          ·
            refine ⟨451129020384947219337068725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 601505360513262959116091633 451129020384947219337068725)
            ·
              refine ⟨42293345661088801812850193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 451129020384947219337068725 42293345661088801812850193)
              ·
                refine ⟨31720009245816601359637645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42293345661088801812850193 31720009245816601359637645)
                ·
                  refine ⟨11895003467181225509864117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31720009245816601359637645 11895003467181225509864117)
                  ·
                    refine ⟨1115156575048239891549761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11895003467181225509864117 1115156575048239891549761)
                    ·
                      rfl

theorem cell23_6515279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 2, 3, 5].length) (baseStart_6515279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515279 prefixEnd_6515279 := by exact prefixLift 6515279
  have htrace : WordTrace (prefixWord ++ tailWord_6515279) baseStart_6515279 baseEnd_6515279 := by
    simpa [prefixWord, tailWord_6515279, baseEnd_6515279] using wordTrace_append hprefix tailTrace_6515279
  have hstable : (prefixWord ++ tailWord_6515279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515279).length < 2 ^ (prefixWord ++ tailWord_6515279).sum := by decide
  have hdescent : baseEnd_6515279 < baseStart_6515279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515294 : List Nat := [4, 4, 1, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_6515294 : Nat := 118140960795 + 6515294 * 2 ^ 59
def prefixEnd_6515294 : Nat := 4983230072969 + 3 ^ 40 * 6515294 * 2
def baseEnd_6515294 : Nat := 3345477427354537115961715

theorem tailTrace_6515294 : CollatzResearch.WordTrace tailWord_6515294 prefixEnd_6515294 3345477427354537115961715 := by
  unfold tailWord_6515294
  simp only [CollatzResearch.WordTrace]
  refine ⟨29704036807276254558982117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158421529638806690981237957 29704036807276254558982117)
  ·
    refine ⟨5569506901364297729809147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29704036807276254558982117 5569506901364297729809147)
    ·
      refine ⟨8354260352046446594713721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5569506901364297729809147 8354260352046446594713721)
      ·
        refine ⟨6265695264034834946035291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8354260352046446594713721 6265695264034834946035291)
        ·
          refine ⟨9398542896052252419052937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6265695264034834946035291 9398542896052252419052937)
          ·
            refine ⟨7048907172039189314289703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9398542896052252419052937 7048907172039189314289703)
            ·
              refine ⟨10573360758058783971434555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7048907172039189314289703 10573360758058783971434555)
              ·
                refine ⟨15860041137088175957151833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10573360758058783971434555 15860041137088175957151833)
                ·
                  refine ⟨11895030852816131967863875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15860041137088175957151833 11895030852816131967863875)
                  ·
                    refine ⟨17842546279224197951795813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11895030852816131967863875 17842546279224197951795813)
                    ·
                      refine ⟨3345477427354537115961715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17842546279224197951795813 3345477427354537115961715)
                      ·
                        rfl

theorem cell23_6515294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_6515294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515294 prefixEnd_6515294 := by exact prefixLift 6515294
  have htrace : WordTrace (prefixWord ++ tailWord_6515294) baseStart_6515294 baseEnd_6515294 := by
    simpa [prefixWord, tailWord_6515294, baseEnd_6515294] using wordTrace_append hprefix tailTrace_6515294
  have hstable : (prefixWord ++ tailWord_6515294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515294).length < 2 ^ (prefixWord ++ tailWord_6515294).sum := by decide
  have hdescent : baseEnd_6515294 < baseStart_6515294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515353 : List Nat := [1, 2, 1, 2, 1, 2, 6, 2, 1, 2, 3]
def baseStart_6515353 : Nat := 118140960795 + 6515353 * 2 ^ 59
def prefixEnd_6515353 : Nat := 4983230072969 + 3 ^ 40 * 6515353 * 2
def baseEnd_6515353 : Nat := 3345507722713152385123943

theorem tailTrace_6515353 : CollatzResearch.WordTrace tailWord_6515353 prefixEnd_6515353 3345507722713152385123943 := by
  unfold tailWord_6515353
  simp only [CollatzResearch.WordTrace]
  refine ⟨237634446364996289548254713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158422964243330859698836475 237634446364996289548254713)
  ·
    refine ⟨178225834773747217161191035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237634446364996289548254713 178225834773747217161191035)
    ·
      refine ⟨267338752160620825741786553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178225834773747217161191035 267338752160620825741786553)
      ·
        refine ⟨200504064120465619306339915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267338752160620825741786553 200504064120465619306339915)
        ·
          refine ⟨300756096180698428959509873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200504064120465619306339915 300756096180698428959509873)
          ·
            refine ⟨225567072135523821719632405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300756096180698428959509873 225567072135523821719632405)
            ·
              refine ⟨10573456506352679143107769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 225567072135523821719632405 10573456506352679143107769)
              ·
                refine ⟨7930092379764509357330827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10573456506352679143107769 7930092379764509357330827)
                ·
                  refine ⟨11895138569646764035996241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7930092379764509357330827 11895138569646764035996241)
                  ·
                    refine ⟨8921353927235073026997181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11895138569646764035996241 8921353927235073026997181)
                    ·
                      refine ⟨3345507722713152385123943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8921353927235073026997181 3345507722713152385123943)
                      ·
                        rfl

theorem cell23_6515353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 2, 1, 2, 3].length) (baseStart_6515353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515353 prefixEnd_6515353 := by exact prefixLift 6515353
  have htrace : WordTrace (prefixWord ++ tailWord_6515353) baseStart_6515353 baseEnd_6515353 := by
    simpa [prefixWord, tailWord_6515353, baseEnd_6515353] using wordTrace_append hprefix tailTrace_6515353
  have hstable : (prefixWord ++ tailWord_6515353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515353).length < 2 ^ (prefixWord ++ tailWord_6515353).sum := by decide
  have hdescent : baseEnd_6515353 < baseStart_6515353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515356 : List Nat := [2, 2, 3, 2, 2, 2, 1, 9]
def baseStart_6515356 : Nat := 118140960795 + 6515356 * 2 ^ 59
def prefixEnd_6515356 : Nat := 4983230072969 + 3 ^ 40 * 6515356 * 2
def baseEnd_6515356 : Nat := 123907750487226513829127

theorem tailTrace_6515356 : CollatzResearch.WordTrace tailWord_6515356 prefixEnd_6515356 123907750487226513829127 := by
  unfold tailWord_6515356
  simp only [CollatzResearch.WordTrace]
  refine ⟨118817277891992710530306961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158423037189323614040409281 118817277891992710530306961)
  ·
    refine ⟨89112958418994532897730221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118817277891992710530306961 89112958418994532897730221)
    ·
      refine ⟨33417359407122949836648833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89112958418994532897730221 33417359407122949836648833)
      ·
        refine ⟨25063019555342212377486625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33417359407122949836648833 25063019555342212377486625)
        ·
          refine ⟨18797264666506659283114969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25063019555342212377486625 18797264666506659283114969)
          ·
            refine ⟨14097948499879994462336227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18797264666506659283114969 14097948499879994462336227)
            ·
              refine ⟨21146922749819991693504341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14097948499879994462336227 21146922749819991693504341)
              ·
                refine ⟨123907750487226513829127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21146922749819991693504341 123907750487226513829127)
                ·
                  rfl

theorem cell23_6515356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 9].length) (baseStart_6515356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515356 prefixEnd_6515356 := by exact prefixLift 6515356
  have htrace : WordTrace (prefixWord ++ tailWord_6515356) baseStart_6515356 baseEnd_6515356 := by
    simpa [prefixWord, tailWord_6515356, baseEnd_6515356] using wordTrace_append hprefix tailTrace_6515356
  have hstable : (prefixWord ++ tailWord_6515356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515356).length < 2 ^ (prefixWord ++ tailWord_6515356).sum := by decide
  have hdescent : baseEnd_6515356 < baseStart_6515356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515400 : List Nat := [2, 1, 3, 1, 2, 4, 1, 3, 2, 1, 3]
def baseStart_6515400 : Nat := 118140960795 + 6515400 * 2 ^ 59
def prefixEnd_6515400 : Nat := 4983230072969 + 3 ^ 40 * 6515400 * 2
def baseEnd_6515400 : Nat := 3345531856303913701236227

theorem tailTrace_6515400 : CollatzResearch.WordTrace tailWord_6515400 prefixEnd_6515400 3345531856303913701236227 := by
  unfold tailWord_6515400
  simp only [CollatzResearch.WordTrace]
  refine ⟨118818080297913008287607827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158424107063884011050143769 118818080297913008287607827)
  ·
    refine ⟨178227120446869512431411741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118818080297913008287607827 178227120446869512431411741)
    ·
      refine ⟨66835170167576067161779403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178227120446869512431411741 66835170167576067161779403)
      ·
        refine ⟨100252755251364100742669105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66835170167576067161779403 100252755251364100742669105)
        ·
          refine ⟨75189566438523075557001829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100252755251364100742669105 75189566438523075557001829)
          ·
            refine ⟨14098043707223076666937843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75189566438523075557001829 14098043707223076666937843)
            ·
              refine ⟨21147065560834615000406765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14098043707223076666937843 21147065560834615000406765)
              ·
                refine ⟨7930149585312980625152537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21147065560834615000406765 7930149585312980625152537)
                ·
                  refine ⟨5947612188984735468864403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7930149585312980625152537 5947612188984735468864403)
                  ·
                    refine ⟨8921418283477103203296605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5947612188984735468864403 8921418283477103203296605)
                    ·
                      refine ⟨3345531856303913701236227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8921418283477103203296605 3345531856303913701236227)
                      ·
                        rfl

theorem cell23_6515400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_6515400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515400 prefixEnd_6515400 := by exact prefixLift 6515400
  have htrace : WordTrace (prefixWord ++ tailWord_6515400) baseStart_6515400 baseEnd_6515400 := by
    simpa [prefixWord, tailWord_6515400, baseEnd_6515400] using wordTrace_append hprefix tailTrace_6515400
  have hstable : (prefixWord ++ tailWord_6515400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515400).length < 2 ^ (prefixWord ++ tailWord_6515400).sum := by decide
  have hdescent : baseEnd_6515400 < baseStart_6515400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515423 : List Nat := [1, 1, 2, 3, 2, 3, 1, 1, 3, 4, 2]
def baseStart_6515423 : Nat := 118140960795 + 6515423 * 2 ^ 59
def prefixEnd_6515423 : Nat := 4983230072969 + 3 ^ 40 * 6515423 * 2
def baseEnd_6515423 : Nat := 3345543666358967111248621

theorem tailTrace_6515423 : CollatzResearch.WordTrace tailWord_6515423 prefixEnd_6515423 3345543666358967111248621 := by
  unfold tailWord_6515423
  simp only [CollatzResearch.WordTrace]
  refine ⟨237636999474742691503302923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158424666316495127668868615 237636999474742691503302923)
  ·
    refine ⟨356455499212114037254954385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237636999474742691503302923 356455499212114037254954385)
    ·
      refine ⟨267341624409085527941215789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356455499212114037254954385 267341624409085527941215789)
      ·
        refine ⟨100253109153407072977955921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267341624409085527941215789 100253109153407072977955921)
        ·
          refine ⟨75189831865055304733466941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100253109153407072977955921 75189831865055304733466941)
          ·
            refine ⟨28196186949395739275050103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75189831865055304733466941 28196186949395739275050103)
            ·
              refine ⟨42294280424093608912575155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28196186949395739275050103 42294280424093608912575155)
              ·
                refine ⟨63441420636140413368862733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42294280424093608912575155 63441420636140413368862733)
                ·
                  refine ⟨23790532738552655013323525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63441420636140413368862733 23790532738552655013323525)
                  ·
                    refine ⟨4460724888478622814998161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23790532738552655013323525 4460724888478622814998161)
                    ·
                      refine ⟨3345543666358967111248621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4460724888478622814998161 3345543666358967111248621)
                      ·
                        rfl

theorem cell23_6515423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 1, 3, 4, 2].length) (baseStart_6515423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515423 prefixEnd_6515423 := by exact prefixLift 6515423
  have htrace : WordTrace (prefixWord ++ tailWord_6515423) baseStart_6515423 baseEnd_6515423 := by
    simpa [prefixWord, tailWord_6515423, baseEnd_6515423] using wordTrace_append hprefix tailTrace_6515423
  have hstable : (prefixWord ++ tailWord_6515423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515423).length < 2 ^ (prefixWord ++ tailWord_6515423).sum := by decide
  have hdescent : baseEnd_6515423 < baseStart_6515423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515436 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 4]
def baseStart_6515436 : Nat := 118140960795 + 6515436 * 2 ^ 59
def prefixEnd_6515436 : Nat := 4983230072969 + 3 ^ 40 * 6515436 * 2
def baseEnd_6515436 : Nat := 3345550341607475560386061

theorem tailTrace_6515436 : CollatzResearch.WordTrace tailWord_6515436 prefixEnd_6515436 3345550341607475560386061 := by
  unfold tailWord_6515436
  simp only [CollatzResearch.WordTrace]
  refine ⟨118818736811847797361763081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158424982415797063149017441 118818736811847797361763081)
  ·
    refine ⟨89114052608885848021322311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118818736811847797361763081 89114052608885848021322311)
    ·
      refine ⟨133671078913328772031983467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89114052608885848021322311 133671078913328772031983467)
      ·
        refine ⟨200506618369993158047975201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133671078913328772031983467 200506618369993158047975201)
        ·
          refine ⟨150379963777494868535981401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200506618369993158047975201 150379963777494868535981401)
          ·
            refine ⟨112784972833121151401986051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150379963777494868535981401 112784972833121151401986051)
            ·
              refine ⟨169177459249681727102979077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112784972833121151401986051 169177459249681727102979077)
              ·
                refine ⟨31720773609315323831808577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169177459249681727102979077 31720773609315323831808577)
                ·
                  refine ⟨23790580206986492873856433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31720773609315323831808577 23790580206986492873856433)
                  ·
                    refine ⟨17842935155239869655392325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23790580206986492873856433 17842935155239869655392325)
                    ·
                      refine ⟨3345550341607475560386061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17842935155239869655392325 3345550341607475560386061)
                      ·
                        rfl

theorem cell23_6515436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 4].length) (baseStart_6515436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515436 prefixEnd_6515436 := by exact prefixLift 6515436
  have htrace : WordTrace (prefixWord ++ tailWord_6515436) baseStart_6515436 baseEnd_6515436 := by
    simpa [prefixWord, tailWord_6515436, baseEnd_6515436] using wordTrace_append hprefix tailTrace_6515436
  have hstable : (prefixWord ++ tailWord_6515436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515436).length < 2 ^ (prefixWord ++ tailWord_6515436).sum := by decide
  have hdescent : baseEnd_6515436 < baseStart_6515436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515463 : List Nat := [1, 1, 4, 4, 1, 2, 1, 2, 7]
def baseStart_6515463 : Nat := 118140960795 + 6515463 * 2 ^ 59
def prefixEnd_6515463 : Nat := 4983230072969 + 3 ^ 40 * 6515463 * 2
def baseEnd_6515463 : Nat := 371729356176127439416493

theorem tailTrace_6515463 : CollatzResearch.WordTrace tailWord_6515463 prefixEnd_6515463 371729356176127439416493 := by
  unfold tailWord_6515463
  simp only [CollatzResearch.WordTrace]
  refine ⟨237638458394597778334759043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158425638929731852223172695 237638458394597778334759043)
  ·
    refine ⟨356457687591896667502138565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237638458394597778334759043 356457687591896667502138565)
    ·
      refine ⟨66835816423480625156650981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 356457687591896667502138565 66835816423480625156650981)
      ·
        refine ⟨12531715579402617216872059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 66835816423480625156650981 12531715579402617216872059)
        ·
          refine ⟨18797573369103925825308089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12531715579402617216872059 18797573369103925825308089)
          ·
            refine ⟨14098180026827944368981067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18797573369103925825308089 14098180026827944368981067)
            ·
              refine ⟨21147270040241916553471601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14098180026827944368981067 21147270040241916553471601)
              ·
                refine ⟨15860452530181437415103701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21147270040241916553471601 15860452530181437415103701)
                ·
                  refine ⟨371729356176127439416493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15860452530181437415103701 371729356176127439416493)
                  ·
                    rfl

theorem cell23_6515463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 2, 7].length) (baseStart_6515463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515463 prefixEnd_6515463 := by exact prefixLift 6515463
  have htrace : WordTrace (prefixWord ++ tailWord_6515463) baseStart_6515463 baseEnd_6515463 := by
    simpa [prefixWord, tailWord_6515463, baseEnd_6515463] using wordTrace_append hprefix tailTrace_6515463
  have hstable : (prefixWord ++ tailWord_6515463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515463).length < 2 ^ (prefixWord ++ tailWord_6515463).sum := by decide
  have hdescent : baseEnd_6515463 < baseStart_6515463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515523 : List Nat := [1, 1, 1, 3, 1, 4, 1, 4, 3, 4]
def baseStart_6515523 : Nat := 118140960795 + 6515523 * 2 ^ 59
def prefixEnd_6515523 : Nat := 4983230072969 + 3 ^ 40 * 6515523 * 2
def baseEnd_6515523 : Nat := 1115198338141472239999387

theorem tailTrace_6515523 : CollatzResearch.WordTrace tailWord_6515523 prefixEnd_6515523 1115198338141472239999387 := by
  unfold tailWord_6515523
  simp only [CollatzResearch.WordTrace]
  refine ⟨237640646774380408581943223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158427097849586939054628815 237640646774380408581943223)
  ·
    refine ⟨356460970161570612872914835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237640646774380408581943223 356460970161570612872914835)
    ·
      refine ⟨534691455242355919309372253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356460970161570612872914835 534691455242355919309372253)
      ·
        refine ⟨200509295715883469741014595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 534691455242355919309372253 200509295715883469741014595)
        ·
          refine ⟨300763943573825204611521893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200509295715883469741014595 300763943573825204611521893)
          ·
            refine ⟨56393239420092225864660355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 300763943573825204611521893 56393239420092225864660355)
            ·
              refine ⟨84589859130138338796990533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56393239420092225864660355 84589859130138338796990533)
              ·
                refine ⟨15860598586900938524435725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84589859130138338796990533 15860598586900938524435725)
                ·
                  refine ⟨5947724470087851946663397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15860598586900938524435725 5947724470087851946663397)
                  ·
                    refine ⟨1115198338141472239999387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5947724470087851946663397 1115198338141472239999387)
                    ·
                      rfl

theorem cell23_6515523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 4].length) (baseStart_6515523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515523 prefixEnd_6515523 := by exact prefixLift 6515523
  have htrace : WordTrace (prefixWord ++ tailWord_6515523) baseStart_6515523 baseEnd_6515523 := by
    simpa [prefixWord, tailWord_6515523, baseEnd_6515523] using wordTrace_append hprefix tailTrace_6515523
  have hstable : (prefixWord ++ tailWord_6515523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515523).length < 2 ^ (prefixWord ++ tailWord_6515523).sum := by decide
  have hdescent : baseEnd_6515523 < baseStart_6515523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515536 : List Nat := [2, 1, 1, 1, 1, 4, 3, 2, 8]
def baseStart_6515536 : Nat := 118140960795 + 6515536 * 2 ^ 59
def prefixEnd_6515536 : Nat := 4983230072969 + 3 ^ 40 * 6515536 * 2
def baseEnd_6515536 : Nat := 371733521074769463237289

theorem tailTrace_6515536 : CollatzResearch.WordTrace tailWord_6515536 prefixEnd_6515536 371733521074769463237289 := by
  unfold tailWord_6515536
  simp only [CollatzResearch.WordTrace]
  refine ⟨118820560461666655901083231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158427413948888874534777641 118820560461666655901083231)
  ·
    refine ⟨178230840692499983851624847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118820560461666655901083231 178230840692499983851624847)
    ·
      refine ⟨267346261038749975777437271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178230840692499983851624847 267346261038749975777437271)
      ·
        refine ⟨401019391558124963666155907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267346261038749975777437271 401019391558124963666155907)
        ·
          refine ⟨601529087337187445499233861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401019391558124963666155907 601529087337187445499233861)
          ·
            refine ⟨112786703875722646031106349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 601529087337187445499233861 112786703875722646031106349)
            ·
              refine ⟨42295013953395992261664881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112786703875722646031106349 42295013953395992261664881)
              ·
                refine ⟨31721260465046994196248661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42295013953395992261664881 31721260465046994196248661)
                ·
                  refine ⟨371733521074769463237289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31721260465046994196248661 371733521074769463237289)
                  ·
                    rfl

theorem cell23_6515536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 2, 8].length) (baseStart_6515536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515536 prefixEnd_6515536 := by exact prefixLift 6515536
  have htrace : WordTrace (prefixWord ++ tailWord_6515536) baseStart_6515536 baseEnd_6515536 := by
    simpa [prefixWord, tailWord_6515536, baseEnd_6515536] using wordTrace_append hprefix tailTrace_6515536
  have hstable : (prefixWord ++ tailWord_6515536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515536).length < 2 ^ (prefixWord ++ tailWord_6515536).sum := by decide
  have hdescent : baseEnd_6515536 < baseStart_6515536 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515570 : List Nat := [3, 2, 1, 2, 1, 1, 6, 1, 6]
def baseStart_6515570 : Nat := 118140960795 + 6515570 * 2 ^ 59
def prefixEnd_6515570 : Nat := 4983230072969 + 3 ^ 40 * 6515570 * 2
def baseEnd_6515570 : Nat := 371735460890575337345605

theorem tailTrace_6515570 : CollatzResearch.WordTrace tailWord_6515570 prefixEnd_6515570 371735460890575337345605 := by
  unfold tailWord_6515570
  simp only [CollatzResearch.WordTrace]
  refine ⟨59410590251302533902226041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158428240670140090405936109 59410590251302533902226041)
  ·
    refine ⟨44557942688476900426669531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59410590251302533902226041 44557942688476900426669531)
    ·
      refine ⟨66836914032715350640004297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44557942688476900426669531 66836914032715350640004297)
      ·
        refine ⟨50127685524536512980003223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66836914032715350640004297 50127685524536512980003223)
        ·
          refine ⟨75191528286804769470004835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50127685524536512980003223 75191528286804769470004835)
          ·
            refine ⟨112787292430207154205007253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75191528286804769470004835 112787292430207154205007253)
            ·
              refine ⟨5286904332665960353359715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 112787292430207154205007253 5286904332665960353359715)
              ·
                refine ⟨7930356498998940530039573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5286904332665960353359715 7930356498998940530039573)
                ·
                  refine ⟨371735460890575337345605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7930356498998940530039573 371735460890575337345605)
                  ·
                    rfl

theorem cell23_6515570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_6515570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515570 prefixEnd_6515570 := by exact prefixLift 6515570
  have htrace : WordTrace (prefixWord ++ tailWord_6515570) baseStart_6515570 baseEnd_6515570 := by
    simpa [prefixWord, tailWord_6515570, baseEnd_6515570] using wordTrace_append hprefix tailTrace_6515570
  have hstable : (prefixWord ++ tailWord_6515570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515570).length < 2 ^ (prefixWord ++ tailWord_6515570).sum := by decide
  have hdescent : baseEnd_6515570 < baseStart_6515570 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515576 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 1, 3, 7]
def baseStart_6515576 : Nat := 118140960795 + 6515576 * 2 ^ 59
def prefixEnd_6515576 : Nat := 4983230072969 + 3 ^ 40 * 6515576 * 2
def baseEnd_6515576 : Nat := 3345622228899105012635417

theorem tailTrace_6515576 : CollatzResearch.WordTrace tailWord_6515576 prefixEnd_6515576 3345622228899105012635417 := by
  unfold tailWord_6515576
  simp only [CollatzResearch.WordTrace]
  refine ⟨118821289921594199316811291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158428386562125599089081721 118821289921594199316811291)
  ·
    refine ⟨178231934882391298975216937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118821289921594199316811291 178231934882391298975216937)
    ·
      refine ⟨133673951161793474231412703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178231934882391298975216937 133673951161793474231412703)
      ·
        refine ⟨200510926742690211347119055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133673951161793474231412703 200510926742690211347119055)
        ·
          refine ⟨300766390114035317020678583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200510926742690211347119055 300766390114035317020678583)
          ·
            refine ⟨451149585171052975531017875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300766390114035317020678583 451149585171052975531017875)
            ·
              refine ⟨676724377756579463296526813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451149585171052975531017875 676724377756579463296526813)
              ·
                refine ⟨253771641658717298736197555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 676724377756579463296526813 253771641658717298736197555)
                ·
                  refine ⟨380657462488075948104296333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253771641658717298736197555 380657462488075948104296333)
                  ·
                    refine ⟨142746548433028480539111125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 380657462488075948104296333 142746548433028480539111125)
                    ·
                      refine ⟨3345622228899105012635417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142746548433028480539111125 3345622228899105012635417)
                      ·
                        rfl

theorem cell23_6515576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 1, 3, 7].length) (baseStart_6515576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515576 prefixEnd_6515576 := by exact prefixLift 6515576
  have htrace : WordTrace (prefixWord ++ tailWord_6515576) baseStart_6515576 baseEnd_6515576 := by
    simpa [prefixWord, tailWord_6515576, baseEnd_6515576] using wordTrace_append hprefix tailTrace_6515576
  have hstable : (prefixWord ++ tailWord_6515576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515576).length < 2 ^ (prefixWord ++ tailWord_6515576).sum := by decide
  have hdescent : baseEnd_6515576 < baseStart_6515576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515580 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 3, 1, 3]
def baseStart_6515580 : Nat := 118140960795 + 6515580 * 2 ^ 59
def prefixEnd_6515580 : Nat := 4983230072969 + 3 ^ 40 * 6515580 * 2
def baseEnd_6515580 : Nat := 3345624282821722996985399

theorem tailTrace_6515580 : CollatzResearch.WordTrace tailWord_6515580 prefixEnd_6515580 3345624282821722996985399 := by
  unfold tailWord_6515580
  simp only [CollatzResearch.WordTrace]
  refine ⟨118821362867586953658384097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158428483823449271544512129 118821362867586953658384097)
  ·
    refine ⟨89116022150690215243788073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118821362867586953658384097 89116022150690215243788073)
    ·
      refine ⟨66837016613017661432841055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89116022150690215243788073 66837016613017661432841055)
      ·
        refine ⟨100255524919526492149261583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66837016613017661432841055 100255524919526492149261583)
        ·
          refine ⟨150383287379289738223892375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100255524919526492149261583 150383287379289738223892375)
          ·
            refine ⟨225574931068934607335838563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150383287379289738223892375 225574931068934607335838563)
            ·
              refine ⟨338362396603401911003757845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225574931068934607335838563 338362396603401911003757845)
              ·
                refine ⟨15860737340784464578301149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 338362396603401911003757845 15860737340784464578301149)
                ·
                  refine ⟨5947776502794174216862931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15860737340784464578301149 5947776502794174216862931)
                  ·
                    refine ⟨8921664754191261325294397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5947776502794174216862931 8921664754191261325294397)
                    ·
                      refine ⟨3345624282821722996985399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8921664754191261325294397 3345624282821722996985399)
                      ·
                        rfl

theorem cell23_6515580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_6515580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515580 prefixEnd_6515580 := by exact prefixLift 6515580
  have htrace : WordTrace (prefixWord ++ tailWord_6515580) baseStart_6515580 baseEnd_6515580 := by
    simpa [prefixWord, tailWord_6515580, baseEnd_6515580] using wordTrace_append hprefix tailTrace_6515580
  have hstable : (prefixWord ++ tailWord_6515580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515580).length < 2 ^ (prefixWord ++ tailWord_6515580).sum := by decide
  have hdescent : baseEnd_6515580 < baseStart_6515580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515613 : List Nat := [1, 4, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_6515613 : Nat := 118140960795 + 6515613 * 2 ^ 59
def prefixEnd_6515613 : Nat := 4983230072969 + 3 ^ 40 * 6515613 * 2
def baseEnd_6515613 : Nat := 1115213742561107122624249

theorem tailTrace_6515613 : CollatzResearch.WordTrace tailWord_6515613 prefixEnd_6515613 1115213742561107122624249 := by
  unfold tailWord_6515613
  simp only [CollatzResearch.WordTrace]
  refine ⟨237643929344054353952719493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158429286229369569301812995 237643929344054353952719493)
  ·
    refine ⟨44558236752010191366134905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237643929344054353952719493 44558236752010191366134905)
    ·
      refine ⟨33418677564007643524601179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44558236752010191366134905 33418677564007643524601179)
      ·
        refine ⟨50128016346011465286901769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33418677564007643524601179 50128016346011465286901769)
        ·
          refine ⟨37596012259508598965176327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50128016346011465286901769 37596012259508598965176327)
          ·
            refine ⟨56394018389262898447764491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37596012259508598965176327 56394018389262898447764491)
            ·
              refine ⟨84591027583894347671646737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56394018389262898447764491 84591027583894347671646737)
              ·
                refine ⟨63443270687920760753735053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84591027583894347671646737 63443270687920760753735053)
                ·
                  refine ⟨23791226507970285282650645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63443270687920760753735053 23791226507970285282650645)
                  ·
                    refine ⟨1115213742561107122624249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23791226507970285282650645 1115213742561107122624249)
                    ·
                      rfl

theorem cell23_6515613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_6515613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515613 prefixEnd_6515613 := by exact prefixLift 6515613
  have htrace : WordTrace (prefixWord ++ tailWord_6515613) baseStart_6515613 baseEnd_6515613 := by
    simpa [prefixWord, tailWord_6515613, baseEnd_6515613] using wordTrace_append hprefix tailTrace_6515613
  have hstable : (prefixWord ++ tailWord_6515613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515613).length < 2 ^ (prefixWord ++ tailWord_6515613).sum := by decide
  have hdescent : baseEnd_6515613 < baseStart_6515613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515640 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 3, 2, 3]
def baseStart_6515640 : Nat := 118140960795 + 6515640 * 2 ^ 59
def prefixEnd_6515640 : Nat := 4983230072969 + 3 ^ 40 * 6515640 * 2
def baseEnd_6515640 : Nat := 3345655091660992762235123

theorem tailTrace_6515640 : CollatzResearch.WordTrace tailWord_6515640 prefixEnd_6515640 3345655091660992762235123 := by
  unfold tailWord_6515640
  simp only [CollatzResearch.WordTrace]
  refine ⟨118822457057478268781976187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158429942743304358375968249 118822457057478268781976187)
  ·
    refine ⟨178233685586217403172964281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118822457057478268781976187 178233685586217403172964281)
    ·
      refine ⟨133675264189663052379723211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178233685586217403172964281 133675264189663052379723211)
      ·
        refine ⟨200512896284494578569584817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133675264189663052379723211 200512896284494578569584817)
        ·
          refine ⟨150384672213370933927188613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200512896284494578569584817 150384672213370933927188613)
          ·
            refine ⟨28197126040007050111347865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150384672213370933927188613 28197126040007050111347865)
            ·
              refine ⟨21147844530005287583510899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28197126040007050111347865 21147844530005287583510899)
              ·
                refine ⟨31721766795007931375266349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21147844530005287583510899 31721766795007931375266349)
                ·
                  refine ⟨11895662548127974265724881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31721766795007931375266349 11895662548127974265724881)
                  ·
                    refine ⟨8921746911095980699293661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11895662548127974265724881 8921746911095980699293661)
                    ·
                      refine ⟨3345655091660992762235123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8921746911095980699293661 3345655091660992762235123)
                      ·
                        rfl

theorem cell23_6515640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 3, 2, 3].length) (baseStart_6515640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515640 prefixEnd_6515640 := by exact prefixLift 6515640
  have htrace : WordTrace (prefixWord ++ tailWord_6515640) baseStart_6515640 baseEnd_6515640 := by
    simpa [prefixWord, tailWord_6515640, baseEnd_6515640] using wordTrace_append hprefix tailTrace_6515640
  have hstable : (prefixWord ++ tailWord_6515640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515640).length < 2 ^ (prefixWord ++ tailWord_6515640).sum := by decide
  have hdescent : baseEnd_6515640 < baseStart_6515640 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515653 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 2, 7, 3]
def baseStart_6515653 : Nat := 118140960795 + 6515653 * 2 ^ 59
def prefixEnd_6515653 : Nat := 4983230072969 + 3 ^ 40 * 6515653 * 2
def baseEnd_6515653 : Nat := 3345661766909501211372563

theorem tailTrace_6515653 : CollatzResearch.WordTrace tailWord_6515653 prefixEnd_6515653 3345661766909501211372563 := by
  unfold tailWord_6515653
  simp only [CollatzResearch.WordTrace]
  refine ⟨237645388263909440784175613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158430258842606293856117075 237645388263909440784175613)
  ·
    refine ⟨89117020598966040294065855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237645388263909440784175613 89117020598966040294065855)
    ·
      refine ⟨133675530898449060441098783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89117020598966040294065855 133675530898449060441098783)
      ·
        refine ⟨200513296347673590661648175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133675530898449060441098783 200513296347673590661648175)
        ·
          refine ⟨300769944521510385992472263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200513296347673590661648175 300769944521510385992472263)
          ·
            refine ⟨451154916782265578988708395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300769944521510385992472263 451154916782265578988708395)
            ·
              refine ⟨676732375173398368483062593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451154916782265578988708395 676732375173398368483062593)
              ·
                refine ⟨507549281380048776362296945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676732375173398368483062593 507549281380048776362296945)
                ·
                  refine ⟨380661961035036582271722709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507549281380048776362296945 380661961035036582271722709)
                  ·
                    refine ⟨8921764711758669896993501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 380661961035036582271722709 8921764711758669896993501)
                    ·
                      refine ⟨3345661766909501211372563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8921764711758669896993501 3345661766909501211372563)
                      ·
                        rfl

theorem cell23_6515653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_6515653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515653 prefixEnd_6515653 := by exact prefixLift 6515653
  have htrace : WordTrace (prefixWord ++ tailWord_6515653) baseStart_6515653 baseEnd_6515653 := by
    simpa [prefixWord, tailWord_6515653, baseEnd_6515653] using wordTrace_append hprefix tailTrace_6515653
  have hstable : (prefixWord ++ tailWord_6515653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515653).length < 2 ^ (prefixWord ++ tailWord_6515653).sum := by decide
  have hdescent : baseEnd_6515653 < baseStart_6515653 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515687 : List Nat := [1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_6515687 : Nat := 118140960795 + 6515687 * 2 ^ 59
def prefixEnd_6515687 : Nat := 4983230072969 + 3 ^ 40 * 6515687 * 2
def baseEnd_6515687 : Nat := 3345679225251754078347407

theorem tailTrace_6515687 : CollatzResearch.WordTrace tailWord_6515687 prefixEnd_6515687 3345679225251754078347407 := by
  unfold tailWord_6515687
  simp only [CollatzResearch.WordTrace]
  refine ⟨237646628345786264590913315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158431085563857509727275543 237646628345786264590913315)
  ·
    refine ⟨356469942518679396886369973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237646628345786264590913315 356469942518679396886369973)
    ·
      refine ⟨33419057111126193458097185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 356469942518679396886369973 33419057111126193458097185)
      ·
        refine ⟨25064292833344645093572889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33419057111126193458097185 25064292833344645093572889)
        ·
          refine ⟨18798219625008483820179667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25064292833344645093572889 18798219625008483820179667)
          ·
            refine ⟨28197329437512725730269501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18798219625008483820179667 28197329437512725730269501)
            ·
              refine ⟨10573998539067272148851063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28197329437512725730269501 10573998539067272148851063)
              ·
                refine ⟨15860997808600908223276595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10573998539067272148851063 15860997808600908223276595)
                ·
                  refine ⟨23791496712901362334914893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15860997808600908223276595 23791496712901362334914893)
                  ·
                    refine ⟨8921811267338010875593085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23791496712901362334914893 8921811267338010875593085)
                    ·
                      refine ⟨3345679225251754078347407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8921811267338010875593085 3345679225251754078347407)
                      ·
                        rfl

theorem cell23_6515687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_6515687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515687 prefixEnd_6515687 := by exact prefixLift 6515687
  have htrace : WordTrace (prefixWord ++ tailWord_6515687) baseStart_6515687 baseEnd_6515687 := by
    simpa [prefixWord, tailWord_6515687, baseEnd_6515687] using wordTrace_append hprefix tailTrace_6515687
  have hstable : (prefixWord ++ tailWord_6515687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515687).length < 2 ^ (prefixWord ++ tailWord_6515687).sum := by decide
  have hdescent : baseEnd_6515687 < baseStart_6515687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515694 : List Nat := [4, 1, 2, 1, 5, 1, 2, 7]
def baseStart_6515694 : Nat := 118140960795 + 6515694 * 2 ^ 59
def prefixEnd_6515694 : Nat := 4983230072969 + 3 ^ 40 * 6515694 * 2
def baseEnd_6515694 : Nat := 123914178504308724109625

theorem tailTrace_6515694 : CollatzResearch.WordTrace tailWord_6515694 prefixEnd_6515694 123914178504308724109625 := by
  unfold tailWord_6515694
  simp only [CollatzResearch.WordTrace]
  refine ⟨29705860457095113098302267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158431255771173936524278757 29705860457095113098302267)
  ·
    refine ⟨44558790685642669647453401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29705860457095113098302267 44558790685642669647453401)
    ·
      refine ⟨33419093014232002235590051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44558790685642669647453401 33419093014232002235590051)
      ·
        refine ⟨50128639521348003353385077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33419093014232002235590051 50128639521348003353385077)
        ·
          refine ⟨4699559955126375314379851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50128639521348003353385077 4699559955126375314379851)
          ·
            refine ⟨7049339932689562971569777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4699559955126375314379851 7049339932689562971569777)
            ·
              refine ⟨5287004949517172228677333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7049339932689562971569777 5287004949517172228677333)
              ·
                refine ⟨123914178504308724109625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5287004949517172228677333 123914178504308724109625)
                ·
                  rfl

theorem cell23_6515694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_6515694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515694 prefixEnd_6515694 := by exact prefixLift 6515694
  have htrace : WordTrace (prefixWord ++ tailWord_6515694) baseStart_6515694 baseEnd_6515694 := by
    simpa [prefixWord, tailWord_6515694, baseEnd_6515694] using wordTrace_append hprefix tailTrace_6515694
  have hstable : (prefixWord ++ tailWord_6515694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515694).length < 2 ^ (prefixWord ++ tailWord_6515694).sum := by decide
  have hdescent : baseEnd_6515694 < baseStart_6515694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515790 : List Nat := [4, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_6515790 : Nat := 118140960795 + 6515790 * 2 ^ 59
def prefixEnd_6515790 : Nat := 4983230072969 + 3 ^ 40 * 6515790 * 2
def baseEnd_6515790 : Nat := 3345732113759167175359433

theorem tailTrace_6515790 : CollatzResearch.WordTrace tailWord_6515790 prefixEnd_6515790 3345732113759167175359433 := by
  unfold tailWord_6515790
  simp only [CollatzResearch.WordTrace]
  refine ⟨29706298133051639147739103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158433590042942075454608549 29706298133051639147739103)
  ·
    refine ⟨44559447199577458721608655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29706298133051639147739103 44559447199577458721608655)
    ·
      refine ⟨66839170799366188082412983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44559447199577458721608655 66839170799366188082412983)
      ·
        refine ⟨100258756199049282123619475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66839170799366188082412983 100258756199049282123619475)
        ·
          refine ⟨150388134298573923185429213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100258756199049282123619475 150388134298573923185429213)
          ·
            refine ⟨56395550361965221194535955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150388134298573923185429213 56395550361965221194535955)
            ·
              refine ⟨84593325542947831791803933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56395550361965221194535955 84593325542947831791803933)
              ·
                refine ⟨31722497078605436921926475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84593325542947831791803933 31722497078605436921926475)
                ·
                  refine ⟨47583745617908155382889713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31722497078605436921926475 47583745617908155382889713)
                  ·
                    refine ⟨35687809213431116537167285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47583745617908155382889713 35687809213431116537167285)
                    ·
                      refine ⟨3345732113759167175359433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35687809213431116537167285 3345732113759167175359433)
                      ·
                        rfl

theorem cell23_6515790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_6515790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515790 prefixEnd_6515790 := by exact prefixLift 6515790
  have htrace : WordTrace (prefixWord ++ tailWord_6515790) baseStart_6515790 baseEnd_6515790 := by
    simpa [prefixWord, tailWord_6515790, baseEnd_6515790] using wordTrace_append hprefix tailTrace_6515790
  have hstable : (prefixWord ++ tailWord_6515790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515790).length < 2 ^ (prefixWord ++ tailWord_6515790).sum := by decide
  have hdescent : baseEnd_6515790 < baseStart_6515790 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515800 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 1, 3, 4]
def baseStart_6515800 : Nat := 118140960795 + 6515800 * 2 ^ 59
def prefixEnd_6515800 : Nat := 4983230072969 + 3 ^ 40 * 6515800 * 2
def baseEnd_6515800 : Nat := 3345737248565712136234387

theorem tailTrace_6515800 : CollatzResearch.WordTrace tailWord_6515800 prefixEnd_6515800 3345737248565712136234387 := by
  unfold tailWord_6515800
  simp only [CollatzResearch.WordTrace]
  refine ⟨118825374897188442444888427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158433833196251256593184569 118825374897188442444888427)
  ·
    refine ⟨178238062345782663667332641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118825374897188442444888427 178238062345782663667332641)
    ·
      refine ⟨133678546759336997750499481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178238062345782663667332641 133678546759336997750499481)
      ·
        refine ⟨100258910069502748312874611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133678546759336997750499481 100258910069502748312874611)
        ·
          refine ⟨150388365104254122469311917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100258910069502748312874611 150388365104254122469311917)
          ·
            refine ⟨56395636914095295925991969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150388365104254122469311917 56395636914095295925991969)
            ·
              refine ⟨42296727685571471944493977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56395636914095295925991969 42296727685571471944493977)
              ·
                refine ⟨31722545764178603958370483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42296727685571471944493977 31722545764178603958370483)
                ·
                  refine ⟨47583818646267905937555725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31722545764178603958370483 47583818646267905937555725)
                  ·
                    refine ⟨17843931992350464726583397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47583818646267905937555725 17843931992350464726583397)
                    ·
                      refine ⟨3345737248565712136234387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17843931992350464726583397 3345737248565712136234387)
                      ·
                        rfl

theorem cell23_6515800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 1, 3, 4].length) (baseStart_6515800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515800 prefixEnd_6515800 := by exact prefixLift 6515800
  have htrace : WordTrace (prefixWord ++ tailWord_6515800) baseStart_6515800 baseEnd_6515800 := by
    simpa [prefixWord, tailWord_6515800, baseEnd_6515800] using wordTrace_append hprefix tailTrace_6515800
  have hstable : (prefixWord ++ tailWord_6515800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515800).length < 2 ^ (prefixWord ++ tailWord_6515800).sum := by decide
  have hdescent : baseEnd_6515800 < baseStart_6515800 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515817 : List Nat := [1, 2, 1, 1, 1, 6, 3, 1, 2, 1, 4]
def baseStart_6515817 : Nat := 118140960795 + 6515817 * 2 ^ 59
def prefixEnd_6515817 : Nat := 4983230072969 + 3 ^ 40 * 6515817 * 2
def baseEnd_6515817 : Nat := 3345745977736838569721809

theorem tailTrace_6515817 : CollatzResearch.WordTrace tailWord_6515817 prefixEnd_6515817 3345745977736838569721809 := by
  unfold tailWord_6515817
  simp only [CollatzResearch.WordTrace]
  refine ⟨237651369835315296793145705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158434246556876864528763803 237651369835315296793145705)
  ·
    refine ⟨178238527376486472594859279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237651369835315296793145705 178238527376486472594859279)
    ·
      refine ⟨267357791064729708892288919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178238527376486472594859279 267357791064729708892288919)
      ·
        refine ⟨401036686597094563338433379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267357791064729708892288919 401036686597094563338433379)
        ·
          refine ⟨601555029895641845007650069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401036686597094563338433379 601555029895641845007650069)
          ·
            refine ⟨28197892026358211484733597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 601555029895641845007650069 28197892026358211484733597)
            ·
              refine ⟨10574209509884329306775099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28197892026358211484733597 10574209509884329306775099)
              ·
                refine ⟨15861314264826493960162649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10574209509884329306775099 15861314264826493960162649)
                ·
                  refine ⟨11895985698619870470121987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15861314264826493960162649 11895985698619870470121987)
                  ·
                    refine ⟨17843978547929805705182981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11895985698619870470121987 17843978547929805705182981)
                    ·
                      refine ⟨3345745977736838569721809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17843978547929805705182981 3345745977736838569721809)
                      ·
                        rfl

theorem cell23_6515817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 1, 4].length) (baseStart_6515817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515817 prefixEnd_6515817 := by exact prefixLift 6515817
  have htrace : WordTrace (prefixWord ++ tailWord_6515817) baseStart_6515817 baseEnd_6515817 := by
    simpa [prefixWord, tailWord_6515817, baseEnd_6515817] using wordTrace_append hprefix tailTrace_6515817
  have hstable : (prefixWord ++ tailWord_6515817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515817).length < 2 ^ (prefixWord ++ tailWord_6515817).sum := by decide
  have hdescent : baseEnd_6515817 < baseStart_6515817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515837 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_6515837 : Nat := 118140960795 + 6515837 * 2 ^ 59
def prefixEnd_6515837 : Nat := 4983230072969 + 3 ^ 40 * 6515837 * 2
def baseEnd_6515837 : Nat := 3345756247349928491471717

theorem tailTrace_6515837 : CollatzResearch.WordTrace tailWord_6515837 prefixEnd_6515837 3345756247349928491471717 := by
  unfold tailWord_6515837
  simp only [CollatzResearch.WordTrace]
  refine ⟨237652099295242840208873765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158434732863495226805915843 237652099295242840208873765)
  ·
    refine ⟨44559768617858032539163831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237652099295242840208873765 44559768617858032539163831)
    ·
      refine ⟨66839652926787048808745747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44559768617858032539163831 66839652926787048808745747)
      ·
        refine ⟨100259479390180573213118621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66839652926787048808745747 100259479390180573213118621)
        ·
          refine ⟨37597304771317714954919483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100259479390180573213118621 37597304771317714954919483)
          ·
            refine ⟨56395957156976572432379225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37597304771317714954919483 56395957156976572432379225)
            ·
              refine ⟨42296967867732429324284419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56395957156976572432379225 42296967867732429324284419)
              ·
                refine ⟨63445451801598643986426629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42296967867732429324284419 63445451801598643986426629)
                ·
                  refine ⟨11896022212799745747454993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63445451801598643986426629 11896022212799745747454993)
                  ·
                    refine ⟨8922016659599809310591245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11896022212799745747454993 8922016659599809310591245)
                    ·
                      refine ⟨3345756247349928491471717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8922016659599809310591245 3345756247349928491471717)
                      ·
                        rfl

theorem cell23_6515837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_6515837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515837 prefixEnd_6515837 := by exact prefixLift 6515837
  have htrace : WordTrace (prefixWord ++ tailWord_6515837) baseStart_6515837 baseEnd_6515837 := by
    simpa [prefixWord, tailWord_6515837, baseEnd_6515837] using wordTrace_append hprefix tailTrace_6515837
  have hstable : (prefixWord ++ tailWord_6515837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515837).length < 2 ^ (prefixWord ++ tailWord_6515837).sum := by decide
  have hdescent : baseEnd_6515837 < baseStart_6515837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515844 : List Nat := [2, 3, 2, 1, 2, 3, 2, 1, 3, 4]
def baseStart_6515844 : Nat := 118140960795 + 6515844 * 2 ^ 59
def prefixEnd_6515844 : Nat := 4983230072969 + 3 ^ 40 * 6515844 * 2
def baseEnd_6515844 : Nat := 1115253280571503321361395

theorem tailTrace_6515844 : CollatzResearch.WordTrace tailWord_6515844 prefixEnd_6515844 1115253280571503321361395 := by
  unfold tailWord_6515844
  simp only [CollatzResearch.WordTrace]
  refine ⟨118826177303108740202189293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158434903070811653602919057 118826177303108740202189293)
  ·
    refine ⟨44559816488665777575820985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118826177303108740202189293 44559816488665777575820985)
    ·
      refine ⟨33419862366499333181865739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44559816488665777575820985 33419862366499333181865739)
      ·
        refine ⟨50129793549748999772798609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33419862366499333181865739 50129793549748999772798609)
        ·
          refine ⟨37597345162311749829598957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50129793549748999772798609 37597345162311749829598957)
          ·
            refine ⟨14099004435866906186099609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37597345162311749829598957 14099004435866906186099609)
            ·
              refine ⟨10574253326900179639574707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14099004435866906186099609 10574253326900179639574707)
              ·
                refine ⟨15861379990350269459362061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10574253326900179639574707 15861379990350269459362061)
                ·
                  refine ⟨5948017496381351047260773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15861379990350269459362061 5948017496381351047260773)
                  ·
                    refine ⟨1115253280571503321361395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5948017496381351047260773 1115253280571503321361395)
                    ·
                      rfl

theorem cell23_6515844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_6515844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515844 prefixEnd_6515844 := by exact prefixLift 6515844
  have htrace : WordTrace (prefixWord ++ tailWord_6515844) baseStart_6515844 baseEnd_6515844 := by
    simpa [prefixWord, tailWord_6515844, baseEnd_6515844] using wordTrace_append hprefix tailTrace_6515844
  have hstable : (prefixWord ++ tailWord_6515844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515844).length < 2 ^ (prefixWord ++ tailWord_6515844).sum := by decide
  have hdescent : baseEnd_6515844 < baseStart_6515844 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515887 : List Nat := [1, 1, 2, 1, 2, 3, 4, 3, 1, 5]
def baseStart_6515887 : Nat := 118140960795 + 6515887 * 2 ^ 59
def prefixEnd_6515887 : Nat := 4983230072969 + 3 ^ 40 * 6515887 * 2
def baseEnd_6515887 : Nat := 1115260640460884431948829

theorem tailTrace_6515887 : CollatzResearch.WordTrace tailWord_6515887 prefixEnd_6515887 1115260640460884431948829 := by
  unfold tailWord_6515887
  simp only [CollatzResearch.WordTrace]
  refine ⟨237653922945061698748193915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158435948630041132498795943 237653922945061698748193915)
  ·
    refine ⟨356480884417592548122290873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237653922945061698748193915 356480884417592548122290873)
    ·
      refine ⟨267360663313194411091718155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356480884417592548122290873 267360663313194411091718155)
      ·
        refine ⟨401040994969791616637577233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267360663313194411091718155 401040994969791616637577233)
        ·
          refine ⟨300780746227343712478182925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401040994969791616637577233 300780746227343712478182925)
          ·
            refine ⟨112792779835253892179318597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 300780746227343712478182925 112792779835253892179318597)
            ·
              refine ⟨21148646219110104783622237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 112792779835253892179318597 21148646219110104783622237)
              ·
                refine ⟨7930742332166289293858339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21148646219110104783622237 7930742332166289293858339)
                ·
                  refine ⟨11896113498249433940787509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7930742332166289293858339 11896113498249433940787509)
                  ·
                    refine ⟨1115260640460884431948829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11896113498249433940787509 1115260640460884431948829)
                    ·
                      rfl

theorem cell23_6515887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 3, 1, 5].length) (baseStart_6515887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515887 prefixEnd_6515887 := by exact prefixLift 6515887
  have htrace : WordTrace (prefixWord ++ tailWord_6515887) baseStart_6515887 baseEnd_6515887 := by
    simpa [prefixWord, tailWord_6515887, baseEnd_6515887] using wordTrace_append hprefix tailTrace_6515887
  have hstable : (prefixWord ++ tailWord_6515887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515887).length < 2 ^ (prefixWord ++ tailWord_6515887).sum := by decide
  have hdescent : baseEnd_6515887 < baseStart_6515887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515901 : List Nat := [1, 4, 1, 2, 1, 1, 2, 6, 1, 1, 3]
def baseStart_6515901 : Nat := 118140960795 + 6515901 * 2 ^ 59
def prefixEnd_6515901 : Nat := 4983230072969 + 3 ^ 40 * 6515901 * 2
def baseEnd_6515901 : Nat := 3345789110111816241071423

theorem tailTrace_6515901 : CollatzResearch.WordTrace tailWord_6515901 prefixEnd_6515901 3345789110111816241071423 := by
  unfold tailWord_6515901
  simp only [CollatzResearch.WordTrace]
  refine ⟨237654433567010979139203557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158436289044673986092802371 237654433567010979139203557)
  ·
    refine ⟨44560206293814558588600667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237654433567010979139203557 44560206293814558588600667)
    ·
      refine ⟨66840309440721837882901001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44560206293814558588600667 66840309440721837882901001)
      ·
        refine ⟨50130232080541378412175751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66840309440721837882901001 50130232080541378412175751)
        ·
          refine ⟨75195348120812067618263627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50130232080541378412175751 75195348120812067618263627)
          ·
            refine ⟨112793022181218101427395441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75195348120812067618263627 112793022181218101427395441)
            ·
              refine ⟨84594766635913576070546581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112793022181218101427395441 84594766635913576070546581)
              ·
                refine ⟨3965379686058448878306871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 84594766635913576070546581 3965379686058448878306871)
                ·
                  refine ⟨5948069529087673317460307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3965379686058448878306871 5948069529087673317460307)
                  ·
                    refine ⟨8922104293631509976190461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5948069529087673317460307 8922104293631509976190461)
                    ·
                      refine ⟨3345789110111816241071423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8922104293631509976190461 3345789110111816241071423)
                      ·
                        rfl

theorem cell23_6515901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_6515901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515901 prefixEnd_6515901 := by exact prefixLift 6515901
  have htrace : WordTrace (prefixWord ++ tailWord_6515901) baseStart_6515901 baseEnd_6515901 := by
    simpa [prefixWord, tailWord_6515901, baseEnd_6515901] using wordTrace_append hprefix tailTrace_6515901
  have hstable : (prefixWord ++ tailWord_6515901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515901).length < 2 ^ (prefixWord ++ tailWord_6515901).sum := by decide
  have hdescent : baseEnd_6515901 < baseStart_6515901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515907 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 2, 6, 2]
def baseStart_6515907 : Nat := 118140960795 + 6515907 * 2 ^ 59
def prefixEnd_6515907 : Nat := 4983230072969 + 3 ^ 40 * 6515907 * 2
def baseEnd_6515907 : Nat := 3345792190995743217596395

theorem tailTrace_6515907 : CollatzResearch.WordTrace tailWord_6515907 prefixEnd_6515907 3345792190995743217596395 := by
  unfold tailWord_6515907
  simp only [CollatzResearch.WordTrace]
  refine ⟨237654652404989242163921975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158436434936659494775947983 237654652404989242163921975)
  ·
    refine ⟨356481978607483863245882963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237654652404989242163921975 356481978607483863245882963)
    ·
      refine ⟨534722967911225794868824445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356481978607483863245882963 534722967911225794868824445)
      ·
        refine ⟨200521112966709673075809167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 534722967911225794868824445 200521112966709673075809167)
        ·
          refine ⟨300781669450064509613713751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200521112966709673075809167 300781669450064509613713751)
          ·
            refine ⟨451172504175096764420570627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300781669450064509613713751 451172504175096764420570627)
            ·
              refine ⟨676758756262645146630855941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451172504175096764420570627 676758756262645146630855941)
              ·
                refine ⟨126892266799245964993285489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 676758756262645146630855941 126892266799245964993285489)
                ·
                  refine ⟨95169200099434473744964117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126892266799245964993285489 95169200099434473744964117)
                  ·
                    refine ⟨4461056254660990956795193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95169200099434473744964117 4461056254660990956795193)
                    ·
                      refine ⟨3345792190995743217596395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4461056254660990956795193 3345792190995743217596395)
                      ·
                        rfl

theorem cell23_6515907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 6, 2].length) (baseStart_6515907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515907 prefixEnd_6515907 := by exact prefixLift 6515907
  have htrace : WordTrace (prefixWord ++ tailWord_6515907) baseStart_6515907 baseEnd_6515907 := by
    simpa [prefixWord, tailWord_6515907, baseEnd_6515907] using wordTrace_append hprefix tailTrace_6515907
  have hstable : (prefixWord ++ tailWord_6515907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515907).length < 2 ^ (prefixWord ++ tailWord_6515907).sum := by decide
  have hdescent : baseEnd_6515907 < baseStart_6515907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515908 : List Nat := [2, 3, 3, 1, 4, 1, 2, 1, 6]
def baseStart_6515908 : Nat := 118140960795 + 6515908 * 2 ^ 59
def prefixEnd_6515908 : Nat := 4983230072969 + 3 ^ 40 * 6515908 * 2
def baseEnd_6515908 : Nat := 371754744941821968187099

theorem tailTrace_6515908 : CollatzResearch.WordTrace tailWord_6515908 prefixEnd_6515908 371754744941821968187099 := by
  unfold tailWord_6515908
  simp only [CollatzResearch.WordTrace]
  refine ⟨118827344438992809667354189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158436459251990412889805585 118827344438992809667354189)
  ·
    refine ⟨44560254164622303625257821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118827344438992809667354189 44560254164622303625257821)
    ·
      refine ⟨16710095311733363859471683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44560254164622303625257821 16710095311733363859471683)
      ·
        refine ⟨25065142967600045789207525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16710095311733363859471683 25065142967600045789207525)
        ·
          refine ⟨4699714306425008585476411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25065142967600045789207525 4699714306425008585476411)
          ·
            refine ⟨7049571459637512878214617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4699714306425008585476411 7049571459637512878214617)
            ·
              refine ⟨5287178594728134658660963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7049571459637512878214617 5287178594728134658660963)
              ·
                refine ⟨7930767892092201987991445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5287178594728134658660963 7930767892092201987991445)
                ·
                  refine ⟨371754744941821968187099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7930767892092201987991445 371754744941821968187099)
                  ·
                    rfl

theorem cell23_6515908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 2, 1, 6].length) (baseStart_6515908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515908 prefixEnd_6515908 := by exact prefixLift 6515908
  have htrace : WordTrace (prefixWord ++ tailWord_6515908) baseStart_6515908 baseEnd_6515908 := by
    simpa [prefixWord, tailWord_6515908, baseEnd_6515908] using wordTrace_append hprefix tailTrace_6515908
  have hstable : (prefixWord ++ tailWord_6515908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515908).length < 2 ^ (prefixWord ++ tailWord_6515908).sum := by decide
  have hdescent : baseEnd_6515908 < baseStart_6515908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515937 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 3, 2, 4]
def baseStart_6515937 : Nat := 118140960795 + 6515937 * 2 ^ 59
def prefixEnd_6515937 : Nat := 4983230072969 + 3 ^ 40 * 6515937 * 2
def baseEnd_6515937 : Nat := 3345807595415378100221257

theorem tailTrace_6515937 : CollatzResearch.WordTrace tailWord_6515937 prefixEnd_6515937 3345807595415378100221257 := by
  unfold tailWord_6515937
  simp only [CollatzResearch.WordTrace]
  refine ⟨237655746594880557287514065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158437164396587038191676043 237655746594880557287514065)
  ·
    refine ⟨178241809946160417965635549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237655746594880557287514065 178241809946160417965635549)
    ·
      refine ⟨66840678729810156737113331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178241809946160417965635549 66840678729810156737113331)
      ·
        refine ⟨100261018094715235105669997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66840678729810156737113331 100261018094715235105669997)
        ·
          refine ⟨37597881785518213164626249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100261018094715235105669997 37597881785518213164626249)
          ·
            refine ⟨28198411339138659873469687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37597881785518213164626249 28198411339138659873469687)
            ·
              refine ⟨42297617008707989810204531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28198411339138659873469687 42297617008707989810204531)
              ·
                refine ⟨63446425513061984715306797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42297617008707989810204531 63446425513061984715306797)
                ·
                  refine ⟨23792409567398244268240049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63446425513061984715306797 23792409567398244268240049)
                  ·
                    refine ⟨17844307175548683201180037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23792409567398244268240049 17844307175548683201180037)
                    ·
                      refine ⟨3345807595415378100221257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17844307175548683201180037 3345807595415378100221257)
                      ·
                        rfl

theorem cell23_6515937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_6515937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515937 prefixEnd_6515937 := by exact prefixLift 6515937
  have htrace : WordTrace (prefixWord ++ tailWord_6515937) baseStart_6515937 baseEnd_6515937 := by
    simpa [prefixWord, tailWord_6515937, baseEnd_6515937] using wordTrace_append hprefix tailTrace_6515937
  have hstable : (prefixWord ++ tailWord_6515937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515937).length < 2 ^ (prefixWord ++ tailWord_6515937).sum := by decide
  have hdescent : baseEnd_6515937 < baseStart_6515937 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515951 : List Nat := [1, 1, 2, 1, 7, 1, 2, 2, 2, 4]
def baseStart_6515951 : Nat := 118140960795 + 6515951 * 2 ^ 59
def prefixEnd_6515951 : Nat := 4983230072969 + 3 ^ 40 * 6515951 * 2
def baseEnd_6515951 : Nat := 1115271594714847015148731

theorem tailTrace_6515951 : CollatzResearch.WordTrace tailWord_6515951 prefixEnd_6515951 1115271594714847015148731 := by
  unfold tailWord_6515951
  simp only [CollatzResearch.WordTrace]
  refine ⟨237656257216829837678523707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158437504811219891785682471 237656257216829837678523707)
  ·
    refine ⟨356484385825244756517785561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237656257216829837678523707 356484385825244756517785561)
    ·
      refine ⟨267363289368933567388339171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356484385825244756517785561 267363289368933567388339171)
      ·
        refine ⟨401044934053400351082508757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267363289368933567388339171 401044934053400351082508757)
        ·
          refine ⟨9399490641876570728496299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 401044934053400351082508757 9399490641876570728496299)
          ·
            refine ⟨14099235962814856092744449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9399490641876570728496299 14099235962814856092744449)
            ·
              refine ⟨10574426972111142069558337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14099235962814856092744449 10574426972111142069558337)
              ·
                refine ⟨7930820229083356552168753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10574426972111142069558337 7930820229083356552168753)
                ·
                  refine ⟨5948115171812517414126565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7930820229083356552168753 5948115171812517414126565)
                  ·
                    refine ⟨1115271594714847015148731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5948115171812517414126565 1115271594714847015148731)
                    ·
                      rfl

theorem cell23_6515951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 4].length) (baseStart_6515951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515951 prefixEnd_6515951 := by exact prefixLift 6515951
  have htrace : WordTrace (prefixWord ++ tailWord_6515951) baseStart_6515951 baseEnd_6515951 := by
    simpa [prefixWord, tailWord_6515951, baseEnd_6515951] using wordTrace_append hprefix tailTrace_6515951
  have hstable : (prefixWord ++ tailWord_6515951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515951).length < 2 ^ (prefixWord ++ tailWord_6515951).sum := by decide
  have hdescent : baseEnd_6515951 < baseStart_6515951 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6515964 : List Nat := [2, 2, 2, 1, 5, 2, 1, 8]
def baseStart_6515964 : Nat := 118140960795 + 6515964 * 2 ^ 59
def prefixEnd_6515964 : Nat := 4983230072969 + 3 ^ 40 * 6515964 * 2
def baseEnd_6515964 : Nat := 123919313310853684984579

theorem tailTrace_6515964 : CollatzResearch.WordTrace tailWord_6515964 prefixEnd_6515964 123919313310853684984579 := by
  unfold tailWord_6515964
  simp only [CollatzResearch.WordTrace]
  refine ⟨118828365682891370449373473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158437820910521827265831297 118828365682891370449373473)
  ·
    refine ⟨89121274262168527837030105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118828365682891370449373473 89121274262168527837030105)
    ·
      refine ⟨66840955696626395877772579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89121274262168527837030105 66840955696626395877772579)
      ·
        refine ⟨100261433544939593816658869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66840955696626395877772579 100261433544939593816658869)
        ·
          refine ⟨9399509394838086920311769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 100261433544939593816658869 9399509394838086920311769)
          ·
            refine ⟨7049632046128565190233827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9399509394838086920311769 7049632046128565190233827)
            ·
              refine ⟨10574448069192847785350741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7049632046128565190233827 10574448069192847785350741)
              ·
                refine ⟨123919313310853684984579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10574448069192847785350741 123919313310853684984579)
                ·
                  rfl

theorem cell23_6515964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 1, 8].length) (baseStart_6515964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6515964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6515964 prefixEnd_6515964 := by exact prefixLift 6515964
  have htrace : WordTrace (prefixWord ++ tailWord_6515964) baseStart_6515964 baseEnd_6515964 := by
    simpa [prefixWord, tailWord_6515964, baseEnd_6515964] using wordTrace_append hprefix tailTrace_6515964
  have hstable : (prefixWord ++ tailWord_6515964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6515964).length < 2 ^ (prefixWord ++ tailWord_6515964).sum := by decide
  have hdescent : baseEnd_6515964 < baseStart_6515964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6515964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516008 : List Nat := [2, 1, 5, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_6516008 : Nat := 118140960795 + 6516008 * 2 ^ 59
def prefixEnd_6516008 : Nat := 4983230072969 + 3 ^ 40 * 6516008 * 2
def baseEnd_6516008 : Nat := 3345844052541847322433431

theorem tailTrace_6516008 : CollatzResearch.WordTrace tailWord_6516008 prefixEnd_6516008 3345844052541847322433431 := by
  unfold tailWord_6516008
  simp only [CollatzResearch.WordTrace]
  refine ⟨118829168088811668206674339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158438890785082224275565785 118829168088811668206674339)
  ·
    refine ⟨178243752133217502310011509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118829168088811668206674339 178243752133217502310011509)
    ·
      refine ⟨16710351762489140841563579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178243752133217502310011509 16710351762489140841563579)
      ·
        refine ⟨25065527643733711262345369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16710351762489140841563579 25065527643733711262345369)
        ·
          refine ⟨18799145732800283446759027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25065527643733711262345369 18799145732800283446759027)
          ·
            refine ⟨28198718599200425170138541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18799145732800283446759027 28198718599200425170138541)
            ·
              refine ⟨10574519474700159438801953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28198718599200425170138541 10574519474700159438801953)
              ·
                refine ⟨7930889606025119579101465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10574519474700159438801953 7930889606025119579101465)
                ·
                  refine ⟨5948167204518839684326099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7930889606025119579101465 5948167204518839684326099)
                  ·
                    refine ⟨8922250806778259526489149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5948167204518839684326099 8922250806778259526489149)
                    ·
                      refine ⟨3345844052541847322433431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8922250806778259526489149 3345844052541847322433431)
                      ·
                        rfl

theorem cell23_6516008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_6516008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516008 prefixEnd_6516008 := by exact prefixLift 6516008
  have htrace : WordTrace (prefixWord ++ tailWord_6516008) baseStart_6516008 baseEnd_6516008 := by
    simpa [prefixWord, tailWord_6516008, baseEnd_6516008] using wordTrace_append hprefix tailTrace_6516008
  have hstable : (prefixWord ++ tailWord_6516008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516008).length < 2 ^ (prefixWord ++ tailWord_6516008).sum := by decide
  have hdescent : baseEnd_6516008 < baseStart_6516008 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516025 : List Nat := [1, 2, 1, 6, 2, 1, 3, 1, 2, 1, 3]
def baseStart_6516025 : Nat := 118140960795 + 6516025 * 2 ^ 59
def prefixEnd_6516025 : Nat := 4983230072969 + 3 ^ 40 * 6516025 * 2
def baseEnd_6516025 : Nat := 3345852781712973755920853

theorem tailTrace_6516025 : CollatzResearch.WordTrace tailWord_6516025 prefixEnd_6516025 3345852781712973755920853 := by
  unfold tailWord_6516025
  simp only [CollatzResearch.WordTrace]
  refine ⟨237658956218561748316717529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158439304145707832211145019 237658956218561748316717529)
  ·
    refine ⟨178244217163921311237538147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237658956218561748316717529 178244217163921311237538147)
    ·
      refine ⟨267366325745881966856307221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178244217163921311237538147 267366325745881966856307221)
      ·
        refine ⟨12532796519338217196389401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 267366325745881966856307221 12532796519338217196389401)
        ·
          refine ⟨9399597389503662897292051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12532796519338217196389401 9399597389503662897292051)
          ·
            refine ⟨14099396084255494345938077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9399597389503662897292051 14099396084255494345938077)
            ·
              refine ⟨5287273531595810379726779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14099396084255494345938077 5287273531595810379726779)
              ·
                refine ⟨7930910297393715569590169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5287273531595810379726779 7930910297393715569590169)
                ·
                  refine ⟨5948182723045286677192627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7930910297393715569590169 5948182723045286677192627)
                  ·
                    refine ⟨8922274084567930015788941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5948182723045286677192627 8922274084567930015788941)
                    ·
                      refine ⟨3345852781712973755920853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8922274084567930015788941 3345852781712973755920853)
                      ·
                        rfl

theorem cell23_6516025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_6516025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516025 prefixEnd_6516025 := by exact prefixLift 6516025
  have htrace : WordTrace (prefixWord ++ tailWord_6516025) baseStart_6516025 baseEnd_6516025 := by
    simpa [prefixWord, tailWord_6516025, baseEnd_6516025] using wordTrace_append hprefix tailTrace_6516025
  have hstable : (prefixWord ++ tailWord_6516025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516025).length < 2 ^ (prefixWord ++ tailWord_6516025).sum := by decide
  have hdescent : baseEnd_6516025 < baseStart_6516025 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516031 : List Nat := [1, 1, 2, 2, 4, 2, 3, 1, 1, 4, 2]
def baseStart_6516031 : Nat := 118140960795 + 6516031 * 2 ^ 59
def prefixEnd_6516031 : Nat := 4983230072969 + 3 ^ 40 * 6516031 * 2
def baseEnd_6516031 : Nat := 3345855862596900732445825

theorem tailTrace_6516031 : CollatzResearch.WordTrace tailWord_6516031 prefixEnd_6516031 3345855862596900732445825 := by
  unfold tailWord_6516031
  simp only [CollatzResearch.WordTrace]
  refine ⟨237659175056540011341435947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158439450037693340894290631 237659175056540011341435947)
  ·
    refine ⟨356488762584810017012153921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237659175056540011341435947 356488762584810017012153921)
    ·
      refine ⟨267366571938607512759115441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356488762584810017012153921 267366571938607512759115441)
      ·
        refine ⟨200524928953955634569336581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267366571938607512759115441 200524928953955634569336581)
        ·
          refine ⟨37598424178866681481750609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200524928953955634569336581 37598424178866681481750609)
          ·
            refine ⟨28198818134150011111312957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37598424178866681481750609 28198818134150011111312957)
            ·
              refine ⟨10574556800306254166742359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28198818134150011111312957 10574556800306254166742359)
              ·
                refine ⟨15861835200459381250113539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10574556800306254166742359 15861835200459381250113539)
                ·
                  refine ⟨23792752800689071875170309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15861835200459381250113539 23792752800689071875170309)
                  ·
                    refine ⟨4461141150129200976594433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23792752800689071875170309 4461141150129200976594433)
                    ·
                      refine ⟨3345855862596900732445825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4461141150129200976594433 3345855862596900732445825)
                      ·
                        rfl

theorem cell23_6516031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 1, 4, 2].length) (baseStart_6516031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516031 prefixEnd_6516031 := by exact prefixLift 6516031
  have htrace : WordTrace (prefixWord ++ tailWord_6516031) baseStart_6516031 baseEnd_6516031 := by
    simpa [prefixWord, tailWord_6516031, baseEnd_6516031] using wordTrace_append hprefix tailTrace_6516031
  have hstable : (prefixWord ++ tailWord_6516031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516031).length < 2 ^ (prefixWord ++ tailWord_6516031).sum := by decide
  have hdescent : baseEnd_6516031 < baseStart_6516031 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516071 : List Nat := [1, 1, 5, 1, 4, 2, 1, 1, 7]
def baseStart_6516071 : Nat := 118140960795 + 6516071 * 2 ^ 59
def prefixEnd_6516071 : Nat := 4983230072969 + 3 ^ 40 * 6516071 * 2
def baseEnd_6516071 : Nat := 371764044647008952882849

theorem tailTrace_6516071 : CollatzResearch.WordTrace tailWord_6516071 prefixEnd_6516071 371764044647008952882849 := by
  unfold tailWord_6516071
  simp only [CollatzResearch.WordTrace]
  refine ⟨237660633976395098172892067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158440422650930065448594711 237660633976395098172892067)
  ·
    refine ⟨356490950964592647259338101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237660633976395098172892067 356490950964592647259338101)
    ·
      refine ⟨33421026652930560680562947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 356490950964592647259338101 33421026652930560680562947)
      ·
        refine ⟨50131539979395841020844421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33421026652930560680562947 50131539979395841020844421)
        ·
          refine ⟨9399663746136720191408329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50131539979395841020844421 9399663746136720191408329)
          ·
            refine ⟨7049747809602540143556247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9399663746136720191408329 7049747809602540143556247)
            ·
              refine ⟨10574621714403810215334371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7049747809602540143556247 10574621714403810215334371)
              ·
                refine ⟨15861932571605715323001557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10574621714403810215334371 15861932571605715323001557)
                ·
                  refine ⟨371764044647008952882849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15861932571605715323001557 371764044647008952882849)
                  ·
                    rfl

theorem cell23_6516071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 1, 7].length) (baseStart_6516071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516071 prefixEnd_6516071 := by exact prefixLift 6516071
  have htrace : WordTrace (prefixWord ++ tailWord_6516071) baseStart_6516071 baseEnd_6516071 := by
    simpa [prefixWord, tailWord_6516071, baseEnd_6516071] using wordTrace_append hprefix tailTrace_6516071
  have hstable : (prefixWord ++ tailWord_6516071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516071).length < 2 ^ (prefixWord ++ tailWord_6516071).sum := by decide
  have hdescent : baseEnd_6516071 < baseStart_6516071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516204 : List Nat := [2, 2, 1, 1, 2, 1, 2, 5, 1, 6]
def baseStart_6516204 : Nat := 118140960795 + 6516204 * 2 ^ 59
def prefixEnd_6516204 : Nat := 4983230072969 + 3 ^ 40 * 6516204 * 2
def baseEnd_6516204 : Nat := 1115314898250042851860843

theorem tailTrace_6516204 : CollatzResearch.WordTrace tailWord_6516204 prefixEnd_6516204 1115314898250042851860843 := by
  unfold tailWord_6516204
  simp only [CollatzResearch.WordTrace]
  refine ⟨118832742442456630943741833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158443656589942174591655777 118832742442456630943741833)
  ·
    refine ⟨89124556831842473207806375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118832742442456630943741833 89124556831842473207806375)
    ·
      refine ⟨133686835247763709811709563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89124556831842473207806375 133686835247763709811709563)
      ·
        refine ⟨200530252871645564717564345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133686835247763709811709563 200530252871645564717564345)
        ·
          refine ⟨150397689653734173538173259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200530252871645564717564345 150397689653734173538173259)
          ·
            refine ⟨225596534480601260307259889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150397689653734173538173259 225596534480601260307259889)
            ·
              refine ⟨169197400860450945230444917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225596534480601260307259889 169197400860450945230444917)
              ·
                refine ⟨15862256330667276115354211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169197400860450945230444917 15862256330667276115354211)
                ·
                  refine ⟨23793384496000914173031317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15862256330667276115354211 23793384496000914173031317)
                  ·
                    refine ⟨1115314898250042851860843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23793384496000914173031317 1115314898250042851860843)
                    ·
                      rfl

theorem cell23_6516204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_6516204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516204 prefixEnd_6516204 := by exact prefixLift 6516204
  have htrace : WordTrace (prefixWord ++ tailWord_6516204) baseStart_6516204 baseEnd_6516204 := by
    simpa [prefixWord, tailWord_6516204, baseEnd_6516204] using wordTrace_append hprefix tailTrace_6516204
  have hstable : (prefixWord ++ tailWord_6516204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516204).length < 2 ^ (prefixWord ++ tailWord_6516204).sum := by decide
  have hdescent : baseEnd_6516204 < baseStart_6516204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516221 : List Nat := [1, 4, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_6516221 : Nat := 118140960795 + 6516221 * 2 ^ 59
def prefixEnd_6516221 : Nat := 4983230072969 + 3 ^ 40 * 6516221 * 2
def baseEnd_6516221 : Nat := 1115317807973751663023317

theorem tailTrace_6516221 : CollatzResearch.WordTrace tailWord_6516221 prefixEnd_6516221 1115317807973751663023317 := by
  unfold tailWord_6516221
  simp only [CollatzResearch.WordTrace]
  refine ⟨237666104925851673790852517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158444069950567782527235011 237666104925851673790852517)
  ·
    refine ⟨44562394673597188835784847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237666104925851673790852517 44562394673597188835784847)
    ·
      refine ⟨66843592010395783253677271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44562394673597188835784847 66843592010395783253677271)
      ·
        refine ⟨100265388015593674880515907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66843592010395783253677271 100265388015593674880515907)
        ·
          refine ⟨150398082023390512320773861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100265388015593674880515907 150398082023390512320773861)
          ·
            refine ⟨28199640379385721060145099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150398082023390512320773861 28199640379385721060145099)
            ·
              refine ⟨42299460569078581590217649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28199640379385721060145099 42299460569078581590217649)
              ·
                refine ⟨31724595426808936192663237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42299460569078581590217649 31724595426808936192663237)
                ·
                  refine ⟨5948361642526675536124357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31724595426808936192663237 5948361642526675536124357)
                  ·
                    refine ⟨1115317807973751663023317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5948361642526675536124357 1115317807973751663023317)
                    ·
                      rfl

theorem cell23_6516221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_6516221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516221 prefixEnd_6516221 := by exact prefixLift 6516221
  have htrace : WordTrace (prefixWord ++ tailWord_6516221) baseStart_6516221 baseEnd_6516221 := by
    simpa [prefixWord, tailWord_6516221, baseEnd_6516221] using wordTrace_append hprefix tailTrace_6516221
  have hstable : (prefixWord ++ tailWord_6516221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516221).length < 2 ^ (prefixWord ++ tailWord_6516221).sum := by decide
  have hdescent : baseEnd_6516221 < baseStart_6516221 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516231 : List Nat := [1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_6516231 : Nat := 118140960795 + 6516231 * 2 ^ 59
def prefixEnd_6516231 : Nat := 4983230072969 + 3 ^ 40 * 6516231 * 2
def baseEnd_6516231 : Nat := 3345958558727799949944905

theorem tailTrace_6516231 : CollatzResearch.WordTrace tailWord_6516231 prefixEnd_6516231 3345958558727799949944905 := by
  unfold tailWord_6516231
  simp only [CollatzResearch.WordTrace]
  refine ⟨237666469655815445498716547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158444313103876963665811031 237666469655815445498716547)
  ·
    refine ⟨356499704483723168248074821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237666469655815445498716547 356499704483723168248074821)
    ·
      refine ⟨66843694590698094046514029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 356499704483723168248074821 66843694590698094046514029)
      ·
        refine ⟨25066385471511785267442761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66843694590698094046514029 25066385471511785267442761)
        ·
          refine ⟨18799789103633838950582071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25066385471511785267442761 18799789103633838950582071)
          ·
            refine ⟨28199683655450758425873107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18799789103633838950582071 28199683655450758425873107)
            ·
              refine ⟨42299525483176137638809661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28199683655450758425873107 42299525483176137638809661)
              ·
                refine ⟨15862322056191051614553623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42299525483176137638809661 15862322056191051614553623)
                ·
                  refine ⟨23793483084286577421830435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15862322056191051614553623 23793483084286577421830435)
                  ·
                    refine ⟨35690224626429866132745653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23793483084286577421830435 35690224626429866132745653)
                    ·
                      refine ⟨3345958558727799949944905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35690224626429866132745653 3345958558727799949944905)
                      ·
                        rfl

theorem cell23_6516231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_6516231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516231 prefixEnd_6516231 := by exact prefixLift 6516231
  have htrace : WordTrace (prefixWord ++ tailWord_6516231) baseStart_6516231 baseEnd_6516231 := by
    simpa [prefixWord, tailWord_6516231, baseEnd_6516231] using wordTrace_append hprefix tailTrace_6516231
  have hstable : (prefixWord ++ tailWord_6516231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516231).length < 2 ^ (prefixWord ++ tailWord_6516231).sum := by decide
  have hdescent : baseEnd_6516231 < baseStart_6516231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516234 : List Nat := [3, 1, 2, 2, 2, 2, 11]
def baseStart_6516234 : Nat := 118140960795 + 6516234 * 2 ^ 59
def prefixEnd_6516234 : Nat := 4983230072969 + 3 ^ 40 * 6516234 * 2
def baseEnd_6516234 : Nat := 41308149372466215286511

theorem tailTrace_6516234 : CollatzResearch.WordTrace tailWord_6516234 prefixEnd_6516234 41308149372466215286511 := by
  unfold tailWord_6516234
  simp only [CollatzResearch.WordTrace]
  refine ⟨59416644768701144252768939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158444386049869718007383837 59416644768701144252768939)
  ·
    refine ⟨89124967153051716379153409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59416644768701144252768939 89124967153051716379153409)
    ·
      refine ⟨66843725364788787284365057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89124967153051716379153409 66843725364788787284365057)
      ·
        refine ⟨50132794023591590463273793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66843725364788787284365057 50132794023591590463273793)
        ·
          refine ⟨37599595517693692847455345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50132794023591590463273793 37599595517693692847455345)
          ·
            refine ⟨28199696638270269635591509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37599595517693692847455345 28199696638270269635591509)
            ·
              refine ⟨41308149372466215286511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28199696638270269635591509 41308149372466215286511)
              ·
                rfl

theorem cell23_6516234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 11].length) (baseStart_6516234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516234 prefixEnd_6516234 := by exact prefixLift 6516234
  have htrace : WordTrace (prefixWord ++ tailWord_6516234) baseStart_6516234 baseEnd_6516234 := by
    simpa [prefixWord, tailWord_6516234, baseEnd_6516234] using wordTrace_append hprefix tailTrace_6516234
  have hstable : (prefixWord ++ tailWord_6516234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516234).length < 2 ^ (prefixWord ++ tailWord_6516234).sum := by decide
  have hdescent : baseEnd_6516234 < baseStart_6516234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516245 : List Nat := [1, 3, 2, 1, 3, 2, 3, 1, 3, 2, 2]
def baseStart_6516245 : Nat := 118140960795 + 6516245 * 2 ^ 59
def prefixEnd_6516245 : Nat := 4983230072969 + 3 ^ 40 * 6516245 * 2
def baseEnd_6516245 : Nat := 3345965747456962895169841

theorem tailTrace_6516245 : CollatzResearch.WordTrace tailWord_6516245 prefixEnd_6516245 3345965747456962895169841 := by
  unfold tailWord_6516245
  simp only [CollatzResearch.WordTrace]
  refine ⟨237666980277764725889726189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158444653518509817259817459 237666980277764725889726189)
  ·
    refine ⟨89125117604161772208647321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237666980277764725889726189 89125117604161772208647321)
    ·
      refine ⟨66843838203121329156485491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89125117604161772208647321 66843838203121329156485491)
      ·
        refine ⟨100265757304681993734728237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66843838203121329156485491 100265757304681993734728237)
        ·
          refine ⟨37599658989255747650523089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100265757304681993734728237 37599658989255747650523089)
          ·
            refine ⟨28199744241941810737892317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37599658989255747650523089 28199744241941810737892317)
            ·
              refine ⟨10574904090728179026709619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28199744241941810737892317 10574904090728179026709619)
              ·
                refine ⟨15862356136092268540064429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10574904090728179026709619 15862356136092268540064429)
                ·
                  refine ⟨5948383551034600702524161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15862356136092268540064429 5948383551034600702524161)
                  ·
                    refine ⟨4461287663275950526893121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5948383551034600702524161 4461287663275950526893121)
                    ·
                      refine ⟨3345965747456962895169841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4461287663275950526893121 3345965747456962895169841)
                      ·
                        rfl

theorem cell23_6516245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_6516245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516245 prefixEnd_6516245 := by exact prefixLift 6516245
  have htrace : WordTrace (prefixWord ++ tailWord_6516245) baseStart_6516245 baseEnd_6516245 := by
    simpa [prefixWord, tailWord_6516245, baseEnd_6516245] using wordTrace_append hprefix tailTrace_6516245
  have hstable : (prefixWord ++ tailWord_6516245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516245).length < 2 ^ (prefixWord ++ tailWord_6516245).sum := by decide
  have hdescent : baseEnd_6516245 < baseStart_6516245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516261 : List Nat := [1, 3, 1, 2, 2, 1, 1, 5, 1, 3, 3]
def baseStart_6516261 : Nat := 118140960795 + 6516261 * 2 ^ 59
def prefixEnd_6516261 : Nat := 4983230072969 + 3 ^ 40 * 6516261 * 2
def baseEnd_6516261 : Nat := 3345973963147434832569767

theorem tailTrace_6516261 : CollatzResearch.WordTrace tailWord_6516261 prefixEnd_6516261 3345973963147434832569767 := by
  unfold tailWord_6516261
  simp only [CollatzResearch.WordTrace]
  refine ⟨237667563845706760622308637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158445042563804507081539091 237667563845706760622308637)
  ·
    refine ⟨89125336442140035233365739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237667563845706760622308637 89125336442140035233365739)
    ·
      refine ⟨133688004663210052850048609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89125336442140035233365739 133688004663210052850048609)
      ·
        refine ⟨100266003497407539637536457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133688004663210052850048609 100266003497407539637536457)
        ·
          refine ⟨75199502623055654728152343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100266003497407539637536457 75199502623055654728152343)
          ·
            refine ⟨112799253934583482092228515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75199502623055654728152343 112799253934583482092228515)
            ·
              refine ⟨169198880901875223138342773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112799253934583482092228515 169198880901875223138342773)
              ·
                refine ⟨15862395084550802169219635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169198880901875223138342773 15862395084550802169219635)
                ·
                  refine ⟨23793592626826203253829453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15862395084550802169219635 23793592626826203253829453)
                  ·
                    refine ⟨8922597235059826220186045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23793592626826203253829453 8922597235059826220186045)
                    ·
                      refine ⟨3345973963147434832569767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8922597235059826220186045 3345973963147434832569767)
                      ·
                        rfl

theorem cell23_6516261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_6516261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516261 prefixEnd_6516261 := by exact prefixLift 6516261
  have htrace : WordTrace (prefixWord ++ tailWord_6516261) baseStart_6516261 baseEnd_6516261 := by
    simpa [prefixWord, tailWord_6516261, baseEnd_6516261] using wordTrace_append hprefix tailTrace_6516261
  have hstable : (prefixWord ++ tailWord_6516261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516261).length < 2 ^ (prefixWord ++ tailWord_6516261).sum := by decide
  have hdescent : baseEnd_6516261 < baseStart_6516261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516311 : List Nat := [1, 1, 3, 2, 2, 4, 1, 1, 2, 6]
def baseStart_6516311 : Nat := 118140960795 + 6516311 * 2 ^ 59
def prefixEnd_6516311 : Nat := 4983230072969 + 3 ^ 40 * 6516311 * 2
def baseEnd_6516311 : Nat := 1115333212393386545648179

theorem tailTrace_6516311 : CollatzResearch.WordTrace tailWord_6516311 prefixEnd_6516311 1115333212393386545648179 := by
  unfold tailWord_6516311
  simp only [CollatzResearch.WordTrace]
  refine ⟨237669387495525619161628787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158446258330350412774419191 237669387495525619161628787)
  ·
    refine ⟨356504081243288428742443181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237669387495525619161628787 356504081243288428742443181)
    ·
      refine ⟨133689030466233160778416193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356504081243288428742443181 133689030466233160778416193)
      ·
        refine ⟨100266772849674870583812145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133689030466233160778416193 100266772849674870583812145)
        ·
          refine ⟨75200079637256152937859109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100266772849674870583812145 75200079637256152937859109)
          ·
            refine ⟨14100014931985528675848583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75200079637256152937859109 14100014931985528675848583)
            ·
              refine ⟨21150022397978293013772875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14100014931985528675848583 21150022397978293013772875)
              ·
                refine ⟨31725033596967439520659313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21150022397978293013772875 31725033596967439520659313)
                ·
                  refine ⟨23793775197725579640494485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31725033596967439520659313 23793775197725579640494485)
                  ·
                    refine ⟨1115333212393386545648179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23793775197725579640494485 1115333212393386545648179)
                    ·
                      rfl

theorem cell23_6516311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_6516311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516311 prefixEnd_6516311 := by exact prefixLift 6516311
  have htrace : WordTrace (prefixWord ++ tailWord_6516311) baseStart_6516311 baseEnd_6516311 := by
    simpa [prefixWord, tailWord_6516311, baseEnd_6516311] using wordTrace_append hprefix tailTrace_6516311
  have hstable : (prefixWord ++ tailWord_6516311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516311).length < 2 ^ (prefixWord ++ tailWord_6516311).sum := by decide
  have hdescent : baseEnd_6516311 < baseStart_6516311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516321 : List Nat := [1, 2, 3, 1, 1, 3, 1, 2, 2, 4, 3]
def baseStart_6516321 : Nat := 118140960795 + 6516321 * 2 ^ 59
def prefixEnd_6516321 : Nat := 4983230072969 + 3 ^ 40 * 6516321 * 2
def baseEnd_6516321 : Nat := 3346004771986704597819491

theorem tailTrace_6516321 : CollatzResearch.WordTrace tailWord_6516321 prefixEnd_6516321 3346004771986704597819491 := by
  unfold tailWord_6516321
  simp only [CollatzResearch.WordTrace]
  refine ⟨237669752225489390869492817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158446501483659593912995211 237669752225489390869492817)
  ·
    refine ⟨178252314169117043152119613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237669752225489390869492817 178252314169117043152119613)
    ·
      refine ⟨66844617813418891182044855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178252314169117043152119613 66844617813418891182044855)
      ·
        refine ⟨100266926720128336773067283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66844617813418891182044855 100266926720128336773067283)
        ·
          refine ⟨150400390080192505159600925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100266926720128336773067283 150400390080192505159600925)
          ·
            refine ⟨56400146280072189434850347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150400390080192505159600925 56400146280072189434850347)
            ·
              refine ⟨84600219420108284152275521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56400146280072189434850347 84600219420108284152275521)
              ·
                refine ⟨63450164565081213114206641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84600219420108284152275521 63450164565081213114206641)
                ·
                  refine ⟨47587623423810909835654981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63450164565081213114206641 47587623423810909835654981)
                  ·
                    refine ⟨8922679391964545594185309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47587623423810909835654981 8922679391964545594185309)
                    ·
                      refine ⟨3346004771986704597819491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8922679391964545594185309 3346004771986704597819491)
                      ·
                        rfl

theorem cell23_6516321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_6516321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516321 prefixEnd_6516321 := by exact prefixLift 6516321
  have htrace : WordTrace (prefixWord ++ tailWord_6516321) baseStart_6516321 baseEnd_6516321 := by
    simpa [prefixWord, tailWord_6516321, baseEnd_6516321] using wordTrace_append hprefix tailTrace_6516321
  have hstable : (prefixWord ++ tailWord_6516321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516321).length < 2 ^ (prefixWord ++ tailWord_6516321).sum := by decide
  have hdescent : baseEnd_6516321 < baseStart_6516321 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516381 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_6516381 : Nat := 118140960795 + 6516381 * 2 ^ 59
def prefixEnd_6516381 : Nat := 4983230072969 + 3 ^ 40 * 6516381 * 2
def baseEnd_6516381 : Nat := 3346035580825974363069215

theorem tailTrace_6516381 : CollatzResearch.WordTrace tailWord_6516381 prefixEnd_6516381 3346035580825974363069215 := by
  unfold tailWord_6516381
  simp only [CollatzResearch.WordTrace]
  refine ⟨237671940605272021116676997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158447960403514680744451331 237671940605272021116676997)
  ·
    refine ⟨44563488863488503959376937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237671940605272021116676997 44563488863488503959376937)
    ·
      refine ⟨33422616647616377969532703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44563488863488503959376937 33422616647616377969532703)
      ·
        refine ⟨50133924971424566954299055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33422616647616377969532703 50133924971424566954299055)
        ·
          refine ⟨75200887457136850431448583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50133924971424566954299055 75200887457136850431448583)
          ·
            refine ⟨112801331185705275647172875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75200887457136850431448583 112801331185705275647172875)
            ·
              refine ⟨169201996778557913470759313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112801331185705275647172875 169201996778557913470759313)
              ·
                refine ⟨126901497583918435103069485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169201996778557913470759313 126901497583918435103069485)
                ·
                  refine ⟨47588061593969413163651057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126901497583918435103069485 47588061593969413163651057)
                  ·
                    refine ⟨35691046195477059872738293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47588061593969413163651057 35691046195477059872738293)
                    ·
                      refine ⟨3346035580825974363069215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35691046195477059872738293 3346035580825974363069215)
                      ·
                        rfl

theorem cell23_6516381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_6516381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516381 prefixEnd_6516381 := by exact prefixLift 6516381
  have htrace : WordTrace (prefixWord ++ tailWord_6516381) baseStart_6516381 baseEnd_6516381 := by
    simpa [prefixWord, tailWord_6516381, baseEnd_6516381] using wordTrace_append hprefix tailTrace_6516381
  have hstable : (prefixWord ++ tailWord_6516381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516381).length < 2 ^ (prefixWord ++ tailWord_6516381).sum := by decide
  have hdescent : baseEnd_6516381 < baseStart_6516381 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516405 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 2, 5]
def baseStart_6516405 : Nat := 118140960795 + 6516405 * 2 ^ 59
def prefixEnd_6516405 : Nat := 4983230072969 + 3 ^ 40 * 6516405 * 2
def baseEnd_6516405 : Nat := 1115349301453894089723035

theorem tailTrace_6516405 : CollatzResearch.WordTrace tailWord_6516405 prefixEnd_6516405 1115349301453894089723035 := by
  unfold tailWord_6516405
  simp only [CollatzResearch.WordTrace]
  refine ⟨237672815957185073215550669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158448543971456715477033779 237672815957185073215550669)
  ·
    refine ⟨89127305983944402455831501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237672815957185073215550669 89127305983944402455831501)
    ·
      refine ⟨33422739743979150920936813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89127305983944402455831501 33422739743979150920936813)
      ·
        refine ⟨12533527403992181595351305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33422739743979150920936813 12533527403992181595351305)
        ·
          refine ⟨9400145552994136196513479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12533527403992181595351305 9400145552994136196513479)
          ·
            refine ⟨14100218329491204294770219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9400145552994136196513479 14100218329491204294770219)
            ·
              refine ⟨21150327494236806442155329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14100218329491204294770219 21150327494236806442155329)
              ·
                refine ⟨15862745620677604831616497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21150327494236806442155329 15862745620677604831616497)
                ·
                  refine ⟨11897059215508203623712373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15862745620677604831616497 11897059215508203623712373)
                  ·
                    refine ⟨1115349301453894089723035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11897059215508203623712373 1115349301453894089723035)
                    ·
                      rfl

theorem cell23_6516405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_6516405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516405 prefixEnd_6516405 := by exact prefixLift 6516405
  have htrace : WordTrace (prefixWord ++ tailWord_6516405) baseStart_6516405 baseEnd_6516405 := by
    simpa [prefixWord, tailWord_6516405, baseEnd_6516405] using wordTrace_append hprefix tailTrace_6516405
  have hstable : (prefixWord ++ tailWord_6516405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516405).length < 2 ^ (prefixWord ++ tailWord_6516405).sum := by decide
  have hdescent : baseEnd_6516405 < baseStart_6516405 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516408 : List Nat := [2, 1, 2, 1, 2, 1, 1, 3, 4, 4, 2]
def baseStart_6516408 : Nat := 118140960795 + 6516408 * 2 ^ 59
def prefixEnd_6516408 : Nat := 4983230072969 + 3 ^ 40 * 6516408 * 2
def baseEnd_6516408 : Nat := 3346049444803645757431591

theorem tailTrace_6516408 : CollatzResearch.WordTrace tailWord_6516408 prefixEnd_6516408 3346049444803645757431591 := by
  unfold tailWord_6516408
  simp only [CollatzResearch.WordTrace]
  refine ⟨118836462688087102363954939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158448616917449469818606585 118836462688087102363954939)
  ·
    refine ⟨178254694032130653545932409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118836462688087102363954939 178254694032130653545932409)
    ·
      refine ⟨133691020524097990159449307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178254694032130653545932409 133691020524097990159449307)
      ·
        refine ⟨200536530786146985239173961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133691020524097990159449307 200536530786146985239173961)
        ·
          refine ⟨150402398089610238929380471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200536530786146985239173961 150402398089610238929380471)
          ·
            refine ⟨225603597134415358394070707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150402398089610238929380471 225603597134415358394070707)
            ·
              refine ⟨338405395701623037591106061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225603597134415358394070707 338405395701623037591106061)
              ·
                refine ⟨126902023388108639096664773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338405395701623037591106061 126902023388108639096664773)
                ·
                  refine ⟨23794129385270369830624645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126902023388108639096664773 23794129385270369830624645)
                  ·
                    refine ⟨4461399259738194343242121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23794129385270369830624645 4461399259738194343242121)
                    ·
                      refine ⟨3346049444803645757431591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4461399259738194343242121 3346049444803645757431591)
                      ·
                        rfl

theorem cell23_6516408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 3, 4, 4, 2].length) (baseStart_6516408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516408 prefixEnd_6516408 := by exact prefixLift 6516408
  have htrace : WordTrace (prefixWord ++ tailWord_6516408) baseStart_6516408 baseEnd_6516408 := by
    simpa [prefixWord, tailWord_6516408, baseEnd_6516408] using wordTrace_append hprefix tailTrace_6516408
  have hstable : (prefixWord ++ tailWord_6516408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516408).length < 2 ^ (prefixWord ++ tailWord_6516408).sum := by decide
  have hdescent : baseEnd_6516408 < baseStart_6516408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516493 : List Nat := [1, 7, 2, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_6516493 : Nat := 118140960795 + 6516493 * 2 ^ 59
def prefixEnd_6516493 : Nat := 4983230072969 + 3 ^ 40 * 6516493 * 2
def baseEnd_6516493 : Nat := 3346093090659277924868701

theorem tailTrace_6516493 : CollatzResearch.WordTrace tailWord_6516493 prefixEnd_6516493 3346093090659277924868701 := by
  unfold tailWord_6516493
  simp only [CollatzResearch.WordTrace]
  refine ⟨237676025580866264244754133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158450683720577509496502755 237676025580866264244754133)
  ·
    refine ⟨5570531849551553068236425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 237676025580866264244754133 5570531849551553068236425)
    ·
      refine ⟨4177898887163664801177319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5570531849551553068236425 4177898887163664801177319)
      ·
        refine ⟨6266848330745497201765979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4177898887163664801177319 6266848330745497201765979)
        ·
          refine ⟨9400272496118245802648969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6266848330745497201765979 9400272496118245802648969)
          ·
            refine ⟨7050204372088684351986727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9400272496118245802648969 7050204372088684351986727)
            ·
              refine ⟨10575306558133026527980091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7050204372088684351986727 10575306558133026527980091)
              ·
                refine ⟨15862959837199539791970137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10575306558133026527980091 15862959837199539791970137)
                ·
                  refine ⟨11897219877899654843977603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15862959837199539791970137 11897219877899654843977603)
                  ·
                    refine ⟨17845829816849482265966405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11897219877899654843977603 17845829816849482265966405)
                    ·
                      refine ⟨3346093090659277924868701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17845829816849482265966405 3346093090659277924868701)
                      ·
                        rfl

theorem cell23_6516493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_6516493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516493 prefixEnd_6516493 := by exact prefixLift 6516493
  have htrace : WordTrace (prefixWord ++ tailWord_6516493) baseStart_6516493 baseEnd_6516493 := by
    simpa [prefixWord, tailWord_6516493, baseEnd_6516493] using wordTrace_append hprefix tailTrace_6516493
  have hstable : (prefixWord ++ tailWord_6516493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516493).length < 2 ^ (prefixWord ++ tailWord_6516493).sum := by decide
  have hdescent : baseEnd_6516493 < baseStart_6516493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516508 : List Nat := [2, 2, 3, 1, 1, 2, 1, 4, 1, 6]
def baseStart_6516508 : Nat := 118140960795 + 6516508 * 2 ^ 59
def prefixEnd_6516508 : Nat := 4983230072969 + 3 ^ 40 * 6516508 * 2
def baseEnd_6516508 : Nat := 1115366930956365122060377

theorem tailTrace_6516508 : CollatzResearch.WordTrace tailWord_6516508 prefixEnd_6516508 1115366930956365122060377 := by
  unfold tailWord_6516508
  simp only [CollatzResearch.WordTrace]
  refine ⟨118838286337905960903275089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158451048450541281204366785 118838286337905960903275089)
  ·
    refine ⟨89128714753429470677456317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118838286337905960903275089 89128714753429470677456317)
    ·
      refine ⟨33423268032536051504046119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89128714753429470677456317 33423268032536051504046119)
      ·
        refine ⟨50134902048804077256069179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33423268032536051504046119 50134902048804077256069179)
        ·
          refine ⟨75202353073206115884103769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50134902048804077256069179 75202353073206115884103769)
          ·
            refine ⟨56401764804904586913077827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75202353073206115884103769 56401764804904586913077827)
            ·
              refine ⟨84602647207356880369616741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56401764804904586913077827 84602647207356880369616741)
              ·
                refine ⟨15862996351379415069303139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84602647207356880369616741 15862996351379415069303139)
                ·
                  refine ⟨23794494527069122603954709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15862996351379415069303139 23794494527069122603954709)
                  ·
                    refine ⟨1115366930956365122060377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23794494527069122603954709 1115366930956365122060377)
                    ·
                      rfl

theorem cell23_6516508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_6516508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516508 prefixEnd_6516508 := by exact prefixLift 6516508
  have htrace : WordTrace (prefixWord ++ tailWord_6516508) baseStart_6516508 baseEnd_6516508 := by
    simpa [prefixWord, tailWord_6516508, baseEnd_6516508] using wordTrace_append hprefix tailTrace_6516508
  have hstable : (prefixWord ++ tailWord_6516508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516508).length < 2 ^ (prefixWord ++ tailWord_6516508).sum := by decide
  have hdescent : baseEnd_6516508 < baseStart_6516508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516542 : List Nat := [4, 2, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_6516542 : Nat := 118140960795 + 6516542 * 2 ^ 59
def prefixEnd_6516542 : Nat := 4983230072969 + 3 ^ 40 * 6516542 * 2
def baseEnd_6516542 : Nat := 1115372750403782744385325

theorem tailTrace_6516542 : CollatzResearch.WordTrace tailWord_6516542 prefixEnd_6516542 1115372750403782744385325 := by
  unfold tailWord_6516542
  simp only [CollatzResearch.WordTrace]
  refine ⟨29709726594711093201660985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158451875171792497075525253 29709726594711093201660985)
  ·
    refine ⟨22282294946033319901245739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29709726594711093201660985 22282294946033319901245739)
    ·
      refine ⟨33423442419049979851868609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22282294946033319901245739 33423442419049979851868609)
      ·
        refine ⟨25067581814287484888901457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33423442419049979851868609 25067581814287484888901457)
        ·
          refine ⟨18800686360715613666676093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25067581814287484888901457 18800686360715613666676093)
          ·
            refine ⟨7050257385268355125003535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18800686360715613666676093 7050257385268355125003535)
            ·
              refine ⟨10575386077902532687505303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7050257385268355125003535 10575386077902532687505303)
              ·
                refine ⟨15863079116853799031257955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10575386077902532687505303 15863079116853799031257955)
                ·
                  refine ⟨23794618675280698546886933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15863079116853799031257955 23794618675280698546886933)
                  ·
                    refine ⟨1115372750403782744385325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23794618675280698546886933 1115372750403782744385325)
                    ·
                      rfl

theorem cell23_6516542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_6516542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516542 prefixEnd_6516542 := by exact prefixLift 6516542
  have htrace : WordTrace (prefixWord ++ tailWord_6516542) baseStart_6516542 baseEnd_6516542 := by
    simpa [prefixWord, tailWord_6516542, baseEnd_6516542] using wordTrace_append hprefix tailTrace_6516542
  have hstable : (prefixWord ++ tailWord_6516542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516542).length < 2 ^ (prefixWord ++ tailWord_6516542).sum := by decide
  have hdescent : baseEnd_6516542 < baseStart_6516542 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516552 : List Nat := [2, 1, 3, 1, 1, 5, 2, 2, 1, 2, 3]
def baseStart_6516552 : Nat := 118140960795 + 6516552 * 2 ^ 59
def prefixEnd_6516552 : Nat := 4983230072969 + 3 ^ 40 * 6516552 * 2
def baseEnd_6516552 : Nat := 3346123386017893194030929

theorem tailTrace_6516552 : CollatzResearch.WordTrace tailWord_6516552 prefixEnd_6516552 3346123386017893194030929 := by
  unfold tailWord_6516552
  simp only [CollatzResearch.WordTrace]
  refine ⟨118839088743826258660575955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158452118325101678214101273 118839088743826258660575955)
  ·
    refine ⟨178258633115739387990863933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118839088743826258660575955 178258633115739387990863933)
    ·
      refine ⟨66846987418402270496573975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178258633115739387990863933 66846987418402270496573975)
      ·
        refine ⟨100270481127603405744860963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66846987418402270496573975 100270481127603405744860963)
        ·
          refine ⟨150405721691405108617291445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100270481127603405744860963 150405721691405108617291445)
          ·
            refine ⟨14100536408569228932871073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150405721691405108617291445 14100536408569228932871073)
            ·
              refine ⟨10575402306426921699653305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14100536408569228932871073 10575402306426921699653305)
              ·
                refine ⟨7931551729820191274739979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10575402306426921699653305 7931551729820191274739979)
                ·
                  refine ⟨11897327594730286912109969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7931551729820191274739979 11897327594730286912109969)
                  ·
                    refine ⟨8922995696047715184082477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11897327594730286912109969 8922995696047715184082477)
                    ·
                      refine ⟨3346123386017893194030929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8922995696047715184082477 3346123386017893194030929)
                      ·
                        rfl

theorem cell23_6516552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_6516552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516552 prefixEnd_6516552 := by exact prefixLift 6516552
  have htrace : WordTrace (prefixWord ++ tailWord_6516552) baseStart_6516552 baseEnd_6516552 := by
    simpa [prefixWord, tailWord_6516552, baseEnd_6516552] using wordTrace_append hprefix tailTrace_6516552
  have hstable : (prefixWord ++ tailWord_6516552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516552).length < 2 ^ (prefixWord ++ tailWord_6516552).sum := by decide
  have hdescent : baseEnd_6516552 < baseStart_6516552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516572 : List Nat := [2, 2, 4, 2, 3, 1, 9]
def baseStart_6516572 : Nat := 118140960795 + 6516572 * 2 ^ 59
def prefixEnd_6516572 : Nat := 4983230072969 + 3 ^ 40 * 6516572 * 2
def baseEnd_6516572 : Nat := 41310292044826952046677

theorem tailTrace_6516572 : CollatzResearch.WordTrace tailWord_6516572 prefixEnd_6516572 41310292044826952046677 := by
  unfold tailWord_6516572
  simp only [CollatzResearch.WordTrace]
  refine ⟨118839453473790030368439985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158452604631720040491253313 118839453473790030368439985)
  ·
    refine ⟨89129590105342522776329989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118839453473790030368439985 89129590105342522776329989)
    ·
      refine ⟨16711798144751723020561873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89129590105342522776329989 16711798144751723020561873)
      ·
        refine ⟨12533848608563792265421405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16711798144751723020561873 12533848608563792265421405)
        ·
          refine ⟨4700193228211422099533027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12533848608563792265421405 4700193228211422099533027)
          ·
            refine ⟨7050289842317133149299541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4700193228211422099533027 7050289842317133149299541)
            ·
              refine ⟨41310292044826952046677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7050289842317133149299541 41310292044826952046677)
              ·
                rfl

theorem cell23_6516572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 9].length) (baseStart_6516572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516572 prefixEnd_6516572 := by exact prefixLift 6516572
  have htrace : WordTrace (prefixWord ++ tailWord_6516572) baseStart_6516572 baseEnd_6516572 := by
    simpa [prefixWord, tailWord_6516572, baseEnd_6516572] using wordTrace_append hprefix tailTrace_6516572
  have hstable : (prefixWord ++ tailWord_6516572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516572).length < 2 ^ (prefixWord ++ tailWord_6516572).sum := by decide
  have hdescent : baseEnd_6516572 < baseStart_6516572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516608 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 5]
def baseStart_6516608 : Nat := 118140960795 + 6516608 * 2 ^ 59
def prefixEnd_6516608 : Nat := 4983230072969 + 3 ^ 40 * 6516608 * 2
def baseEnd_6516608 : Nat := 3346152140934544974930671

theorem tailTrace_6516608 : CollatzResearch.WordTrace tailWord_6516608 prefixEnd_6516608 3346152140934544974930671 := by
  unfold tailWord_6516608
  simp only [CollatzResearch.WordTrace]
  refine ⟨118840109987724819442595239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158453479983633092590126985 118840109987724819442595239)
  ·
    refine ⟨178260164981587229163892859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118840109987724819442595239 178260164981587229163892859)
    ·
      refine ⟨267390247472380843745839289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178260164981587229163892859 267390247472380843745839289)
      ·
        refine ⟨200542685604285632809379467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267390247472380843745839289 200542685604285632809379467)
        ·
          refine ⟨300814028406428449214069201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200542685604285632809379467 300814028406428449214069201)
          ·
            refine ⟨225610521304821336910551901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300814028406428449214069201 225610521304821336910551901)
            ·
              refine ⟨84603945489308001341456963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225610521304821336910551901 84603945489308001341456963)
              ·
                refine ⟨126905918233962002012185445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84603945489308001341456963 126905918233962002012185445)
                ·
                  refine ⟨23794859668867875377284771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126905918233962002012185445 23794859668867875377284771)
                  ·
                    refine ⟨35692289503301813065927157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23794859668867875377284771 35692289503301813065927157)
                    ·
                      refine ⟨3346152140934544974930671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35692289503301813065927157 3346152140934544974930671)
                      ·
                        rfl

theorem cell23_6516608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 5].length) (baseStart_6516608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516608 prefixEnd_6516608 := by exact prefixLift 6516608
  have htrace : WordTrace (prefixWord ++ tailWord_6516608) baseStart_6516608 baseEnd_6516608 := by
    simpa [prefixWord, tailWord_6516608, baseEnd_6516608] using wordTrace_append hprefix tailTrace_6516608
  have hstable : (prefixWord ++ tailWord_6516608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516608).length < 2 ^ (prefixWord ++ tailWord_6516608).sum := by decide
  have hdescent : baseEnd_6516608 < baseStart_6516608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516655 : List Nat := [1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 3]
def baseStart_6516655 : Nat := 118140960795 + 6516655 * 2 ^ 59
def prefixEnd_6516655 : Nat := 4983230072969 + 3 ^ 40 * 6516655 * 2
def baseEnd_6516655 : Nat := 3346176274525306291042955

theorem tailTrace_6516655 : CollatzResearch.WordTrace tailWord_6516655 prefixEnd_6516655 3346176274525306291042955 := by
  unfold tailWord_6516655
  simp only [CollatzResearch.WordTrace]
  refine ⟨237681934206279365912151419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158454622804186243941434279 237681934206279365912151419)
  ·
    refine ⟨356522901309419048868227129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237681934206279365912151419 356522901309419048868227129)
    ·
      refine ⟨267392175982064286651170347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356522901309419048868227129 267392175982064286651170347)
      ·
        refine ⟨401088263973096429976755521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267392175982064286651170347 401088263973096429976755521)
        ·
          refine ⟨300816197979822322482566641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401088263973096429976755521 300816197979822322482566641)
          ·
            refine ⟨225612148484866741861924981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300816197979822322482566641 225612148484866741861924981)
            ·
              refine ⟨21151138920456257049555467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225612148484866741861924981 21151138920456257049555467)
              ·
                refine ⟨31726708380684385574333201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21151138920456257049555467 31726708380684385574333201)
                ·
                  refine ⟨23795031285513289180749901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31726708380684385574333201 23795031285513289180749901)
                  ·
                    refine ⟨8923136732067483442781213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23795031285513289180749901 8923136732067483442781213)
                    ·
                      refine ⟨3346176274525306291042955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8923136732067483442781213 3346176274525306291042955)
                      ·
                        rfl

theorem cell23_6516655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3, 3].length) (baseStart_6516655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516655 prefixEnd_6516655 := by exact prefixLift 6516655
  have htrace : WordTrace (prefixWord ++ tailWord_6516655) baseStart_6516655 baseEnd_6516655 := by
    simpa [prefixWord, tailWord_6516655, baseEnd_6516655] using wordTrace_append hprefix tailTrace_6516655
  have hstable : (prefixWord ++ tailWord_6516655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516655).length < 2 ^ (prefixWord ++ tailWord_6516655).sum := by decide
  have hdescent : baseEnd_6516655 < baseStart_6516655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516690 : List Nat := [3, 2, 2, 3, 3, 1, 1, 2, 2, 2, 2]
def baseStart_6516690 : Nat := 118140960795 + 6516690 * 2 ^ 59
def prefixEnd_6516690 : Nat := 4983230072969 + 3 ^ 40 * 6516690 * 2
def baseEnd_6516690 : Nat := 3346194246348213654105295

theorem tailTrace_6516690 : CollatzResearch.WordTrace tailWord_6516690 prefixEnd_6516690 3346194246348213654105295 := by
  unfold tailWord_6516690
  simp only [CollatzResearch.WordTrace]
  refine ⟨59420802690288141722418881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158455473840768377926450349 59420802690288141722418881)
  ·
    refine ⟨44565602017716106291814161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59420802690288141722418881 44565602017716106291814161)
    ·
      refine ⟨33424201513287079718860621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44565602017716106291814161 33424201513287079718860621)
      ·
        refine ⟨12534075567482654894572733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33424201513287079718860621 12534075567482654894572733)
        ·
          refine ⟨4700278337805995585464775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12534075567482654894572733 4700278337805995585464775)
          ·
            refine ⟨7050417506708993378197163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4700278337805995585464775 7050417506708993378197163)
            ·
              refine ⟨10575626260063490067295745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7050417506708993378197163 10575626260063490067295745)
              ·
                refine ⟨7931719695047617550471809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10575626260063490067295745 7931719695047617550471809)
                ·
                  refine ⟨5948789771285713162853857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7931719695047617550471809 5948789771285713162853857)
                  ·
                    refine ⟨4461592328464284872140393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5948789771285713162853857 4461592328464284872140393)
                    ·
                      refine ⟨3346194246348213654105295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4461592328464284872140393 3346194246348213654105295)
                      ·
                        rfl

theorem cell23_6516690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_6516690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516690 prefixEnd_6516690 := by exact prefixLift 6516690
  have htrace : WordTrace (prefixWord ++ tailWord_6516690) baseStart_6516690 baseEnd_6516690 := by
    simpa [prefixWord, tailWord_6516690, baseEnd_6516690] using wordTrace_append hprefix tailTrace_6516690
  have hstable : (prefixWord ++ tailWord_6516690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516690).length < 2 ^ (prefixWord ++ tailWord_6516690).sum := by decide
  have hdescent : baseEnd_6516690 < baseStart_6516690 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516695 : List Nat := [1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 4]
def baseStart_6516695 : Nat := 118140960795 + 6516695 * 2 ^ 59
def prefixEnd_6516695 : Nat := 4983230072969 + 3 ^ 40 * 6516695 * 2
def baseEnd_6516695 : Nat := 3346196813751486134542771

theorem tailTrace_6516695 : CollatzResearch.WordTrace tailWord_6516695 prefixEnd_6516695 3346196813751486134542771 := by
  unfold tailWord_6516695
  simp only [CollatzResearch.WordTrace]
  refine ⟨237683393126134452743607539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158455595417422968495738359 237683393126134452743607539)
  ·
    refine ⟨356525089689201679115411309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237683393126134452743607539 356525089689201679115411309)
    ·
      refine ⟨133696908633450629668279241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356525089689201679115411309 133696908633450629668279241)
      ·
        refine ⟨100272681475087972251209431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133696908633450629668279241 100272681475087972251209431)
        ·
          refine ⟨150409022212631958376814147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100272681475087972251209431 150409022212631958376814147)
          ·
            refine ⟨225613533318947937565221221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150409022212631958376814147 225613533318947937565221221)
            ·
              refine ⟨42302537497302738293478979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225613533318947937565221221 42302537497302738293478979)
              ·
                refine ⟨63453806245954107440218469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42302537497302738293478979 63453806245954107440218469)
                ·
                  refine ⟨11897588671116395145040963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63453806245954107440218469 11897588671116395145040963)
                  ·
                    refine ⟨17846383006674592717561445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11897588671116395145040963 17846383006674592717561445)
                    ·
                      refine ⟨3346196813751486134542771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17846383006674592717561445 3346196813751486134542771)
                      ·
                        rfl

theorem cell23_6516695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_6516695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516695 prefixEnd_6516695 := by exact prefixLift 6516695
  have htrace : WordTrace (prefixWord ++ tailWord_6516695) baseStart_6516695 baseEnd_6516695 := by
    simpa [prefixWord, tailWord_6516695, baseEnd_6516695] using wordTrace_append hprefix tailTrace_6516695
  have hstable : (prefixWord ++ tailWord_6516695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516695).length < 2 ^ (prefixWord ++ tailWord_6516695).sum := by decide
  have hdescent : baseEnd_6516695 < baseStart_6516695 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516732 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_6516732 : Nat := 118140960795 + 6516732 * 2 ^ 59
def prefixEnd_6516732 : Nat := 4983230072969 + 3 ^ 40 * 6516732 * 2
def baseEnd_6516732 : Nat := 3346215812535702489780101

theorem tailTrace_6516732 : CollatzResearch.WordTrace tailWord_6516732 prefixEnd_6516732 3346215812535702489780101 := by
  unfold tailWord_6516732
  simp only [CollatzResearch.WordTrace]
  refine ⟨118842371313500204031352225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158456495084666938708469633 118842371313500204031352225)
  ·
    refine ⟨89131778485125153023514169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118842371313500204031352225 89131778485125153023514169)
    ·
      refine ⟨66848833863843864767635627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89131778485125153023514169 66848833863843864767635627)
      ·
        refine ⟨100273250795765797151453441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66848833863843864767635627 100273250795765797151453441)
        ·
          refine ⟨75204938096824347863590081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100273250795765797151453441 75204938096824347863590081)
          ·
            refine ⟨56403703572618260897692561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75204938096824347863590081 56403703572618260897692561)
            ·
              refine ⟨42302777679463695673269421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56403703572618260897692561 42302777679463695673269421)
              ·
                refine ⟨15863541629798885877476033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42302777679463695673269421 15863541629798885877476033)
                ·
                  refine ⟨11897656222349164408107025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15863541629798885877476033 11897656222349164408107025)
                  ·
                    refine ⟨8923242166761873306080269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11897656222349164408107025 8923242166761873306080269)
                    ·
                      refine ⟨3346215812535702489780101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8923242166761873306080269 3346215812535702489780101)
                      ·
                        rfl

theorem cell23_6516732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_6516732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516732 prefixEnd_6516732 := by exact prefixLift 6516732
  have htrace : WordTrace (prefixWord ++ tailWord_6516732) baseStart_6516732 baseEnd_6516732 := by
    simpa [prefixWord, tailWord_6516732, baseEnd_6516732] using wordTrace_append hprefix tailTrace_6516732
  have hstable : (prefixWord ++ tailWord_6516732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516732).length < 2 ^ (prefixWord ++ tailWord_6516732).sum := by decide
  have hdescent : baseEnd_6516732 < baseStart_6516732 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516789 : List Nat := [1, 3, 3, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_6516789 : Nat := 118140960795 + 6516789 * 2 ^ 59
def prefixEnd_6516789 : Nat := 4983230072969 + 3 ^ 40 * 6516789 * 2
def baseEnd_6516789 : Nat := 3346245080933008766767339

theorem tailTrace_6516789 : CollatzResearch.WordTrace tailWord_6516789 prefixEnd_6516789 3346245080933008766767339 := by
  unfold tailWord_6516789
  simp only [CollatzResearch.WordTrace]
  refine ⟨237686821587793906797529421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158457881058529271198352947 237686821587793906797529421)
  ·
    refine ⟨89132558095422715049073533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237686821587793906797529421 89132558095422715049073533)
    ·
      refine ⟨33424709285783518143402575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89132558095422715049073533 33424709285783518143402575)
      ·
        refine ⟨50137063928675277215103863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33424709285783518143402575 50137063928675277215103863)
        ·
          refine ⟨75205595893012915822655795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50137063928675277215103863 75205595893012915822655795)
          ·
            refine ⟨112808393839519373733983693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75205595893012915822655795 112808393839519373733983693)
            ·
              refine ⟨42303147689819765150243885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112808393839519373733983693 42303147689819765150243885)
              ·
                refine ⟨15863680383682411931341457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42303147689819765150243885 15863680383682411931341457)
                ·
                  refine ⟨11897760287761808948506093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15863680383682411931341457 11897760287761808948506093)
                  ·
                    refine ⟨4461660107910678355689785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11897760287761808948506093 4461660107910678355689785)
                    ·
                      refine ⟨3346245080933008766767339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4461660107910678355689785 3346245080933008766767339)
                      ·
                        rfl

theorem cell23_6516789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_6516789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516789 prefixEnd_6516789 := by exact prefixLift 6516789
  have htrace : WordTrace (prefixWord ++ tailWord_6516789) baseStart_6516789 baseEnd_6516789 := by
    simpa [prefixWord, tailWord_6516789, baseEnd_6516789] using wordTrace_append hprefix tailTrace_6516789
  have hstable : (prefixWord ++ tailWord_6516789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516789).length < 2 ^ (prefixWord ++ tailWord_6516789).sum := by decide
  have hdescent : baseEnd_6516789 < baseStart_6516789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516795 : List Nat := [1, 1, 1, 1, 1, 2, 1, 8, 1, 6]
def baseStart_6516795 : Nat := 118140960795 + 6516795 * 2 ^ 59
def prefixEnd_6516795 : Nat := 4983230072969 + 3 ^ 40 * 6516795 * 2
def baseEnd_6516795 : Nat := 1115416053938978581097437

theorem tailTrace_6516795 : CollatzResearch.WordTrace tailWord_6516795 prefixEnd_6516795 1115416053938978581097437 := by
  unfold tailWord_6516795
  simp only [CollatzResearch.WordTrace]
  refine ⟨237687040425772169822247839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158458026950514779881498559 237687040425772169822247839)
  ·
    refine ⟨356530560638658254733371759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237687040425772169822247839 356530560638658254733371759)
    ·
      refine ⟨534795840957987382100057639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356530560638658254733371759 534795840957987382100057639)
      ·
        refine ⟨802193761436981073150086459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534795840957987382100057639 802193761436981073150086459)
        ·
          refine ⟨1203290642155471609725129689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802193761436981073150086459 1203290642155471609725129689)
          ·
            refine ⟨902467981616603707293847267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1203290642155471609725129689 902467981616603707293847267)
            ·
              refine ⟨1353701972424905560940770901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902467981616603707293847267 1353701972424905560940770901)
              ·
                refine ⟨15863694989354362042274659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1353701972424905560940770901 15863694989354362042274659)
                ·
                  refine ⟨23795542484031543063411989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15863694989354362042274659 23795542484031543063411989)
                  ·
                    refine ⟨1115416053938978581097437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23795542484031543063411989 1115416053938978581097437)
                    ·
                      rfl

theorem cell23_6516795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 8, 1, 6].length) (baseStart_6516795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516795 prefixEnd_6516795 := by exact prefixLift 6516795
  have htrace : WordTrace (prefixWord ++ tailWord_6516795) baseStart_6516795 baseEnd_6516795 := by
    simpa [prefixWord, tailWord_6516795, baseEnd_6516795] using wordTrace_append hprefix tailTrace_6516795
  have hstable : (prefixWord ++ tailWord_6516795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516795).length < 2 ^ (prefixWord ++ tailWord_6516795).sum := by decide
  have hdescent : baseEnd_6516795 < baseStart_6516795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516796 : List Nat := [2, 2, 2, 2, 2, 1, 2, 5, 1, 1, 3]
def baseStart_6516796 : Nat := 118140960795 + 6516796 * 2 ^ 59
def prefixEnd_6516796 : Nat := 4983230072969 + 3 ^ 40 * 6516796 * 2
def baseEnd_6516796 : Nat := 3346248675297590239379807

theorem tailTrace_6516796 : CollatzResearch.WordTrace tailWord_6516796 prefixEnd_6516796 3346248675297590239379807 := by
  unfold tailWord_6516796
  simp only [CollatzResearch.WordTrace]
  refine ⟨118843538449384273496517121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158458051265845697995356161 118843538449384273496517121)
  ·
    refine ⟨89132653837038205122387841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118843538449384273496517121 89132653837038205122387841)
    ·
      refine ⟨66849490377778653841790881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89132653837038205122387841 66849490377778653841790881)
      ·
        refine ⟨50137117783333990381343161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66849490377778653841790881 50137117783333990381343161)
        ·
          refine ⟨37602838337500492786007371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50137117783333990381343161 37602838337500492786007371)
          ·
            refine ⟨56404257506250739179011057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37602838337500492786007371 56404257506250739179011057)
            ·
              refine ⟨42303193129688054384258293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56404257506250739179011057 42303193129688054384258293)
              ·
                refine ⟨3965924355908255098524215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42303193129688054384258293 3965924355908255098524215)
                ·
                  refine ⟨5948886533862382647786323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3965924355908255098524215 5948886533862382647786323)
                  ·
                    refine ⟨8923329800793573971679485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5948886533862382647786323 8923329800793573971679485)
                    ·
                      refine ⟨3346248675297590239379807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8923329800793573971679485 3346248675297590239379807)
                      ·
                        rfl

theorem cell23_6516796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_6516796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516796 prefixEnd_6516796 := by exact prefixLift 6516796
  have htrace : WordTrace (prefixWord ++ tailWord_6516796) baseStart_6516796 baseEnd_6516796 := by
    simpa [prefixWord, tailWord_6516796, baseEnd_6516796] using wordTrace_append hprefix tailTrace_6516796
  have hstable : (prefixWord ++ tailWord_6516796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516796).length < 2 ^ (prefixWord ++ tailWord_6516796).sum := by decide
  have hdescent : baseEnd_6516796 < baseStart_6516796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516812 : List Nat := [2, 2, 1, 3, 1, 1, 2, 3, 4, 4]
def baseStart_6516812 : Nat := 118140960795 + 6516812 * 2 ^ 59
def prefixEnd_6516812 : Nat := 4983230072969 + 3 ^ 40 * 6516812 * 2
def baseEnd_6516812 : Nat := 1115418963662687392259911

theorem tailTrace_6516812 : CollatzResearch.WordTrace tailWord_6516812 prefixEnd_6516812 1115418963662687392259911 := by
  unfold tailWord_6516812
  simp only [CollatzResearch.WordTrace]
  refine ⟨118843830233355290862808345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158458440311140387817077793 118843830233355290862808345)
  ·
    refine ⟨89132872675016468147106259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118843830233355290862808345 89132872675016468147106259)
    ·
      refine ⟨133699309012524702220659389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89132872675016468147106259 133699309012524702220659389)
      ·
        refine ⟨50137240879696763332747271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133699309012524702220659389 50137240879696763332747271)
        ·
          refine ⟨75205861319545144999120907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50137240879696763332747271 75205861319545144999120907)
          ·
            refine ⟨112808791979317717498681361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75205861319545144999120907 112808791979317717498681361)
            ·
              refine ⟨84606593984488288124011021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112808791979317717498681361 84606593984488288124011021)
              ·
                refine ⟨31727472744183108046504133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84606593984488288124011021 31727472744183108046504133)
                ·
                  refine ⟨5948901139534332758719525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31727472744183108046504133 5948901139534332758719525)
                  ·
                    refine ⟨1115418963662687392259911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5948901139534332758719525 1115418963662687392259911)
                    ·
                      rfl

theorem cell23_6516812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_6516812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516812 prefixEnd_6516812 := by exact prefixLift 6516812
  have htrace : WordTrace (prefixWord ++ tailWord_6516812) baseStart_6516812 baseEnd_6516812 := by
    simpa [prefixWord, tailWord_6516812, baseEnd_6516812] using wordTrace_append hprefix tailTrace_6516812
  have hstable : (prefixWord ++ tailWord_6516812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516812).length < 2 ^ (prefixWord ++ tailWord_6516812).sum := by decide
  have hdescent : baseEnd_6516812 < baseStart_6516812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516813 : List Nat := [1, 6, 1, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_6516813 : Nat := 118140960795 + 6516813 * 2 ^ 59
def prefixEnd_6516813 : Nat := 4983230072969 + 3 ^ 40 * 6516813 * 2
def baseEnd_6516813 : Nat := 3346257404468716672867229

theorem tailTrace_6516813 : CollatzResearch.WordTrace tailWord_6516813 prefixEnd_6516813 3346257404468716672867229 := by
  unfold tailWord_6516813
  simp only [CollatzResearch.WordTrace]
  refine ⟨237687696939706958896403093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158458464626471305930935395 237687696939706958896403093)
  ·
    refine ⟨11141610794048763698268895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 237687696939706958896403093 11141610794048763698268895)
    ·
      refine ⟨16712416191073145547403343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11141610794048763698268895 16712416191073145547403343)
      ·
        refine ⟨25068624286609718321105015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16712416191073145547403343 25068624286609718321105015)
        ·
          refine ⟨37602936429914577481657523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25068624286609718321105015 37602936429914577481657523)
          ·
            refine ⟨56404404644871866222486285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37602936429914577481657523 56404404644871866222486285)
            ·
              refine ⟨21151651741826949833432357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56404404644871866222486285 21151651741826949833432357)
              ·
                refine ⟨3965934701592553093768567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21151651741826949833432357 3965934701592553093768567)
                ·
                  refine ⟨5948902052388829640652851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3965934701592553093768567 5948902052388829640652851)
                  ·
                    refine ⟨8923353078583244460979277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5948902052388829640652851 8923353078583244460979277)
                    ·
                      refine ⟨3346257404468716672867229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8923353078583244460979277 3346257404468716672867229)
                      ·
                        rfl

theorem cell23_6516813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_6516813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516813 prefixEnd_6516813 := by exact prefixLift 6516813
  have htrace : WordTrace (prefixWord ++ tailWord_6516813) baseStart_6516813 baseEnd_6516813 := by
    simpa [prefixWord, tailWord_6516813, baseEnd_6516813] using wordTrace_append hprefix tailTrace_6516813
  have hstable : (prefixWord ++ tailWord_6516813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516813).length < 2 ^ (prefixWord ++ tailWord_6516813).sum := by decide
  have hdescent : baseEnd_6516813 < baseStart_6516813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516829 : List Nat := [1, 4, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_6516829 : Nat := 118140960795 + 6516829 * 2 ^ 59
def prefixEnd_6516829 : Nat := 4983230072969 + 3 ^ 40 * 6516829 * 2
def baseEnd_6516829 : Nat := 1115421873386396203422385

theorem tailTrace_6516829 : CollatzResearch.WordTrace tailWord_6516829 prefixEnd_6516829 1115421873386396203422385 := by
  unfold tailWord_6516829
  simp only [CollatzResearch.WordTrace]
  refine ⟨237688280507648993628985541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158458853671765995752657027 237688280507648993628985541)
  ·
    refine ⟨44566552595184186305434789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237688280507648993628985541 44566552595184186305434789)
    ·
      refine ⟨8356228611597034932269023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44566552595184186305434789 8356228611597034932269023)
      ·
        refine ⟨12534342917395552398403535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8356228611597034932269023 12534342917395552398403535)
        ·
          refine ⟨18801514376093328597605303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12534342917395552398403535 18801514376093328597605303)
          ·
            refine ⟨28202271564139992896407955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18801514376093328597605303 28202271564139992896407955)
            ·
              refine ⟨42303407346209989344611933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28202271564139992896407955 42303407346209989344611933)
              ·
                refine ⟨15863777754828746004229475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42303407346209989344611933 15863777754828746004229475)
                ·
                  refine ⟨23795666632243119006344213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15863777754828746004229475 23795666632243119006344213)
                  ·
                    refine ⟨1115421873386396203422385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23795666632243119006344213 1115421873386396203422385)
                    ·
                      rfl

theorem cell23_6516829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_6516829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516829 prefixEnd_6516829 := by exact prefixLift 6516829
  have htrace : WordTrace (prefixWord ++ tailWord_6516829) baseStart_6516829 baseEnd_6516829 := by
    simpa [prefixWord, tailWord_6516829, baseEnd_6516829] using wordTrace_append hprefix tailTrace_6516829
  have hstable : (prefixWord ++ tailWord_6516829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516829).length < 2 ^ (prefixWord ++ tailWord_6516829).sum := by decide
  have hdescent : baseEnd_6516829 < baseStart_6516829 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516830 : List Nat := [4, 4, 1, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_6516830 : Nat := 118140960795 + 6516830 * 2 ^ 59
def prefixEnd_6516830 : Nat := 4983230072969 + 3 ^ 40 * 6516830 * 2
def baseEnd_6516830 : Nat := 3346266133639843106354651

theorem tailTrace_6516830 : CollatzResearch.WordTrace tailWord_6516830 prefixEnd_6516830 3346266133639843106354651 := by
  unfold tailWord_6516830
  simp only [CollatzResearch.WordTrace]
  refine ⟨29711039622580671349971493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158458877987096913866514629 29711039622580671349971493)
  ·
    refine ⟨5570819929233875878119655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29711039622580671349971493 5570819929233875878119655)
    ·
      refine ⟨8356229893850813817179483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5570819929233875878119655 8356229893850813817179483)
      ·
        refine ⟨12534344840776220725769225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8356229893850813817179483 12534344840776220725769225)
        ·
          refine ⟨9400758630582165544326919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12534344840776220725769225 9400758630582165544326919)
          ·
            refine ⟨14101137945873248316490379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9400758630582165544326919 14101137945873248316490379)
            ·
              refine ⟨21151706918809872474735569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14101137945873248316490379 21151706918809872474735569)
              ·
                refine ⟨15863780189107404356051677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21151706918809872474735569 15863780189107404356051677)
                ·
                  refine ⟨5948917570915276633519379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15863780189107404356051677 5948917570915276633519379)
                  ·
                    refine ⟨8923376356372914950279069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5948917570915276633519379 8923376356372914950279069)
                    ·
                      refine ⟨3346266133639843106354651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8923376356372914950279069 3346266133639843106354651)
                      ·
                        rfl

theorem cell23_6516830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_6516830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516830 prefixEnd_6516830 := by exact prefixLift 6516830
  have htrace : WordTrace (prefixWord ++ tailWord_6516830) baseStart_6516830 baseEnd_6516830 := by
    simpa [prefixWord, tailWord_6516830, baseEnd_6516830] using wordTrace_append hprefix tailTrace_6516830
  have hstable : (prefixWord ++ tailWord_6516830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516830).length < 2 ^ (prefixWord ++ tailWord_6516830).sum := by decide
  have hdescent : baseEnd_6516830 < baseStart_6516830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516832 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 4]
def baseStart_6516832 : Nat := 118140960795 + 6516832 * 2 ^ 59
def prefixEnd_6516832 : Nat := 4983230072969 + 3 ^ 40 * 6516832 * 2
def baseEnd_6516832 : Nat := 3346267160601152098529641

theorem tailTrace_6516832 : CollatzResearch.WordTrace tailWord_6516832 prefixEnd_6516832 3346267160601152098529641 := by
  unfold tailWord_6516832
  simp only [CollatzResearch.WordTrace]
  refine ⟨118844194963319062570672375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158458926617758750094229833 118844194963319062570672375)
  ·
    refine ⟨178266292444978593856008563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118844194963319062570672375 178266292444978593856008563)
    ·
      refine ⟨267399438667467890784012845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178266292444978593856008563 267399438667467890784012845)
      ·
        refine ⟨100274789500300459044004817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267399438667467890784012845 100274789500300459044004817)
        ·
          refine ⟨75206092125225344283003613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100274789500300459044004817 75206092125225344283003613)
          ·
            refine ⟨28202284546959504106126355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75206092125225344283003613 28202284546959504106126355)
            ·
              refine ⟨42303426820439256159189533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28202284546959504106126355 42303426820439256159189533)
              ·
                refine ⟨15863785057664721059696075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42303426820439256159189533 15863785057664721059696075)
                ·
                  refine ⟨23795677586497081589544113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15863785057664721059696075 23795677586497081589544113)
                  ·
                    refine ⟨17846758189872811192158085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23795677586497081589544113 17846758189872811192158085)
                    ·
                      refine ⟨3346267160601152098529641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17846758189872811192158085 3346267160601152098529641)
                      ·
                        rfl

theorem cell23_6516832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_6516832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516832 prefixEnd_6516832 := by exact prefixLift 6516832
  have htrace : WordTrace (prefixWord ++ tailWord_6516832) baseStart_6516832 baseEnd_6516832 := by
    simpa [prefixWord, tailWord_6516832, baseEnd_6516832] using wordTrace_append hprefix tailTrace_6516832
  have hstable : (prefixWord ++ tailWord_6516832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516832).length < 2 ^ (prefixWord ++ tailWord_6516832).sum := by decide
  have hdescent : baseEnd_6516832 < baseStart_6516832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516839 : List Nat := [1, 1, 5, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_6516839 : Nat := 118140960795 + 6516839 * 2 ^ 59
def prefixEnd_6516839 : Nat := 4983230072969 + 3 ^ 40 * 6516839 * 2
def baseEnd_6516839 : Nat := 3346270754965733571142109

theorem tailTrace_6516839 : CollatzResearch.WordTrace tailWord_6516839 prefixEnd_6516839 3346270754965733571142109 := by
  unfold tailWord_6516839
  simp only [CollatzResearch.WordTrace]
  refine ⟨237688645237612765336849571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158459096825075176891233047 237688645237612765336849571)
  ·
    refine ⟨356532967856419148005274357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237688645237612765336849571 356532967856419148005274357)
    ·
      refine ⟨33424965736539295125494471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 356532967856419148005274357 33424965736539295125494471)
      ·
        refine ⟨50137448604808942688241707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33424965736539295125494471 50137448604808942688241707)
        ·
          refine ⟨75206172907213414032362561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50137448604808942688241707 75206172907213414032362561)
          ·
            refine ⟨56404629680410060524271921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75206172907213414032362561 56404629680410060524271921)
            ·
              refine ⟨42303472260307545393203941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56404629680410060524271921 42303472260307545393203941)
              ·
                refine ⟨7931901048807664761225739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42303472260307545393203941 7931901048807664761225739)
                ·
                  refine ⟨11897851573211497141838609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7931901048807664761225739 11897851573211497141838609)
                  ·
                    refine ⟨8923388679908622856378957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11897851573211497141838609 8923388679908622856378957)
                    ·
                      refine ⟨3346270754965733571142109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8923388679908622856378957 3346270754965733571142109)
                      ·
                        rfl

theorem cell23_6516839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_6516839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516839 prefixEnd_6516839 := by exact prefixLift 6516839
  have htrace : WordTrace (prefixWord ++ tailWord_6516839) baseStart_6516839 baseEnd_6516839 := by
    simpa [prefixWord, tailWord_6516839, baseEnd_6516839] using wordTrace_append hprefix tailTrace_6516839
  have hstable : (prefixWord ++ tailWord_6516839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516839).length < 2 ^ (prefixWord ++ tailWord_6516839).sum := by decide
  have hdescent : baseEnd_6516839 < baseStart_6516839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516896 : List Nat := [2, 1, 1, 4, 2, 2, 1, 4, 1, 3, 2]
def baseStart_6516896 : Nat := 118140960795 + 6516896 * 2 ^ 59
def prefixEnd_6516896 : Nat := 4983230072969 + 3 ^ 40 * 6516896 * 2
def baseEnd_6516896 : Nat := 3346300023363039848129347

theorem tailTrace_6516896 : CollatzResearch.WordTrace tailWord_6516896 prefixEnd_6516896 3346300023363039848129347 := by
  unfold tailWord_6516896
  simp only [CollatzResearch.WordTrace]
  refine ⟨118845362099203132035837271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158460482798937509381116361 118845362099203132035837271)
  ·
    refine ⟨178268043148804698053755907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118845362099203132035837271 178268043148804698053755907)
    ·
      refine ⟨267402064723207047080633861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178268043148804698053755907 267402064723207047080633861)
      ·
        refine ⟨50137887135601321327618849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267402064723207047080633861 50137887135601321327618849)
        ·
          refine ⟨37603415351700990995714137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50137887135601321327618849 37603415351700990995714137)
          ·
            refine ⟨28202561513775743246785603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37603415351700990995714137 28202561513775743246785603)
            ·
              refine ⟨42303842270663614870178405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28202561513775743246785603 42303842270663614870178405)
              ·
                refine ⟨7931970425749427788158451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42303842270663614870178405 7931970425749427788158451)
                ·
                  refine ⟨11897955638624141682237677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7931970425749427788158451 11897955638624141682237677)
                  ·
                    refine ⟨4461733364484053130839129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11897955638624141682237677 4461733364484053130839129)
                    ·
                      refine ⟨3346300023363039848129347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4461733364484053130839129 3346300023363039848129347)
                      ·
                        rfl

theorem cell23_6516896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_6516896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516896 prefixEnd_6516896 := by exact prefixLift 6516896
  have htrace : WordTrace (prefixWord ++ tailWord_6516896) baseStart_6516896 baseEnd_6516896 := by
    simpa [prefixWord, tailWord_6516896, baseEnd_6516896] using wordTrace_append hprefix tailTrace_6516896
  have hstable : (prefixWord ++ tailWord_6516896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516896).length < 2 ^ (prefixWord ++ tailWord_6516896).sum := by decide
  have hdescent : baseEnd_6516896 < baseStart_6516896 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516922 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4]
def baseStart_6516922 : Nat := 118140960795 + 6516922 * 2 ^ 59
def prefixEnd_6516922 : Nat := 4983230072969 + 3 ^ 40 * 6516922 * 2
def baseEnd_6516922 : Nat := 3346313373860056746404227

theorem tailTrace_6516922 : CollatzResearch.WordTrace tailWord_6516922 prefixEnd_6516922 3346313373860056746404227 := by
  unfold tailWord_6516922
  simp only [CollatzResearch.WordTrace]
  refine ⟨59422918124078017628030255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158461114997541380341414013 59422918124078017628030255)
  ·
    refine ⟨89134377186117026442045383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59422918124078017628030255 89134377186117026442045383)
    ·
      refine ⟨133701565779175539663068075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89134377186117026442045383 133701565779175539663068075)
      ·
        refine ⟨200552348668763309494602113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133701565779175539663068075 200552348668763309494602113)
        ·
          refine ⟨150414261501572482120951585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200552348668763309494602113 150414261501572482120951585)
          ·
            refine ⟨112810696126179361590713689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150414261501572482120951585 112810696126179361590713689)
            ·
              refine ⟨84608022094634521193035267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112810696126179361590713689 84608022094634521193035267)
              ·
                refine ⟨126912033141951781789552901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84608022094634521193035267 126912033141951781789552901)
                ·
                  refine ⟨23796006214115959085541169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126912033141951781789552901 23796006214115959085541169)
                  ·
                    refine ⟨17847004660586969314155877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23796006214115959085541169 17847004660586969314155877)
                    ·
                      refine ⟨3346313373860056746404227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17847004660586969314155877 3346313373860056746404227)
                      ·
                        rfl

theorem cell23_6516922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 4, 2, 4].length) (baseStart_6516922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516922 prefixEnd_6516922 := by exact prefixLift 6516922
  have htrace : WordTrace (prefixWord ++ tailWord_6516922) baseStart_6516922 baseEnd_6516922 := by
    simpa [prefixWord, tailWord_6516922, baseEnd_6516922] using wordTrace_append hprefix tailTrace_6516922
  have hstable : (prefixWord ++ tailWord_6516922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516922).length < 2 ^ (prefixWord ++ tailWord_6516922).sum := by decide
  have hdescent : baseEnd_6516922 < baseStart_6516922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6516972 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_6516972 : Nat := 118140960795 + 6516972 * 2 ^ 59
def prefixEnd_6516972 : Nat := 4983230072969 + 3 ^ 40 * 6516972 * 2
def baseEnd_6516972 : Nat := 3346339047892781550778997

theorem tailTrace_6516972 : CollatzResearch.WordTrace tailWord_6516972 prefixEnd_6516972 3346339047892781550778997 := by
  unfold tailWord_6516972
  simp only [CollatzResearch.WordTrace]
  refine ⟨118846748073065464525720585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158462330764087286034294113 118846748073065464525720585)
  ·
    refine ⟨89135061054799098394290439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118846748073065464525720585 89135061054799098394290439)
    ·
      refine ⟨133702591582198647591435659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89135061054799098394290439 133702591582198647591435659)
      ·
        refine ⟨200553887373297971387153489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133702591582198647591435659 200553887373297971387153489)
        ·
          refine ⟨150415415529973478540365117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200553887373297971387153489 150415415529973478540365117)
          ·
            refine ⟨56405780823740054452636919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150415415529973478540365117 56405780823740054452636919)
            ·
              refine ⟨84608671235610081678955379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56405780823740054452636919 84608671235610081678955379)
              ·
                refine ⟨126913006853415122518433069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84608671235610081678955379 126913006853415122518433069)
                ·
                  refine ⟨47592377570030670944412401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126913006853415122518433069 47592377570030670944412401)
                  ·
                    refine ⟨35694283177523003208309301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 47592377570030670944412401 35694283177523003208309301)
                    ·
                      refine ⟨3346339047892781550778997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35694283177523003208309301 3346339047892781550778997)
                      ·
                        rfl

theorem cell23_6516972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_6516972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6516972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6516972 prefixEnd_6516972 := by exact prefixLift 6516972
  have htrace : WordTrace (prefixWord ++ tailWord_6516972) baseStart_6516972 baseEnd_6516972 := by
    simpa [prefixWord, tailWord_6516972, baseEnd_6516972] using wordTrace_append hprefix tailTrace_6516972
  have hstable : (prefixWord ++ tailWord_6516972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6516972).length < 2 ^ (prefixWord ++ tailWord_6516972).sum := by decide
  have hdescent : baseEnd_6516972 < baseStart_6516972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6516972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517009 : List Nat := [1, 2, 2, 1, 1, 5, 1, 1, 5, 4]
def baseStart_6517009 : Nat := 118140960795 + 6517009 * 2 ^ 59
def prefixEnd_6517009 : Nat := 4983230072969 + 3 ^ 40 * 6517009 * 2
def baseEnd_6517009 : Nat := 1115452682225665968672109

theorem tailTrace_6517009 : CollatzResearch.WordTrace tailWord_6517009 prefixEnd_6517009 1115452682225665968672109 := by
  unfold tailWord_6517009
  simp only [CollatzResearch.WordTrace]
  refine ⟨237694845646996884370538081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158463230431331256247025387 237694845646996884370538081)
  ·
    refine ⟨178271134235247663277903561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237694845646996884370538081 178271134235247663277903561)
    ·
      refine ⟨133703350676435747458427671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178271134235247663277903561 133703350676435747458427671)
      ·
        refine ⟨200555026014653621187641507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133703350676435747458427671 200555026014653621187641507)
        ·
          refine ⟨300832539021980431781462261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200555026014653621187641507 300832539021980431781462261)
          ·
            refine ⟨28203050533310665479512087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 300832539021980431781462261 28203050533310665479512087)
            ·
              refine ⟨42304575799965998219268131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28203050533310665479512087 42304575799965998219268131)
              ·
                refine ⟨63456863699948997328902197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42304575799965998219268131 63456863699948997328902197)
                ·
                  refine ⟨5949080971870218499584581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63456863699948997328902197 5949080971870218499584581)
                  ·
                    refine ⟨1115452682225665968672109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5949080971870218499584581 1115452682225665968672109)
                    ·
                      rfl

theorem cell23_6517009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 1, 5, 4].length) (baseStart_6517009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517009 prefixEnd_6517009 := by exact prefixLift 6517009
  have htrace : WordTrace (prefixWord ++ tailWord_6517009) baseStart_6517009 baseEnd_6517009 := by
    simpa [prefixWord, tailWord_6517009, baseEnd_6517009] using wordTrace_append hprefix tailTrace_6517009
  have hstable : (prefixWord ++ tailWord_6517009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517009).length < 2 ^ (prefixWord ++ tailWord_6517009).sum := by decide
  have hdescent : baseEnd_6517009 < baseStart_6517009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517039 : List Nat := [1, 1, 2, 1, 2, 1, 7, 2, 6]
def baseStart_6517039 : Nat := 118140960795 + 6517039 * 2 ^ 59
def prefixEnd_6517039 : Nat := 4983230072969 + 3 ^ 40 * 6517039 * 2
def baseEnd_6517039 : Nat := 371819272344070309849021

theorem tailTrace_6517039 : CollatzResearch.WordTrace tailWord_6517039 prefixEnd_6517039 371819272344070309849021 := by
  unfold tailWord_6517039
  simp only [CollatzResearch.WordTrace]
  refine ⟨237695939836888199494130171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158463959891258799662753447 237695939836888199494130171)
  ·
    refine ⟨356543909755332299241195257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237695939836888199494130171 356543909755332299241195257)
    ·
      refine ⟨267407932316499224430896443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356543909755332299241195257 267407932316499224430896443)
      ·
        refine ⟨401111898474748836646344665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267407932316499224430896443 401111898474748836646344665)
        ·
          refine ⟨300833923856061627484758499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401111898474748836646344665 300833923856061627484758499)
          ·
            refine ⟨451250885784092441227137749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300833923856061627484758499 451250885784092441227137749)
            ·
              refine ⟨10576192635564666591261041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 451250885784092441227137749 10576192635564666591261041)
              ·
                refine ⟨7932144476673499943445781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10576192635564666591261041 7932144476673499943445781)
                ·
                  refine ⟨371819272344070309849021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7932144476673499943445781 371819272344070309849021)
                  ·
                    rfl

theorem cell23_6517039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 6].length) (baseStart_6517039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517039 prefixEnd_6517039 := by exact prefixLift 6517039
  have htrace : WordTrace (prefixWord ++ tailWord_6517039) baseStart_6517039 baseEnd_6517039 := by
    simpa [prefixWord, tailWord_6517039, baseEnd_6517039] using wordTrace_append hprefix tailTrace_6517039
  have hstable : (prefixWord ++ tailWord_6517039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517039).length < 2 ^ (prefixWord ++ tailWord_6517039).sum := by decide
  have hdescent : baseEnd_6517039 < baseStart_6517039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517077 : List Nat := [1, 3, 2, 2, 5, 1, 1, 3, 1, 4]
def baseStart_6517077 : Nat := 118140960795 + 6517077 * 2 ^ 59
def prefixEnd_6517077 : Nat := 4983230072969 + 3 ^ 40 * 6517077 * 2
def baseEnd_6517077 : Nat := 1115464321120501213322005

theorem tailTrace_6517077 : CollatzResearch.WordTrace tailWord_6517077 prefixEnd_6517077 1115464321120501213322005 := by
  unfold tailWord_6517077
  simp only [CollatzResearch.WordTrace]
  refine ⟨237697325810750531984013485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158464883873833687989342323 237697325810750531984013485)
  ·
    refine ⟨89136497179031449494005057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237697325810750531984013485 89136497179031449494005057)
    ·
      refine ⟨66852372884273587120503793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89136497179031449494005057 66852372884273587120503793)
      ·
        refine ⟨50139279663205190340377845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66852372884273587120503793 50139279663205190340377845)
        ·
          refine ⟨4700557468425486594410423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50139279663205190340377845 4700557468425486594410423)
          ·
            refine ⟨7050836202638229891615635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4700557468425486594410423 7050836202638229891615635)
            ·
              refine ⟨10576254303957344837423453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7050836202638229891615635 10576254303957344837423453)
              ·
                refine ⟨3966095363984004314033795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10576254303957344837423453 3966095363984004314033795)
                ·
                  refine ⟨5949143045976006471050693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966095363984004314033795 5949143045976006471050693)
                  ·
                    refine ⟨1115464321120501213322005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5949143045976006471050693 1115464321120501213322005)
                    ·
                      rfl

theorem cell23_6517077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_6517077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517077 prefixEnd_6517077 := by exact prefixLift 6517077
  have htrace : WordTrace (prefixWord ++ tailWord_6517077) baseStart_6517077 baseEnd_6517077 := by
    simpa [prefixWord, tailWord_6517077, baseEnd_6517077] using wordTrace_append hprefix tailTrace_6517077
  have hstable : (prefixWord ++ tailWord_6517077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517077).length < 2 ^ (prefixWord ++ tailWord_6517077).sum := by decide
  have hdescent : baseEnd_6517077 < baseStart_6517077 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517089 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 7, 1, 4]
def baseStart_6517089 : Nat := 118140960795 + 6517089 * 2 ^ 59
def prefixEnd_6517089 : Nat := 4983230072969 + 3 ^ 40 * 6517089 * 2
def baseEnd_6517089 : Nat := 3346399125129357593015959

theorem tailTrace_6517089 : CollatzResearch.WordTrace tailWord_6517089 prefixEnd_6517089 3346399125129357593015959 := by
  unfold tailWord_6517089
  simp only [CollatzResearch.WordTrace]
  refine ⟨237697763486707058033450321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158465175657804705355633547 237697763486707058033450321)
  ·
    refine ⟨178273322615030293525087741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237697763486707058033450321 178273322615030293525087741)
    ·
      refine ⟨66852495980636360071907903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178273322615030293525087741 66852495980636360071907903)
      ·
        refine ⟨100278743970954540107861855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66852495980636360071907903 100278743970954540107861855)
        ·
          refine ⟨150418115956431810161792783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100278743970954540107861855 150418115956431810161792783)
          ·
            refine ⟨225627173934647715242689175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150418115956431810161792783 225627173934647715242689175)
            ·
              refine ⟨338440760901971572864033763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225627173934647715242689175 338440760901971572864033763)
              ·
                refine ⟨507661141352957359296050645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338440760901971572864033763 507661141352957359296050645)
                ·
                  refine ⟨11898308000459938108501187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 507661141352957359296050645 11898308000459938108501187)
                  ·
                    refine ⟨17847462000689907162751781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11898308000459938108501187 17847462000689907162751781)
                    ·
                      refine ⟨3346399125129357593015959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17847462000689907162751781 3346399125129357593015959)
                      ·
                        rfl

theorem cell23_6517089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_6517089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517089 prefixEnd_6517089 := by exact prefixLift 6517089
  have htrace : WordTrace (prefixWord ++ tailWord_6517089) baseStart_6517089 baseEnd_6517089 := by
    simpa [prefixWord, tailWord_6517089, baseEnd_6517089] using wordTrace_append hprefix tailTrace_6517089
  have hstable : (prefixWord ++ tailWord_6517089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517089).length < 2 ^ (prefixWord ++ tailWord_6517089).sum := by decide
  have hdescent : baseEnd_6517089 < baseStart_6517089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517093 : List Nat := [1, 3, 1, 3, 1, 4, 1, 2, 2, 3, 2]
def baseStart_6517093 : Nat := 118140960795 + 6517093 * 2 ^ 59
def prefixEnd_6517093 : Nat := 4983230072969 + 3 ^ 40 * 6517093 * 2
def baseEnd_6517093 : Nat := 3346401179051975577365941

theorem tailTrace_6517093 : CollatzResearch.WordTrace tailWord_6517093 prefixEnd_6517093 3346401179051975577365941 := by
  unfold tailWord_6517093
  simp only [CollatzResearch.WordTrace]
  refine ⟨237697909378692566716595933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158465272919128377811063955 237697909378692566716595933)
  ·
    refine ⟨89136716017009712518723475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237697909378692566716595933 89136716017009712518723475)
    ·
      refine ⟨133705074025514568778085213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89136716017009712518723475 133705074025514568778085213)
      ·
        refine ⟨50139402759567963291781955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133705074025514568778085213 50139402759567963291781955)
        ·
          refine ⟨75209104139351944937672933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50139402759567963291781955 75209104139351944937672933)
          ·
            refine ⟨14101707026128489675813675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75209104139351944937672933 14101707026128489675813675)
            ·
              refine ⟨21152560539192734513720513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14101707026128489675813675 21152560539192734513720513)
              ·
                refine ⟨15864420404394550885290385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21152560539192734513720513 15864420404394550885290385)
                ·
                  refine ⟨11898315303295913163967789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15864420404394550885290385 11898315303295913163967789)
                  ·
                    refine ⟨4461868238735967436487921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11898315303295913163967789 4461868238735967436487921)
                    ·
                      refine ⟨3346401179051975577365941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4461868238735967436487921 3346401179051975577365941)
                      ·
                        rfl

theorem cell23_6517093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_6517093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517093 prefixEnd_6517093 := by exact prefixLift 6517093
  have htrace : WordTrace (prefixWord ++ tailWord_6517093) baseStart_6517093 baseEnd_6517093 := by
    simpa [prefixWord, tailWord_6517093, baseEnd_6517093] using wordTrace_append hprefix tailTrace_6517093
  have hstable : (prefixWord ++ tailWord_6517093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517093).length < 2 ^ (prefixWord ++ tailWord_6517093).sum := by decide
  have hdescent : baseEnd_6517093 < baseStart_6517093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517100 : List Nat := [2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 3]
def baseStart_6517100 : Nat := 118140960795 + 6517100 * 2 ^ 59
def prefixEnd_6517100 : Nat := 4983230072969 + 3 ^ 40 * 6517100 * 2
def baseEnd_6517100 : Nat := 3346404773416557049978409

theorem tailTrace_6517100 : CollatzResearch.WordTrace tailWord_6517100 prefixEnd_6517100 3346404773416557049978409 := by
  unfold tailWord_6517100
  simp only [CollatzResearch.WordTrace]
  refine ⟨118849082344833603456050377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158465443126444804608067169 118849082344833603456050377)
  ·
    refine ⟨89136811758625202592037783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118849082344833603456050377 89136811758625202592037783)
    ·
      refine ⟨133705217637937803888056675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89136811758625202592037783 133705217637937803888056675)
      ·
        refine ⟨200557826456906705832085013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133705217637937803888056675 200557826456906705832085013)
        ·
          refine ⟨9401148115167501835878985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 200557826456906705832085013 9401148115167501835878985)
          ·
            refine ⟨7050861086375626376909239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9401148115167501835878985 7050861086375626376909239)
            ·
              refine ⟨10576291629563439565363859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7050861086375626376909239 10576291629563439565363859)
              ·
                refine ⟨15864437444345159348045789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10576291629563439565363859 15864437444345159348045789)
                ·
                  refine ⟨5949164041629434755517171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15864437444345159348045789 5949164041629434755517171)
                  ·
                    refine ⟨8923746062444152133275757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5949164041629434755517171 8923746062444152133275757)
                    ·
                      refine ⟨3346404773416557049978409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8923746062444152133275757 3346404773416557049978409)
                      ·
                        rfl

theorem cell23_6517100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_6517100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517100 prefixEnd_6517100 := by exact prefixLift 6517100
  have htrace : WordTrace (prefixWord ++ tailWord_6517100) baseStart_6517100 baseEnd_6517100 := by
    simpa [prefixWord, tailWord_6517100, baseEnd_6517100] using wordTrace_append hprefix tailTrace_6517100
  have hstable : (prefixWord ++ tailWord_6517100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517100).length < 2 ^ (prefixWord ++ tailWord_6517100).sum := by decide
  have hdescent : baseEnd_6517100 < baseStart_6517100 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517129 : List Nat := [1, 2, 1, 1, 6, 1, 2, 9]
def baseStart_6517129 : Nat := 118140960795 + 6517129 * 2 ^ 59
def prefixEnd_6517129 : Nat := 4983230072969 + 3 ^ 40 * 6517129 * 2
def baseEnd_6517129 : Nat := 123941469050205090241325

theorem tailTrace_6517129 : CollatzResearch.WordTrace tailWord_6517129 prefixEnd_6517129 123941469050205090241325 := by
  unfold tailWord_6517129
  simp only [CollatzResearch.WordTrace]
  refine ⟨237699222406562144864906441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158466148271041429909937627 237699222406562144864906441)
  ·
    refine ⟨178274416804921608648679831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237699222406562144864906441 178274416804921608648679831)
    ·
      refine ⟨267411625207382412973019747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178274416804921608648679831 267411625207382412973019747)
      ·
        refine ⟨401117437811073619459529621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267411625207382412973019747 401117437811073619459529621)
        ·
          refine ⟨18802379897394075912165451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 401117437811073619459529621 18802379897394075912165451)
          ·
            refine ⟨28203569846091113868248177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18802379897394075912165451 28203569846091113868248177)
            ·
              refine ⟨21152677384568335401186133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28203569846091113868248177 21152677384568335401186133)
              ·
                refine ⟨123941469050205090241325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21152677384568335401186133 123941469050205090241325)
                ·
                  rfl

theorem cell23_6517129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 9].length) (baseStart_6517129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517129 prefixEnd_6517129 := by exact prefixLift 6517129
  have htrace : WordTrace (prefixWord ++ tailWord_6517129) baseStart_6517129 baseEnd_6517129 := by
    simpa [prefixWord, tailWord_6517129, baseEnd_6517129] using wordTrace_append hprefix tailTrace_6517129
  have hstable : (prefixWord ++ tailWord_6517129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517129).length < 2 ^ (prefixWord ++ tailWord_6517129).sum := by decide
  have hdescent : baseEnd_6517129 < baseStart_6517129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517150 : List Nat := [4, 3, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_6517150 : Nat := 118140960795 + 6517150 * 2 ^ 59
def prefixEnd_6517150 : Nat := 4983230072969 + 3 ^ 40 * 6517150 * 2
def baseEnd_6517150 : Nat := 1115476815816427284784393

theorem tailTrace_6517150 : CollatzResearch.WordTrace tailWord_6517150 prefixEnd_6517150 1115476815816427284784393 := by
  unfold tailWord_6517150
  simp only [CollatzResearch.WordTrace]
  refine ⟨29712498542435758181427613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158466658892990710300947269 29712498542435758181427613)
  ·
    refine ⟨11142186953413409318035355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29712498542435758181427613 11142186953413409318035355)
    ·
      refine ⟨16713280430120113977053033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11142186953413409318035355 16713280430120113977053033)
      ·
        refine ⟨12534960322590085482789775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16713280430120113977053033 12534960322590085482789775)
        ·
          refine ⟨18802440483885128224184663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12534960322590085482789775 18802440483885128224184663)
          ·
            refine ⟨28203660725827692336276995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18802440483885128224184663 28203660725827692336276995)
            ·
              refine ⟨42305491088741538504415493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28203660725827692336276995 42305491088741538504415493)
              ·
                refine ⟨7932279579139038469577905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42305491088741538504415493 7932279579139038469577905)
                ·
                  refine ⟨5949209684354278852183429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7932279579139038469577905 5949209684354278852183429)
                  ·
                    refine ⟨1115476815816427284784393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5949209684354278852183429 1115476815816427284784393)
                    ·
                      rfl

theorem cell23_6517150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_6517150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517150 prefixEnd_6517150 := by exact prefixLift 6517150
  have htrace : WordTrace (prefixWord ++ tailWord_6517150) baseStart_6517150 baseEnd_6517150 := by
    simpa [prefixWord, tailWord_6517150, baseEnd_6517150] using wordTrace_append hprefix tailTrace_6517150
  have hstable : (prefixWord ++ tailWord_6517150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517150).length < 2 ^ (prefixWord ++ tailWord_6517150).sum := by decide
  have hdescent : baseEnd_6517150 < baseStart_6517150 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517199 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 5]
def baseStart_6517199 : Nat := 118140960795 + 6517199 * 2 ^ 59
def prefixEnd_6517199 : Nat := 4983230072969 + 3 ^ 40 * 6517199 * 2
def baseEnd_6517199 : Nat := 3346455608001352162640453

theorem tailTrace_6517199 : CollatzResearch.WordTrace tailWord_6517199 prefixEnd_6517199 3346455608001352162640453 := by
  unfold tailWord_6517199
  simp only [CollatzResearch.WordTrace]
  refine ⟨237701775516308546819954651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158467850344205697879969767 237701775516308546819954651)
  ·
    refine ⟨356552663274462820229931977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237701775516308546819954651 356552663274462820229931977)
    ·
      refine ⟨267414497455847115172448983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356552663274462820229931977 267414497455847115172448983)
      ·
        refine ⟨401121746183770672758673475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267414497455847115172448983 401121746183770672758673475)
        ·
          refine ⟨601682619275656009138010213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401121746183770672758673475 601682619275656009138010213)
          ·
            refine ⟨112815491114185501713376915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 601682619275656009138010213 112815491114185501713376915)
            ·
              refine ⟨169223236671278252570065373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112815491114185501713376915 169223236671278252570065373)
              ·
                refine ⟨63458713751729344713774515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169223236671278252570065373 63458713751729344713774515)
                ·
                  refine ⟨95188070627594017070661773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63458713751729344713774515 95188070627594017070661773)
                  ·
                    refine ⟨35695526485347756401498165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95188070627594017070661773 35695526485347756401498165)
                    ·
                      refine ⟨3346455608001352162640453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35695526485347756401498165 3346455608001352162640453)
                      ·
                        rfl

theorem cell23_6517199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 3, 5].length) (baseStart_6517199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517199 prefixEnd_6517199 := by exact prefixLift 6517199
  have htrace : WordTrace (prefixWord ++ tailWord_6517199) baseStart_6517199 baseEnd_6517199 := by
    simpa [prefixWord, tailWord_6517199, baseEnd_6517199] using wordTrace_append hprefix tailTrace_6517199
  have hstable : (prefixWord ++ tailWord_6517199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517199).length < 2 ^ (prefixWord ++ tailWord_6517199).sum := by decide
  have hdescent : baseEnd_6517199 < baseStart_6517199 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517230 : List Nat := [4, 1, 2, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_6517230 : Nat := 118140960795 + 6517230 * 2 ^ 59
def prefixEnd_6517230 : Nat := 4983230072969 + 3 ^ 40 * 6517230 * 2
def baseEnd_6517230 : Nat := 3346471525901641541352811

theorem tailTrace_6517230 : CollatzResearch.WordTrace tailWord_6517230 prefixEnd_6517230 3346471525901641541352811 := by
  unfold tailWord_6517230
  simp only [CollatzResearch.WordTrace]
  refine ⟨29712863272399529889291643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158468604119464159409555429 29712863272399529889291643)
  ·
    refine ⟨44569294908599294833937465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29712863272399529889291643 44569294908599294833937465)
    ·
      refine ⟨33426971181449471125453099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44569294908599294833937465 33426971181449471125453099)
      ·
        refine ⟨50140456772174206688179649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33426971181449471125453099 50140456772174206688179649)
        ·
          refine ⟨37605342579130655016134737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50140456772174206688179649 37605342579130655016134737)
          ·
            refine ⟨28204006934347991262101053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37605342579130655016134737 28204006934347991262101053)
            ·
              refine ⟨10576502600380496723287895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28204006934347991262101053 10576502600380496723287895)
              ·
                refine ⟨15864753900570745084931843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10576502600380496723287895 15864753900570745084931843)
                ·
                  refine ⟨23797130850856117627397765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15864753900570745084931843 23797130850856117627397765)
                  ·
                    refine ⟨4461962034535522055137081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23797130850856117627397765 4461962034535522055137081)
                    ·
                      refine ⟨3346471525901641541352811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4461962034535522055137081 3346471525901641541352811)
                      ·
                        rfl

theorem cell23_6517230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_6517230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517230 prefixEnd_6517230 := by exact prefixLift 6517230
  have htrace : WordTrace (prefixWord ++ tailWord_6517230) baseStart_6517230 baseEnd_6517230 := by
    simpa [prefixWord, tailWord_6517230, baseEnd_6517230] using wordTrace_append hprefix tailTrace_6517230
  have hstable : (prefixWord ++ tailWord_6517230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517230).length < 2 ^ (prefixWord ++ tailWord_6517230).sum := by decide
  have hdescent : baseEnd_6517230 < baseStart_6517230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517239 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_6517239 : Nat := 118140960795 + 6517239 * 2 ^ 59
def prefixEnd_6517239 : Nat := 4983230072969 + 3 ^ 40 * 6517239 * 2
def baseEnd_6517239 : Nat := 3346476147227532006140269

theorem tailTrace_6517239 : CollatzResearch.WordTrace tailWord_6517239 prefixEnd_6517239 3346476147227532006140269 := by
  unfold tailWord_6517239
  simp only [CollatzResearch.WordTrace]
  refine ⟨237703234436163633651410771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158468822957442422434273847 237703234436163633651410771)
  ·
    refine ⟨356554851654245450477116157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237703234436163633651410771 356554851654245450477116157)
    ·
      refine ⟨133708069370342043928918559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356554851654245450477116157 133708069370342043928918559)
      ·
        refine ⟨200562104055513065893377839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133708069370342043928918559 200562104055513065893377839)
        ·
          refine ⟨300843156083269598840066759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200562104055513065893377839 300843156083269598840066759)
          ·
            refine ⟨451264734124904398260100139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300843156083269598840066759 451264734124904398260100139)
            ·
              refine ⟨676897101187356597390150209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451264734124904398260100139 676897101187356597390150209)
              ·
                refine ⟨507672825890517448042612657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676897101187356597390150209 507672825890517448042612657)
                ·
                  refine ⟨380754619417888086031959493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507672825890517448042612657 380754619417888086031959493)
                  ·
                    refine ⟨71391491140854016130992405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 380754619417888086031959493 71391491140854016130992405)
                    ·
                      refine ⟨3346476147227532006140269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71391491140854016130992405 3346476147227532006140269)
                      ·
                        rfl

theorem cell23_6517239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_6517239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517239 prefixEnd_6517239 := by exact prefixLift 6517239
  have htrace : WordTrace (prefixWord ++ tailWord_6517239) baseStart_6517239 baseEnd_6517239 := by
    simpa [prefixWord, tailWord_6517239, baseEnd_6517239] using wordTrace_append hprefix tailTrace_6517239
  have hstable : (prefixWord ++ tailWord_6517239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517239).length < 2 ^ (prefixWord ++ tailWord_6517239).sum := by decide
  have hdescent : baseEnd_6517239 < baseStart_6517239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517250 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_6517250 : Nat := 118140960795 + 6517250 * 2 ^ 59
def prefixEnd_6517250 : Nat := 4983230072969 + 3 ^ 40 * 6517250 * 2
def baseEnd_6517250 : Nat := 3346481795514731463102719

theorem tailTrace_6517250 : CollatzResearch.WordTrace tailWord_6517250 prefixEnd_6517250 3346481795514731463102719 := by
  unfold tailWord_6517250
  simp only [CollatzResearch.WordTrace]
  refine ⟨59425908909780945632515301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158469090426082521686707469 59425908909780945632515301)
  ·
    refine ⟨11142357920583927306096619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59425908909780945632515301 11142357920583927306096619)
    ·
      refine ⟨16713536880875890959144929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11142357920583927306096619 16713536880875890959144929)
      ·
        refine ⟨12535152660656918219358697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16713536880875890959144929 12535152660656918219358697)
        ·
          refine ⟨9401364495492688664519023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12535152660656918219358697 9401364495492688664519023)
          ·
            refine ⟨14102046743239032996778535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9401364495492688664519023 14102046743239032996778535)
            ·
              refine ⟨21153070114858549495167803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14102046743239032996778535 21153070114858549495167803)
              ·
                refine ⟨31729605172287824242751705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21153070114858549495167803 31729605172287824242751705)
                ·
                  refine ⟨23797203879215868182063779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31729605172287824242751705 23797203879215868182063779)
                  ·
                    refine ⟨35695805818823802273095669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23797203879215868182063779 35695805818823802273095669)
                    ·
                      refine ⟨3346481795514731463102719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35695805818823802273095669 3346481795514731463102719)
                      ·
                        rfl

theorem cell23_6517250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_6517250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517250 prefixEnd_6517250 := by exact prefixLift 6517250
  have htrace : WordTrace (prefixWord ++ tailWord_6517250) baseStart_6517250 baseEnd_6517250 := by
    simpa [prefixWord, tailWord_6517250, baseEnd_6517250] using wordTrace_append hprefix tailTrace_6517250
  have hstable : (prefixWord ++ tailWord_6517250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517250).length < 2 ^ (prefixWord ++ tailWord_6517250).sum := by decide
  have hdescent : baseEnd_6517250 < baseStart_6517250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517253 : List Nat := [1, 3, 1, 1, 2, 2, 5, 3, 5]
def baseStart_6517253 : Nat := 118140960795 + 6517253 * 2 ^ 59
def prefixEnd_6517253 : Nat := 4983230072969 + 3 ^ 40 * 6517253 * 2
def baseEnd_6517253 : Nat := 371831481772966105707245

theorem tailTrace_6517253 : CollatzResearch.WordTrace tailWord_6517253 prefixEnd_6517253 371831481772966105707245 := by
  unfold tailWord_6517253
  simp only [CollatzResearch.WordTrace]
  refine ⟨237703745058112914042420413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158469163372075276028280275 237703745058112914042420413)
  ·
    refine ⟨89138904396792342765907655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237703745058112914042420413 89138904396792342765907655)
    ·
      refine ⟨133708356595188514148861483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89138904396792342765907655 133708356595188514148861483)
      ·
        refine ⟨200562534892782771223292225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133708356595188514148861483 200562534892782771223292225)
        ·
          refine ⟨150421901169587078417469169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200562534892782771223292225 150421901169587078417469169)
          ·
            refine ⟨112816425877190308813101877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150421901169587078417469169 112816425877190308813101877)
            ·
              refine ⟨10576539925986591451228301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 112816425877190308813101877 10576539925986591451228301)
              ·
                refine ⟨3966202472244971794210613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10576539925986591451228301 3966202472244971794210613)
                ·
                  refine ⟨371831481772966105707245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3966202472244971794210613 371831481772966105707245)
                  ·
                    rfl

theorem cell23_6517253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 3, 5].length) (baseStart_6517253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517253 prefixEnd_6517253 := by exact prefixLift 6517253
  have htrace : WordTrace (prefixWord ++ tailWord_6517253) baseStart_6517253 baseEnd_6517253 := by
    simpa [prefixWord, tailWord_6517253, baseEnd_6517253] using wordTrace_append hprefix tailTrace_6517253
  have hstable : (prefixWord ++ tailWord_6517253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517253).length < 2 ^ (prefixWord ++ tailWord_6517253).sum := by decide
  have hdescent : baseEnd_6517253 < baseStart_6517253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517276 : List Nat := [2, 2, 3, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_6517276 : Nat := 118140960795 + 6517276 * 2 ^ 59
def prefixEnd_6517276 : Nat := 4983230072969 + 3 ^ 40 * 6517276 * 2
def baseEnd_6517276 : Nat := 3346495146011748361377599

theorem tailTrace_6517276 : CollatzResearch.WordTrace tailWord_6517276 prefixEnd_6517276 3346495146011748361377599 := by
  unfold tailWord_6517276
  simp only [CollatzResearch.WordTrace]
  refine ⟨118852291968514794485253841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158469722624686392647005121 118852291968514794485253841)
  ·
    refine ⟨89139218976386095863940381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118852291968514794485253841 89139218976386095863940381)
    ·
      refine ⟨33427207116144785948977643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89139218976386095863940381 33427207116144785948977643)
      ·
        refine ⟨50140810674217178923466465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33427207116144785948977643 50140810674217178923466465)
        ·
          refine ⟨37605608005662884192599849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50140810674217178923466465 37605608005662884192599849)
          ·
            refine ⟨28204206004247163144449887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37605608005662884192599849 28204206004247163144449887)
            ·
              refine ⟨42306309006370744716674831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28204206004247163144449887 42306309006370744716674831)
              ·
                refine ⟨63459463509556117075012247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42306309006370744716674831 63459463509556117075012247)
                ·
                  refine ⟨95189195264334175612518371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63459463509556117075012247 95189195264334175612518371)
                  ·
                    refine ⟨142783792896501263418777557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95189195264334175612518371 142783792896501263418777557)
                    ·
                      refine ⟨3346495146011748361377599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142783792896501263418777557 3346495146011748361377599)
                      ·
                        rfl

theorem cell23_6517276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_6517276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517276 prefixEnd_6517276 := by exact prefixLift 6517276
  have htrace : WordTrace (prefixWord ++ tailWord_6517276) baseStart_6517276 baseEnd_6517276 := by
    simpa [prefixWord, tailWord_6517276, baseEnd_6517276] using wordTrace_append hprefix tailTrace_6517276
  have hstable : (prefixWord ++ tailWord_6517276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517276).length < 2 ^ (prefixWord ++ tailWord_6517276).sum := by decide
  have hdescent : baseEnd_6517276 < baseStart_6517276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517303 : List Nat := [1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 4]
def baseStart_6517303 : Nat := 118140960795 + 6517303 * 2 ^ 59
def prefixEnd_6517303 : Nat := 4983230072969 + 3 ^ 40 * 6517303 * 2
def baseEnd_6517303 : Nat := 3346509009989419755739975

theorem tailTrace_6517303 : CollatzResearch.WordTrace tailWord_6517303 prefixEnd_6517303 3346509009989419755739975 := by
  unfold tailWord_6517303
  simp only [CollatzResearch.WordTrace]
  refine ⟨237705568707931772581740563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158470379138621181721160375 237705568707931772581740563)
  ·
    refine ⟨356558353061897658872610845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237705568707931772581740563 356558353061897658872610845)
    ·
      refine ⟨133709382398211622077229067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356558353061897658872610845 133709382398211622077229067)
      ·
        refine ⟨200564073597317433115843601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133709382398211622077229067 200564073597317433115843601)
        ·
          refine ⟨150423055197988074836882701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200564073597317433115843601 150423055197988074836882701)
          ·
            refine ⟨56408645699245528063831013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150423055197988074836882701 56408645699245528063831013)
            ·
              refine ⟨10576621068608536511968315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56408645699245528063831013 10576621068608536511968315)
              ·
                refine ⟨15864931602912804767952473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10576621068608536511968315 15864931602912804767952473)
                ·
                  refine ⟨11898698702184603575964355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15864931602912804767952473 11898698702184603575964355)
                  ·
                    refine ⟨17848048053276905363946533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11898698702184603575964355 17848048053276905363946533)
                    ·
                      refine ⟨3346509009989419755739975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17848048053276905363946533 3346509009989419755739975)
                      ·
                        rfl

theorem cell23_6517303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_6517303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517303 prefixEnd_6517303 := by exact prefixLift 6517303
  have htrace : WordTrace (prefixWord ++ tailWord_6517303) baseStart_6517303 baseEnd_6517303 := by
    simpa [prefixWord, tailWord_6517303, baseEnd_6517303] using wordTrace_append hprefix tailTrace_6517303
  have hstable : (prefixWord ++ tailWord_6517303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517303).length < 2 ^ (prefixWord ++ tailWord_6517303).sum := by decide
  have hdescent : baseEnd_6517303 < baseStart_6517303 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517323 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 3]
def baseStart_6517323 : Nat := 118140960795 + 6517323 * 2 ^ 59
def prefixEnd_6517323 : Nat := 4983230072969 + 3 ^ 40 * 6517323 * 2
def baseEnd_6517323 : Nat := 3346519279602509677489883

theorem tailTrace_6517323 : CollatzResearch.WordTrace tailWord_6517323 prefixEnd_6517323 3346519279602509677489883 := by
  unfold tailWord_6517323
  simp only [CollatzResearch.WordTrace]
  refine ⟨237706298167859315997468623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158470865445239543998312415 237706298167859315997468623)
  ·
    refine ⟨356559447251788973996202935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237706298167859315997468623 356559447251788973996202935)
    ·
      refine ⟨534839170877683460994304403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356559447251788973996202935 534839170877683460994304403)
      ·
        refine ⟨802258756316525191491456605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534839170877683460994304403 802258756316525191491456605)
        ·
          refine ⟨300847033618696946809296227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 802258756316525191491456605 300847033618696946809296227)
          ·
            refine ⟨451270550428045420213944341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300847033618696946809296227 451270550428045420213944341)
            ·
              refine ⟨21153307051314629072528641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 451270550428045420213944341 21153307051314629072528641)
              ·
                refine ⟨15864980288485971804396481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21153307051314629072528641 15864980288485971804396481)
                ·
                  refine ⟨11898735216364478853297361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15864980288485971804396481 11898735216364478853297361)
                  ·
                    refine ⟨8924051412273359139973021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11898735216364478853297361 8924051412273359139973021)
                    ·
                      refine ⟨3346519279602509677489883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8924051412273359139973021 3346519279602509677489883)
                      ·
                        rfl

theorem cell23_6517323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 2, 3].length) (baseStart_6517323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517323 prefixEnd_6517323 := by exact prefixLift 6517323
  have htrace : WordTrace (prefixWord ++ tailWord_6517323) baseStart_6517323 baseEnd_6517323 := by
    simpa [prefixWord, tailWord_6517323, baseEnd_6517323] using wordTrace_append hprefix tailTrace_6517323
  have hstable : (prefixWord ++ tailWord_6517323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517323).length < 2 ^ (prefixWord ++ tailWord_6517323).sum := by decide
  have hdescent : baseEnd_6517323 < baseStart_6517323 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517326 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 8]
def baseStart_6517326 : Nat := 118140960795 + 6517326 * 2 ^ 59
def prefixEnd_6517326 : Nat := 4983230072969 + 3 ^ 40 * 6517326 * 2
def baseEnd_6517326 : Nat := 371835646671608129528041

theorem tailTrace_6517326 : CollatzResearch.WordTrace tailWord_6517326 prefixEnd_6517326 371835646671608129528041 := by
  unfold tailWord_6517326
  simp only [CollatzResearch.WordTrace]
  refine ⟨29713300948356055938728479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158470938391232298339885221 29713300948356055938728479)
  ·
    refine ⟨44569951422534083908092719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29713300948356055938728479 44569951422534083908092719)
    ·
      refine ⟨66854927133801125862139079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44569951422534083908092719 66854927133801125862139079)
      ·
        refine ⟨100282390700701688793208619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66854927133801125862139079 100282390700701688793208619)
        ·
          refine ⟨150423586051052533189812929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100282390700701688793208619 150423586051052533189812929)
          ·
            refine ⟨112817689538289399892359697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150423586051052533189812929 112817689538289399892359697)
            ·
              refine ⟨84613267153717049919269773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112817689538289399892359697 84613267153717049919269773)
              ·
                refine ⟨31729975182643893719726165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84613267153717049919269773 31729975182643893719726165)
                ·
                  refine ⟨371835646671608129528041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31729975182643893719726165 371835646671608129528041)
                  ·
                    rfl

theorem cell23_6517326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_6517326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517326 prefixEnd_6517326 := by exact prefixLift 6517326
  have htrace : WordTrace (prefixWord ++ tailWord_6517326) baseStart_6517326 baseEnd_6517326 := by
    simpa [prefixWord, tailWord_6517326, baseEnd_6517326] using wordTrace_append hprefix tailTrace_6517326
  have hstable : (prefixWord ++ tailWord_6517326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517326).length < 2 ^ (prefixWord ++ tailWord_6517326).sum := by decide
  have hdescent : baseEnd_6517326 < baseStart_6517326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517357 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_6517357 : Nat := 118140960795 + 6517357 * 2 ^ 59
def prefixEnd_6517357 : Nat := 4983230072969 + 3 ^ 40 * 6517357 * 2
def baseEnd_6517357 : Nat := 3346536737944762544464727

theorem tailTrace_6517357 : CollatzResearch.WordTrace tailWord_6517357 prefixEnd_6517357 3346536737944762544464727 := by
  unfold tailWord_6517357
  simp only [CollatzResearch.WordTrace]
  refine ⟨237707538249736139804206325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158471692166490759869470883 237707538249736139804206325)
  ·
    refine ⟨22285081710912763106644343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237707538249736139804206325 22285081710912763106644343)
    ·
      refine ⟨33427622566369144659966515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22285081710912763106644343 33427622566369144659966515)
      ·
        refine ⟨50141433849553716989949773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33427622566369144659966515 50141433849553716989949773)
        ·
          refine ⟨18803037693582643871231165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50141433849553716989949773 18803037693582643871231165)
          ·
            refine ⟨7051139135093491451711687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18803037693582643871231165 7051139135093491451711687)
            ·
              refine ⟨10576708702640237177567531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7051139135093491451711687 10576708702640237177567531)
              ·
                refine ⟨15865063053960355766351297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10576708702640237177567531 15865063053960355766351297)
                ·
                  refine ⟨11898797290470266824763473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15865063053960355766351297 11898797290470266824763473)
                  ·
                    refine ⟨8924097967852700118572605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11898797290470266824763473 8924097967852700118572605)
                    ·
                      refine ⟨3346536737944762544464727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8924097967852700118572605 3346536737944762544464727)
                      ·
                        rfl

theorem cell23_6517357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_6517357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517357 prefixEnd_6517357 := by exact prefixLift 6517357
  have htrace : WordTrace (prefixWord ++ tailWord_6517357) baseStart_6517357 baseEnd_6517357 := by
    simpa [prefixWord, tailWord_6517357, baseEnd_6517357] using wordTrace_append hprefix tailTrace_6517357
  have hstable : (prefixWord ++ tailWord_6517357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517357).length < 2 ^ (prefixWord ++ tailWord_6517357).sum := by decide
  have hdescent : baseEnd_6517357 < baseStart_6517357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517421 : List Nat := [1, 5, 2, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_6517421 : Nat := 118140960795 + 6517421 * 2 ^ 59
def prefixEnd_6517421 : Nat := 4983230072969 + 3 ^ 40 * 6517421 * 2
def baseEnd_6517421 : Nat := 3346569600706650294064433

theorem tailTrace_6517421 : CollatzResearch.WordTrace tailWord_6517421 prefixEnd_6517421 3346569600706650294064433 := by
  unfold tailWord_6517421
  simp only [CollatzResearch.WordTrace]
  refine ⟨237709872521504278734536117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158473248347669519156357411 237709872521504278734536117)
  ·
    refine ⟨22285300548891026131362761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237709872521504278734536117 22285300548891026131362761)
    ·
      refine ⟨16713975411668269598522071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22285300548891026131362761 16713975411668269598522071)
      ·
        refine ⟨25070963117502404397783107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16713975411668269598522071 25070963117502404397783107)
        ·
          refine ⟨37606444676253606596674661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25070963117502404397783107 37606444676253606596674661)
          ·
            refine ⟨7051208376797551236876499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37606444676253606596674661 7051208376797551236876499)
            ·
              refine ⟨10576812565196326855314749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7051208376797551236876499 10576812565196326855314749)
              ·
                refine ⟨3966304711948622570743031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10576812565196326855314749 3966304711948622570743031)
                ·
                  refine ⟨5949457067922933856114547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966304711948622570743031 5949457067922933856114547)
                  ·
                    refine ⟨8924185601884400784171821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5949457067922933856114547 8924185601884400784171821)
                    ·
                      refine ⟨3346569600706650294064433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8924185601884400784171821 3346569600706650294064433)
                      ·
                        rfl

theorem cell23_6517421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_6517421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517421 prefixEnd_6517421 := by exact prefixLift 6517421
  have htrace : WordTrace (prefixWord ++ tailWord_6517421) baseStart_6517421 baseEnd_6517421 := by
    simpa [prefixWord, tailWord_6517421, baseEnd_6517421] using wordTrace_append hprefix tailTrace_6517421
  have hstable : (prefixWord ++ tailWord_6517421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517421).length < 2 ^ (prefixWord ++ tailWord_6517421).sum := by decide
  have hdescent : baseEnd_6517421 < baseStart_6517421 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517444 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_6517444 : Nat := 118140960795 + 6517444 * 2 ^ 59
def prefixEnd_6517444 : Nat := 4983230072969 + 3 ^ 40 * 6517444 * 2
def baseEnd_6517444 : Nat := 3346581410761703704076827

theorem tailTrace_6517444 : CollatzResearch.WordTrace tailWord_6517444 prefixEnd_6517444 3346581410761703704076827 := by
  unfold tailWord_6517444
  simp only [CollatzResearch.WordTrace]
  refine ⟨118855355700210476831311693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158473807600280635775082257 118855355700210476831311693)
  ·
    refine ⟨44570758387578928811741885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118855355700210476831311693 44570758387578928811741885)
    ·
      refine ⟨16714034395342098304403207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44570758387578928811741885 16714034395342098304403207)
      ·
        refine ⟨25071051593013147456604811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16714034395342098304403207 25071051593013147456604811)
        ·
          refine ⟨37606577389519721184907217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25071051593013147456604811 37606577389519721184907217)
          ·
            refine ⟨28204933042139790888680413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37606577389519721184907217 28204933042139790888680413)
            ·
              refine ⟨10576849890802421583255155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28204933042139790888680413 10576849890802421583255155)
              ·
                refine ⟨15865274836203632374882733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10576849890802421583255155 15865274836203632374882733)
                ·
                  refine ⟨5949478063576362140581025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15865274836203632374882733 5949478063576362140581025)
                  ·
                    refine ⟨4462108547682271605435769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5949478063576362140581025 4462108547682271605435769)
                    ·
                      refine ⟨3346581410761703704076827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4462108547682271605435769 3346581410761703704076827)
                      ·
                        rfl

theorem cell23_6517444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_6517444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517444 prefixEnd_6517444 := by exact prefixLift 6517444
  have htrace : WordTrace (prefixWord ++ tailWord_6517444) baseStart_6517444 baseEnd_6517444 := by
    simpa [prefixWord, tailWord_6517444, baseEnd_6517444] using wordTrace_append hprefix tailTrace_6517444
  have hstable : (prefixWord ++ tailWord_6517444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517444).length < 2 ^ (prefixWord ++ tailWord_6517444).sum := by decide
  have hdescent : baseEnd_6517444 < baseStart_6517444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517454 : List Nat := [4, 1, 1, 1, 3, 4, 2, 1, 2, 4]
def baseStart_6517454 : Nat := 118140960795 + 6517454 * 2 ^ 59
def prefixEnd_6517454 : Nat := 4983230072969 + 3 ^ 40 * 6517454 * 2
def baseEnd_6517454 : Nat := 1115528848522749554983927

theorem tailTrace_6517454 : CollatzResearch.WordTrace tailWord_6517454 prefixEnd_6517454 1115528848522749554983927 := by
  unfold tailWord_6517454
  simp only [CollatzResearch.WordTrace]
  refine ⟨29713884516298090671310927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158474050753589816913658277 29713884516298090671310927)
  ·
    refine ⟨44570826774447136006966391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29713884516298090671310927 44570826774447136006966391)
    ·
      refine ⟨66856240161670704010449587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44570826774447136006966391 66856240161670704010449587)
      ·
        refine ⟨100284360242506056015674381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66856240161670704010449587 100284360242506056015674381)
        ·
          refine ⟨37606635090939771005877893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100284360242506056015674381 37606635090939771005877893)
          ·
            refine ⟨7051244079551207063602105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37606635090939771005877893 7051244079551207063602105)
            ·
              refine ⟨5288433059663405297701579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7051244079551207063602105 5288433059663405297701579)
              ·
                refine ⟨7932649589495107946552369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5288433059663405297701579 7932649589495107946552369)
                ·
                  refine ⟨5949487192121330959914277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7932649589495107946552369 5949487192121330959914277)
                  ·
                    refine ⟨1115528848522749554983927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5949487192121330959914277 1115528848522749554983927)
                    ·
                      rfl

theorem cell23_6517454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_6517454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517454 prefixEnd_6517454 := by exact prefixLift 6517454
  have htrace : WordTrace (prefixWord ++ tailWord_6517454) baseStart_6517454 baseEnd_6517454 := by
    simpa [prefixWord, tailWord_6517454, baseEnd_6517454] using wordTrace_append hprefix tailTrace_6517454
  have hstable : (prefixWord ++ tailWord_6517454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517454).length < 2 ^ (prefixWord ++ tailWord_6517454).sum := by decide
  have hdescent : baseEnd_6517454 < baseStart_6517454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517461 : List Nat := [1, 3, 2, 5, 2, 1, 1, 2, 1, 1, 4]
def baseStart_6517461 : Nat := 118140960795 + 6517461 * 2 ^ 59
def prefixEnd_6517461 : Nat := 4983230072969 + 3 ^ 40 * 6517461 * 2
def baseEnd_6517461 : Nat := 3346590139932830137564249

theorem tailTrace_6517461 : CollatzResearch.WordTrace tailWord_6517461 prefixEnd_6517461 3346590139932830137564249 := by
  unfold tailWord_6517461
  simp only [CollatzResearch.WordTrace]
  refine ⟨237711331441359365565992237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158474220960906243710661491 237711331441359365565992237)
  ·
    refine ⟨89141749290509762087247089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237711331441359365565992237 89141749290509762087247089)
    ·
      refine ⟨66856311967882321565435317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89141749290509762087247089 66856311967882321565435317)
      ·
        refine ⟨6267779246988967646759561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 66856311967882321565435317 6267779246988967646759561)
        ·
          refine ⟨4700834435241725735069671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6267779246988967646759561 4700834435241725735069671)
          ·
            refine ⟨7051251652862588602604507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4700834435241725735069671 7051251652862588602604507)
            ·
              refine ⟨10576877479293882903906761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7051251652862588602604507 10576877479293882903906761)
              ·
                refine ⟨7932658109470412177930071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10576877479293882903906761 7932658109470412177930071)
                ·
                  refine ⟨11898987164205618266895107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7932658109470412177930071 11898987164205618266895107)
                  ·
                    refine ⟨17848480746308427400342661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11898987164205618266895107 17848480746308427400342661)
                    ·
                      refine ⟨3346590139932830137564249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17848480746308427400342661 3346590139932830137564249)
                      ·
                        rfl

theorem cell23_6517461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_6517461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517461 prefixEnd_6517461 := by exact prefixLift 6517461
  have htrace : WordTrace (prefixWord ++ tailWord_6517461) baseStart_6517461 baseEnd_6517461 := by
    simpa [prefixWord, tailWord_6517461, baseEnd_6517461] using wordTrace_append hprefix tailTrace_6517461
  have hstable : (prefixWord ++ tailWord_6517461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517461).length < 2 ^ (prefixWord ++ tailWord_6517461).sum := by decide
  have hdescent : baseEnd_6517461 < baseStart_6517461 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517494 : List Nat := [5, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3]
def baseStart_6517494 : Nat := 118140960795 + 6517494 * 2 ^ 59
def prefixEnd_6517494 : Nat := 4983230072969 + 3 ^ 40 * 6517494 * 2
def baseEnd_6517494 : Nat := 3346607084794428508451597

theorem tailTrace_6517494 : CollatzResearch.WordTrace tailWord_6517494 prefixEnd_6517494 3346607084794428508451597 := by
  unfold tailWord_6517494
  simp only [CollatzResearch.WordTrace]
  refine ⟨14857033440639988262621471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 158475023366826541467962357 14857033440639988262621471)
  ·
    refine ⟨22285550160959982393932207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14857033440639988262621471 22285550160959982393932207)
    ·
      refine ⟨33428325241439973590898311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22285550160959982393932207 33428325241439973590898311)
      ·
        refine ⟨50142487862159960386347467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33428325241439973590898311 50142487862159960386347467)
        ·
          refine ⟨75213731793239940579521201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50142487862159960386347467 75213731793239940579521201)
          ·
            refine ⟨56410298844929955434640901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75213731793239940579521201 56410298844929955434640901)
            ·
              refine ⟨10576931033424366643995169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56410298844929955434640901 10576931033424366643995169)
              ·
                refine ⟨7932698275068274982996377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10576931033424366643995169 7932698275068274982996377)
                ·
                  refine ⟨5949523706301206237247283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7932698275068274982996377 5949523706301206237247283)
                  ·
                    refine ⟨8924285559451809355870925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5949523706301206237247283 8924285559451809355870925)
                    ·
                      refine ⟨3346607084794428508451597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8924285559451809355870925 3346607084794428508451597)
                      ·
                        rfl

theorem cell23_6517494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 2, 1, 3].length) (baseStart_6517494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517494 prefixEnd_6517494 := by exact prefixLift 6517494
  have htrace : WordTrace (prefixWord ++ tailWord_6517494) baseStart_6517494 baseEnd_6517494 := by
    simpa [prefixWord, tailWord_6517494, baseEnd_6517494] using wordTrace_append hprefix tailTrace_6517494
  have hstable : (prefixWord ++ tailWord_6517494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517494).length < 2 ^ (prefixWord ++ tailWord_6517494).sum := by decide
  have hdescent : baseEnd_6517494 < baseStart_6517494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517513 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 1, 4, 4]
def baseStart_6517513 : Nat := 118140960795 + 6517513 * 2 ^ 59
def prefixEnd_6517513 : Nat := 4983230072969 + 3 ^ 40 * 6517513 * 2
def baseEnd_6517513 : Nat := 3346616840926863934114009

theorem tailTrace_6517513 : CollatzResearch.WordTrace tailWord_6517513 prefixEnd_6517513 3346616840926863934114009 := by
  unfold tailWord_6517513
  simp only [CollatzResearch.WordTrace]
  refine ⟨237713228037170978446885193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158475485358113985631256795 237713228037170978446885193)
  ·
    refine ⟨178284921027878233835163895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237713228037170978446885193 178284921027878233835163895)
    ·
      refine ⟨267427381541817350752745843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178284921027878233835163895 267427381541817350752745843)
      ·
        refine ⟨401141072312726026129118765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267427381541817350752745843 401141072312726026129118765)
        ·
          refine ⟨150427902117272259798419537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401141072312726026129118765 150427902117272259798419537)
          ·
            refine ⟨112820926587954194848814653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150427902117272259798419537 112820926587954194848814653)
            ·
              refine ⟨42307847470482823068305495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112820926587954194848814653 42307847470482823068305495)
              ·
                refine ⟨63461771205724234602458243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42307847470482823068305495 63461771205724234602458243)
                ·
                  refine ⟨95192656808586351903687365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63461771205724234602458243 95192656808586351903687365)
                  ·
                    refine ⟨17848623151609940981941381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95192656808586351903687365 17848623151609940981941381)
                    ·
                      refine ⟨3346616840926863934114009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17848623151609940981941381 3346616840926863934114009)
                      ·
                        rfl

theorem cell23_6517513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_6517513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517513 prefixEnd_6517513 := by exact prefixLift 6517513
  have htrace : WordTrace (prefixWord ++ tailWord_6517513) baseStart_6517513 baseEnd_6517513 := by
    simpa [prefixWord, tailWord_6517513, baseEnd_6517513] using wordTrace_append hprefix tailTrace_6517513
  have hstable : (prefixWord ++ tailWord_6517513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517513).length < 2 ^ (prefixWord ++ tailWord_6517513).sum := by decide
  have hdescent : baseEnd_6517513 < baseStart_6517513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517523 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 7]
def baseStart_6517523 : Nat := 118140960795 + 6517523 * 2 ^ 59
def prefixEnd_6517523 : Nat := 4983230072969 + 3 ^ 40 * 6517523 * 2
def baseEnd_6517523 : Nat := 371846886192600988332107

theorem tailTrace_6517523 : CollatzResearch.WordTrace tailWord_6517523 prefixEnd_6517523 371846886192600988332107 := by
  unfold tailWord_6517523
  simp only [CollatzResearch.WordTrace]
  refine ⟨237713592767134750154749223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158475728511423166769832815 237713592767134750154749223)
  ·
    refine ⟨356570389150702125232123835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237713592767134750154749223 356570389150702125232123835)
    ·
      refine ⟨534855583726053187848185753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356570389150702125232123835 534855583726053187848185753)
      ·
        refine ⟨401141687794539890886139315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 534855583726053187848185753 401141687794539890886139315)
        ·
          refine ⟨601712531691809836329208973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401141687794539890886139315 601712531691809836329208973)
          ·
            refine ⟨225642199384428688623453365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 601712531691809836329208973 225642199384428688623453365)
            ·
              refine ⟨21153956192290189558448753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225642199384428688623453365 21153956192290189558448753)
              ·
                refine ⟨15865467144217642168836565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21153956192290189558448753 15865467144217642168836565)
                ·
                  refine ⟨371846886192600988332107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15865467144217642168836565 371846886192600988332107)
                  ·
                    rfl

theorem cell23_6517523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 7].length) (baseStart_6517523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517523 prefixEnd_6517523 := by exact prefixLift 6517523
  have htrace : WordTrace (prefixWord ++ tailWord_6517523) baseStart_6517523 baseEnd_6517523 := by
    simpa [prefixWord, tailWord_6517523, baseEnd_6517523] using wordTrace_append hprefix tailTrace_6517523
  have hstable : (prefixWord ++ tailWord_6517523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517523).length < 2 ^ (prefixWord ++ tailWord_6517523).sum := by decide
  have hdescent : baseEnd_6517523 < baseStart_6517523 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517557 : List Nat := [1, 3, 3, 1, 3, 1, 2, 4, 5]
def baseStart_6517557 : Nat := 118140960795 + 6517557 * 2 ^ 59
def prefixEnd_6517557 : Nat := 4983230072969 + 3 ^ 40 * 6517557 * 2
def baseEnd_6517557 : Nat := 371848826008406862440423

theorem tailTrace_6517557 : CollatzResearch.WordTrace tailWord_6517557 prefixEnd_6517557 371848826008406862440423 := by
  unfold tailWord_6517557
  simp only [CollatzResearch.WordTrace]
  refine ⟨237714832849011573961486925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158476555232674382640991283 237714832849011573961486925)
  ·
    refine ⟨89143062318379340235557597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237714832849011573961486925 89143062318379340235557597)
    ·
      refine ⟨33428648369392252588334099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89143062318379340235557597 33428648369392252588334099)
      ·
        refine ⟨50142972554088378882501149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33428648369392252588334099 50142972554088378882501149)
        ·
          refine ⟨18803614707783142080937931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50142972554088378882501149 18803614707783142080937931)
          ·
            refine ⟨28205422061674713121406897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18803614707783142080937931 28205422061674713121406897)
            ·
              refine ⟨21154066546256034841055173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28205422061674713121406897 21154066546256034841055173)
              ·
                refine ⟨3966387477423006532697845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21154066546256034841055173 3966387477423006532697845)
                ·
                  refine ⟨371848826008406862440423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3966387477423006532697845 371848826008406862440423)
                  ·
                    rfl

theorem cell23_6517557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 4, 5].length) (baseStart_6517557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517557 prefixEnd_6517557 := by exact prefixLift 6517557
  have htrace : WordTrace (prefixWord ++ tailWord_6517557) baseStart_6517557 baseEnd_6517557 := by
    simpa [prefixWord, tailWord_6517557, baseEnd_6517557] using wordTrace_append hprefix tailTrace_6517557
  have hstable : (prefixWord ++ tailWord_6517557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517557).length < 2 ^ (prefixWord ++ tailWord_6517557).sum := by decide
  have hdescent : baseEnd_6517557 < baseStart_6517557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517607 : List Nat := [1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_6517607 : Nat := 118140960795 + 6517607 * 2 ^ 59
def prefixEnd_6517607 : Nat := 4983230072969 + 3 ^ 40 * 6517607 * 2
def baseEnd_6517607 : Nat := 3346665108108386566338577

theorem tailTrace_6517607 : CollatzResearch.WordTrace tailWord_6517607 prefixEnd_6517607 3346665108108386566338577 := by
  unfold tailWord_6517607
  simp only [CollatzResearch.WordTrace]
  refine ⟨237716656498830432500807075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158477770999220288333871383 237716656498830432500807075)
  ·
    refine ⟨356574984748245648751210613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237716656498830432500807075 356574984748245648751210613)
    ·
      refine ⟨33428904820148029570425995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 356574984748245648751210613 33428904820148029570425995)
      ·
        refine ⟨50143357230222044355638993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33428904820148029570425995 50143357230222044355638993)
        ·
          refine ⟨37607517922666533266729245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50143357230222044355638993 37607517922666533266729245)
          ·
            refine ⟨14102819220999949975023467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37607517922666533266729245 14102819220999949975023467)
            ·
              refine ⟨21154228831499924962535201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14102819220999949975023467 21154228831499924962535201)
              ·
                refine ⟨15865671623624943721901401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21154228831499924962535201 15865671623624943721901401)
                ·
                  refine ⟨11899253717718707791426051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15865671623624943721901401 11899253717718707791426051)
                  ·
                    refine ⟨17848880576578061687139077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11899253717718707791426051 17848880576578061687139077)
                    ·
                      refine ⟨3346665108108386566338577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17848880576578061687139077 3346665108108386566338577)
                      ·
                        rfl

theorem cell23_6517607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_6517607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517607 prefixEnd_6517607 := by exact prefixLift 6517607
  have htrace : WordTrace (prefixWord ++ tailWord_6517607) baseStart_6517607 baseEnd_6517607 := by
    simpa [prefixWord, tailWord_6517607, baseEnd_6517607] using wordTrace_append hprefix tailTrace_6517607
  have hstable : (prefixWord ++ tailWord_6517607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517607).length < 2 ^ (prefixWord ++ tailWord_6517607).sum := by decide
  have hdescent : baseEnd_6517607 < baseStart_6517607 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517617 : List Nat := [1, 2, 2, 2, 1, 4, 3, 1, 3, 4]
def baseStart_6517617 : Nat := 118140960795 + 6517617 * 2 ^ 59
def prefixEnd_6517617 : Nat := 4983230072969 + 3 ^ 40 * 6517617 * 2
def baseEnd_6517617 : Nat := 1115556747638310509071177

theorem tailTrace_6517617 : CollatzResearch.WordTrace tailWord_6517617 prefixEnd_6517617 1115556747638310509071177 := by
  unfold tailWord_6517617
  simp only [CollatzResearch.WordTrace]
  refine ⟨237717021228794204208671105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158478014152529469472447403 237717021228794204208671105)
  ·
    refine ⟨178287765921595653156503329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237717021228794204208671105 178287765921595653156503329)
    ·
      refine ⟨133715824441196739867377497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178287765921595653156503329 133715824441196739867377497)
      ·
        refine ⟨100286868330897554900533123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133715824441196739867377497 100286868330897554900533123)
        ·
          refine ⟨150430302496346332350799685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100286868330897554900533123 150430302496346332350799685)
          ·
            refine ⟨28205681718064937315774941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150430302496346332350799685 28205681718064937315774941)
            ·
              refine ⟨10577130644274351493415603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28205681718064937315774941 10577130644274351493415603)
              ·
                refine ⟨15865695966411527240123405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10577130644274351493415603 15865695966411527240123405)
                ·
                  refine ⟨5949635987404322715046277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15865695966411527240123405 5949635987404322715046277)
                  ·
                    refine ⟨1115556747638310509071177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5949635987404322715046277 1115556747638310509071177)
                    ·
                      rfl

theorem cell23_6517617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 3, 4].length) (baseStart_6517617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517617 prefixEnd_6517617 := by exact prefixLift 6517617
  have htrace : WordTrace (prefixWord ++ tailWord_6517617) baseStart_6517617 baseEnd_6517617 := by
    simpa [prefixWord, tailWord_6517617, baseEnd_6517617] using wordTrace_append hprefix tailTrace_6517617
  have hstable : (prefixWord ++ tailWord_6517617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517617).length < 2 ^ (prefixWord ++ tailWord_6517617).sum := by decide
  have hdescent : baseEnd_6517617 < baseStart_6517617 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517720 : List Nat := [2, 1, 2, 2, 2, 4, 10]
def baseStart_6517720 : Nat := 118140960795 + 6517720 * 2 ^ 59
def prefixEnd_6517720 : Nat := 4983230072969 + 3 ^ 40 * 6517720 * 2
def baseEnd_6517720 : Nat := 41317569523732649681797

theorem tailTrace_6517720 : CollatzResearch.WordTrace tailWord_6517720 prefixEnd_6517720 41317569523732649681797 := by
  unfold tailWord_6517720
  simp only [CollatzResearch.WordTrace]
  refine ⟨118860388973710526399835307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158480518631614035199780409 118860388973710526399835307)
  ·
    refine ⟨178290583460565789599752961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118860388973710526399835307 178290583460565789599752961)
    ·
      refine ⟨133717937595424342199814721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178290583460565789599752961 133717937595424342199814721)
      ·
        refine ⟨100288453196568256649861041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133717937595424342199814721 100288453196568256649861041)
        ·
          refine ⟨75216339897426192487395781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100288453196568256649861041 75216339897426192487395781)
          ·
            refine ⟨14103063730767411091386709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75216339897426192487395781 14103063730767411091386709)
            ·
              refine ⟨41317569523732649681797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14103063730767411091386709 41317569523732649681797)
              ·
                rfl

theorem cell23_6517720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 10].length) (baseStart_6517720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517720 prefixEnd_6517720 := by exact prefixLift 6517720
  have htrace : WordTrace (prefixWord ++ tailWord_6517720) baseStart_6517720 baseEnd_6517720 := by
    simpa [prefixWord, tailWord_6517720, baseEnd_6517720] using wordTrace_append hprefix tailTrace_6517720
  have hstable : (prefixWord ++ tailWord_6517720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517720).length < 2 ^ (prefixWord ++ tailWord_6517720).sum := by decide
  have hdescent : baseEnd_6517720 < baseStart_6517720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517731 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 3, 2, 2]
def baseStart_6517731 : Nat := 118140960795 + 6517731 * 2 ^ 59
def prefixEnd_6517731 : Nat := 4983230072969 + 3 ^ 40 * 6517731 * 2
def baseEnd_6517731 : Nat := 3346728779709544081188007

theorem tailTrace_6517731 : CollatzResearch.WordTrace tailWord_6517731 prefixEnd_6517731 3346728779709544081188007 := by
  unfold tailWord_6517731
  simp only [CollatzResearch.WordTrace]
  refine ⟨237721179150381201678321047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158480786100254134452214031 237721179150381201678321047)
  ·
    refine ⟨356581768725571802517481571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237721179150381201678321047 356581768725571802517481571)
    ·
      refine ⟨534872653088357703776222357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356581768725571802517481571 534872653088357703776222357)
      ·
        refine ⟨25072155613516767364510423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 534872653088357703776222357 25072155613516767364510423)
        ·
          refine ⟨37608233420275151046765635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25072155613516767364510423 37608233420275151046765635)
          ·
            refine ⟨56412350130412726570148453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37608233420275151046765635 56412350130412726570148453)
            ·
              refine ⟨10577315649452386231902835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56412350130412726570148453 10577315649452386231902835)
              ·
                refine ⟨15865973474178579347854253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10577315649452386231902835 15865973474178579347854253)
                ·
                  refine ⟨5949740052816967255445345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15865973474178579347854253 5949740052816967255445345)
                  ·
                    refine ⟨4462305039612725441584009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5949740052816967255445345 4462305039612725441584009)
                    ·
                      refine ⟨3346728779709544081188007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4462305039612725441584009 3346728779709544081188007)
                      ·
                        rfl

theorem cell23_6517731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_6517731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517731 prefixEnd_6517731 := by exact prefixLift 6517731
  have htrace : WordTrace (prefixWord ++ tailWord_6517731) baseStart_6517731 baseEnd_6517731 := by
    simpa [prefixWord, tailWord_6517731, baseEnd_6517731] using wordTrace_append hprefix tailTrace_6517731
  have hstable : (prefixWord ++ tailWord_6517731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517731).length < 2 ^ (prefixWord ++ tailWord_6517731).sum := by decide
  have hdescent : baseEnd_6517731 < baseStart_6517731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517804 : List Nat := [2, 2, 1, 1, 1, 2, 4, 3, 1, 4, 2]
def baseStart_6517804 : Nat := 118140960795 + 6517804 * 2 ^ 59
def prefixEnd_6517804 : Nat := 4983230072969 + 3 ^ 40 * 6517804 * 2
def baseEnd_6517804 : Nat := 3346766263797322295575171

theorem tailTrace_6517804 : CollatzResearch.WordTrace tailWord_6517804 prefixEnd_6517804 3346766263797322295575171 := by
  unfold tailWord_6517804
  simp only [CollatzResearch.WordTrace]
  refine ⟨118861920839558367572864233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158482561119411156763818977 118861920839558367572864233)
  ·
    refine ⟨89146440629668775679648175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118861920839558367572864233 89146440629668775679648175)
    ·
      refine ⟨133719660944503163519472263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89146440629668775679648175 133719660944503163519472263)
      ·
        refine ⟨200579491416754745279208395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133719660944503163519472263 200579491416754745279208395)
        ·
          refine ⟨300869237125132117918812593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200579491416754745279208395 300869237125132117918812593)
          ·
            refine ⟨225651927843849088439109445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300869237125132117918812593 225651927843849088439109445)
            ·
              refine ⟨42309736470721704082333021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225651927843849088439109445 42309736470721704082333021)
              ·
                refine ⟨15866151176520639030874883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42309736470721704082333021 15866151176520639030874883)
                ·
                  refine ⟨23799226764780958546312325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15866151176520639030874883 23799226764780958546312325)
                  ·
                    refine ⟨4462355018396429727433561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23799226764780958546312325 4462355018396429727433561)
                    ·
                      refine ⟨3346766263797322295575171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4462355018396429727433561 3346766263797322295575171)
                      ·
                        rfl

theorem cell23_6517804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 4, 2].length) (baseStart_6517804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517804 prefixEnd_6517804 := by exact prefixLift 6517804
  have htrace : WordTrace (prefixWord ++ tailWord_6517804) baseStart_6517804 baseEnd_6517804 := by
    simpa [prefixWord, tailWord_6517804, baseEnd_6517804] using wordTrace_append hprefix tailTrace_6517804
  have hstable : (prefixWord ++ tailWord_6517804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517804).length < 2 ^ (prefixWord ++ tailWord_6517804).sum := by decide
  have hdescent : baseEnd_6517804 < baseStart_6517804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517821 : List Nat := [1, 4, 1, 3, 1, 3, 1, 2, 1, 4, 2]
def baseStart_6517821 : Nat := 118140960795 + 6517821 * 2 ^ 59
def prefixEnd_6517821 : Nat := 4983230072969 + 3 ^ 40 * 6517821 * 2
def baseEnd_6517821 : Nat := 3346774992968448729062593

theorem tailTrace_6517821 : CollatzResearch.WordTrace tailWord_6517821 prefixEnd_6517821 3346774992968448729062593 := by
  unfold tailWord_6517821
  simp only [CollatzResearch.WordTrace]
  refine ⟨237724461720055147049097317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158482974480036764699398211 237724461720055147049097317)
  ·
    refine ⟨44573336572510340071705747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237724461720055147049097317 44573336572510340071705747)
    ·
      refine ⟨66860004858765510107558621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44573336572510340071705747 66860004858765510107558621)
      ·
        refine ⟨25072501822037066290334483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66860004858765510107558621 25072501822037066290334483)
        ·
          refine ⟨37608752733055599435501725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25072501822037066290334483 37608752733055599435501725)
          ·
            refine ⟨14103282274895849788313147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37608752733055599435501725 14103282274895849788313147)
            ·
              refine ⟨21154923412343774682469721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14103282274895849788313147 21154923412343774682469721)
              ·
                refine ⟨15866192559257831011852291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21154923412343774682469721 15866192559257831011852291)
                ·
                  refine ⟨23799288838886746517778437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15866192559257831011852291 23799288838886746517778437)
                  ·
                    refine ⟨4462366657291264972083457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23799288838886746517778437 4462366657291264972083457)
                    ·
                      refine ⟨3346774992968448729062593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4462366657291264972083457 3346774992968448729062593)
                      ·
                        rfl

theorem cell23_6517821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_6517821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517821 prefixEnd_6517821 := by exact prefixLift 6517821
  have htrace : WordTrace (prefixWord ++ tailWord_6517821) baseStart_6517821 baseEnd_6517821 := by
    simpa [prefixWord, tailWord_6517821, baseEnd_6517821] using wordTrace_append hprefix tailTrace_6517821
  have hstable : (prefixWord ++ tailWord_6517821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517821).length < 2 ^ (prefixWord ++ tailWord_6517821).sum := by decide
  have hdescent : baseEnd_6517821 < baseStart_6517821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517825 : List Nat := [1, 2, 5, 1, 3, 1, 3, 1, 1, 3, 2]
def baseStart_6517825 : Nat := 118140960795 + 6517825 * 2 ^ 59
def prefixEnd_6517825 : Nat := 4983230072969 + 3 ^ 40 * 6517825 * 2
def baseEnd_6517825 : Nat := 3346777046891066713412575

theorem tailTrace_6517825 : CollatzResearch.WordTrace tailWord_6517825 prefixEnd_6517825 3346777046891066713412575 := by
  unfold tailWord_6517825
  simp only [CollatzResearch.WordTrace]
  refine ⟨237724607612040655732242929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158483071741360437154828619 237724607612040655732242929)
  ·
    refine ⟨178293455709030491799182197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237724607612040655732242929 178293455709030491799182197)
    ·
      refine ⟨16715011472721608606173331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178293455709030491799182197 16715011472721608606173331)
      ·
        refine ⟨25072517209082412909259997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16715011472721608606173331 25072517209082412909259997)
        ·
          refine ⟨9402193953405904840972499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25072517209082412909259997 9402193953405904840972499)
          ·
            refine ⟨14103290930108857261458749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9402193953405904840972499 14103290930108857261458749)
            ·
              refine ⟨5288734098790821473047031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14103290930108857261458749 5288734098790821473047031)
              ·
                refine ⟨7933101148186232209570547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5288734098790821473047031 7933101148186232209570547)
                ·
                  refine ⟨11899651722279348314355821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7933101148186232209570547 11899651722279348314355821)
                  ·
                    refine ⟨4462369395854755617883433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11899651722279348314355821 4462369395854755617883433)
                    ·
                      refine ⟨3346777046891066713412575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4462369395854755617883433 3346777046891066713412575)
                      ·
                        rfl

theorem cell23_6517825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_6517825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517825 prefixEnd_6517825 := by exact prefixLift 6517825
  have htrace : WordTrace (prefixWord ++ tailWord_6517825) baseStart_6517825 baseEnd_6517825 := by
    simpa [prefixWord, tailWord_6517825, baseEnd_6517825] using wordTrace_append hprefix tailTrace_6517825
  have hstable : (prefixWord ++ tailWord_6517825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517825).length < 2 ^ (prefixWord ++ tailWord_6517825).sum := by decide
  have hdescent : baseEnd_6517825 < baseStart_6517825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517838 : List Nat := [4, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2]
def baseStart_6517838 : Nat := 118140960795 + 6517838 * 2 ^ 59
def prefixEnd_6517838 : Nat := 4983230072969 + 3 ^ 40 * 6517838 * 2
def baseEnd_6517838 : Nat := 3346783722139575162550015

theorem tailTrace_6517838 : CollatzResearch.WordTrace tailWord_6517838 prefixEnd_6517838 3346783722139575162550015 := by
  unfold tailWord_6517838
  simp only [CollatzResearch.WordTrace]
  refine ⟨29715635220124194869058271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158483387840662372634977445 29715635220124194869058271)
  ·
    refine ⟨44573452830186292303587407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29715635220124194869058271 44573452830186292303587407)
    ·
      refine ⟨66860179245279438455381111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44573452830186292303587407 66860179245279438455381111)
      ·
        refine ⟨100290268867919157683071667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66860179245279438455381111 100290268867919157683071667)
        ·
          refine ⟨150435403301878736524607501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100290268867919157683071667 150435403301878736524607501)
          ·
            refine ⟨56413276238204526196727813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150435403301878736524607501 56413276238204526196727813)
            ·
              refine ⟨10577489294663348661886465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56413276238204526196727813 10577489294663348661886465)
              ·
                refine ⟨7933116970997511496414849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10577489294663348661886465 7933116970997511496414849)
                ·
                  refine ⟨5949837728248133622311137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7933116970997511496414849 5949837728248133622311137)
                  ·
                    refine ⟨4462378296186100216733353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5949837728248133622311137 4462378296186100216733353)
                    ·
                      refine ⟨3346783722139575162550015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4462378296186100216733353 3346783722139575162550015)
                      ·
                        rfl

theorem cell23_6517838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_6517838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517838 prefixEnd_6517838 := by exact prefixLift 6517838
  have htrace : WordTrace (prefixWord ++ tailWord_6517838) baseStart_6517838 baseEnd_6517838 := by
    simpa [prefixWord, tailWord_6517838, baseEnd_6517838] using wordTrace_append hprefix tailTrace_6517838
  have hstable : (prefixWord ++ tailWord_6517838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517838).length < 2 ^ (prefixWord ++ tailWord_6517838).sum := by decide
  have hdescent : baseEnd_6517838 < baseStart_6517838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517857 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 4, 5]
def baseStart_6517857 : Nat := 118140960795 + 6517857 * 2 ^ 59
def prefixEnd_6517857 : Nat := 4983230072969 + 3 ^ 40 * 6517857 * 2
def baseEnd_6517857 : Nat := 1115597826090670196070809

theorem tailTrace_6517857 : CollatzResearch.WordTrace tailWord_6517857 prefixEnd_6517857 1115597826090670196070809 := by
  unfold tailWord_6517857
  simp only [CollatzResearch.WordTrace]
  refine ⟨237725774747924725197407825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158483849831949816798271883 237725774747924725197407825)
  ·
    refine ⟨178294331060943543898055869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237725774747924725197407825 178294331060943543898055869)
    ·
      refine ⟨66860374147853828961770951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178294331060943543898055869 66860374147853828961770951)
      ·
        refine ⟨100290561221780743442656427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66860374147853828961770951 100290561221780743442656427)
        ·
          refine ⟨150435841832671115163984641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100290561221780743442656427 150435841832671115163984641)
          ·
            refine ⟨112826881374503336372988481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150435841832671115163984641 112826881374503336372988481)
            ·
              refine ⟨84620161030877502279741361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112826881374503336372988481 84620161030877502279741361)
              ·
                refine ⟨63465120773158126709806021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84620161030877502279741361 63465120773158126709806021)
                ·
                  refine ⟨11899710144967148758088629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63465120773158126709806021 11899710144967148758088629)
                  ·
                    refine ⟨1115597826090670196070809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11899710144967148758088629 1115597826090670196070809)
                    ·
                      rfl

theorem cell23_6517857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_6517857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517857 prefixEnd_6517857 := by exact prefixLift 6517857
  have htrace : WordTrace (prefixWord ++ tailWord_6517857) baseStart_6517857 baseEnd_6517857 := by
    simpa [prefixWord, tailWord_6517857, baseEnd_6517857] using wordTrace_append hprefix tailTrace_6517857
  have hstable : (prefixWord ++ tailWord_6517857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517857).length < 2 ^ (prefixWord ++ tailWord_6517857).sum := by decide
  have hdescent : baseEnd_6517857 < baseStart_6517857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517911 : List Nat := [1, 1, 3, 3, 3, 1, 2, 1, 2, 4, 2]
def baseStart_6517911 : Nat := 118140960795 + 6517911 * 2 ^ 59
def prefixEnd_6517911 : Nat := 4983230072969 + 3 ^ 40 * 6517911 * 2
def baseEnd_6517911 : Nat := 3346821206227353376937179

theorem tailTrace_6517911 : CollatzResearch.WordTrace tailWord_6517911 prefixEnd_6517911 3346821206227353376937179 := by
  unfold tailWord_6517911
  simp only [CollatzResearch.WordTrace]
  refine ⟨237727744289729092419873587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158485162859819394946582391 237727744289729092419873587)
  ·
    refine ⟨356591616434593638629810381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237727744289729092419873587 356591616434593638629810381)
    ·
      refine ⟨133721856162972614486178893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356591616434593638629810381 133721856162972614486178893)
      ·
        refine ⟨50145696061114730432317085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133721856162972614486178893 50145696061114730432317085)
        ·
          refine ⟨18804636022918023912118907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50145696061114730432317085 18804636022918023912118907)
          ·
            refine ⟨28206954034377035868178361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18804636022918023912118907 28206954034377035868178361)
            ·
              refine ⟨21155215525782776901133771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28206954034377035868178361 21155215525782776901133771)
              ·
                refine ⟨31732823288674165351700657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21155215525782776901133771 31732823288674165351700657)
                ·
                  refine ⟨23799617466505624013775493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31732823288674165351700657 23799617466505624013775493)
                  ·
                    refine ⟨4462428274969804502582905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23799617466505624013775493 4462428274969804502582905)
                    ·
                      refine ⟨3346821206227353376937179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4462428274969804502582905 3346821206227353376937179)
                      ·
                        rfl

theorem cell23_6517911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_6517911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517911 prefixEnd_6517911 := by exact prefixLift 6517911
  have htrace : WordTrace (prefixWord ++ tailWord_6517911) baseStart_6517911 baseEnd_6517911 := by
    simpa [prefixWord, tailWord_6517911, baseEnd_6517911] using wordTrace_append hprefix tailTrace_6517911
  have hstable : (prefixWord ++ tailWord_6517911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517911).length < 2 ^ (prefixWord ++ tailWord_6517911).sum := by decide
  have hdescent : baseEnd_6517911 < baseStart_6517911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517938 : List Nat := [3, 2, 1, 1, 1, 4, 3, 3, 1, 4]
def baseStart_6517938 : Nat := 118140960795 + 6517938 * 2 ^ 59
def prefixEnd_6517938 : Nat := 4983230072969 + 3 ^ 40 * 6517938 * 2
def baseEnd_6517938 : Nat := 1115611690068341590433185

theorem tailTrace_6517938 : CollatzResearch.WordTrace tailWord_6517938 prefixEnd_6517938 1115611690068341590433185 := by
  unfold tailWord_6517938
  simp only [CollatzResearch.WordTrace]
  refine ⟨59432182265157819007776617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158485819373754184020737645 59432182265157819007776617)
  ·
    refine ⟨44574136698868364255832463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59432182265157819007776617 44574136698868364255832463)
    ·
      refine ⟨66861205048302546383748695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44574136698868364255832463 66861205048302546383748695)
      ·
        refine ⟨100291807572453819575623043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66861205048302546383748695 100291807572453819575623043)
        ·
          refine ⟨150437711358680729363434565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100291807572453819575623043 150437711358680729363434565)
          ·
            refine ⟨28207070879752636755643981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150437711358680729363434565 28207070879752636755643981)
            ·
              refine ⟨10577651579907238783366493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28207070879752636755643981 10577651579907238783366493)
              ·
                refine ⟨3966619342465214543762435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10577651579907238783366493 3966619342465214543762435)
                ·
                  refine ⟨5949929013697821815643653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966619342465214543762435 5949929013697821815643653)
                  ·
                    refine ⟨1115611690068341590433185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5949929013697821815643653 1115611690068341590433185)
                    ·
                      rfl

theorem cell23_6517938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 3, 3, 1, 4].length) (baseStart_6517938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517938 prefixEnd_6517938 := by exact prefixLift 6517938
  have htrace : WordTrace (prefixWord ++ tailWord_6517938) baseStart_6517938 baseEnd_6517938 := by
    simpa [prefixWord, tailWord_6517938, baseEnd_6517938] using wordTrace_append hprefix tailTrace_6517938
  have hstable : (prefixWord ++ tailWord_6517938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517938).length < 2 ^ (prefixWord ++ tailWord_6517938).sum := by decide
  have hdescent : baseEnd_6517938 < baseStart_6517938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517957 : List Nat := [1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_6517957 : Nat := 118140960795 + 6517957 * 2 ^ 59
def prefixEnd_6517957 : Nat := 4983230072969 + 3 ^ 40 * 6517957 * 2
def baseEnd_6517957 : Nat := 3346844826337460196961967

theorem tailTrace_6517957 : CollatzResearch.WordTrace tailWord_6517957 prefixEnd_6517957 3346844826337460196961967 := by
  unfold tailWord_6517957
  simp only [CollatzResearch.WordTrace]
  refine ⟨237729422047562442276048125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158486281365041628184032083 237729422047562442276048125)
  ·
    refine ⟨89148533267835915853518047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237729422047562442276048125 89148533267835915853518047)
    ·
      refine ⟨133722799901753873780277071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89148533267835915853518047 133722799901753873780277071)
      ·
        refine ⟨200584199852630810670415607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133722799901753873780277071 200584199852630810670415607)
        ·
          refine ⟨300876299778946216005623411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200584199852630810670415607 300876299778946216005623411)
          ·
            refine ⟨451314449668419324008435117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300876299778946216005623411 451314449668419324008435117)
            ·
              refine ⟨169242918625657246503163169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 451314449668419324008435117 169242918625657246503163169)
              ·
                refine ⟨126932188969242934877372377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169242918625657246503163169 126932188969242934877372377)
                ·
                  refine ⟨95199141726932201158029283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126932188969242934877372377 95199141726932201158029283)
                  ·
                    refine ⟨142798712590398301737043925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95199141726932201158029283 142798712590398301737043925)
                    ·
                      refine ⟨3346844826337460196961967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142798712590398301737043925 3346844826337460196961967)
                      ·
                        rfl

theorem cell23_6517957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_6517957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517957 prefixEnd_6517957 := by exact prefixLift 6517957
  have htrace : WordTrace (prefixWord ++ tailWord_6517957) baseStart_6517957 baseEnd_6517957 := by
    simpa [prefixWord, tailWord_6517957, baseEnd_6517957] using wordTrace_append hprefix tailTrace_6517957
  have hstable : (prefixWord ++ tailWord_6517957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517957).length < 2 ^ (prefixWord ++ tailWord_6517957).sum := by decide
  have hdescent : baseEnd_6517957 < baseStart_6517957 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6517994 : List Nat := [3, 1, 3, 1, 1, 3, 1, 1, 3, 6]
def baseStart_6517994 : Nat := 118140960795 + 6517994 * 2 ^ 59
def prefixEnd_6517994 : Nat := 4983230072969 + 3 ^ 40 * 6517994 * 2
def baseEnd_6517994 : Nat := 1115621275040558850733099

theorem tailTrace_6517994 : CollatzResearch.WordTrace tailWord_6517994 prefixEnd_6517994 1115621275040558850733099 := by
  unfold tailWord_6517994
  simp only [CollatzResearch.WordTrace]
  refine ⟨59432692887107099398786259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158487181032285598396763357 59432692887107099398786259)
  ·
    refine ⟨89149039330660649098179389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59432692887107099398786259 89149039330660649098179389)
    ·
      refine ⟨33430889748997743411817271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89149039330660649098179389 33430889748997743411817271)
      ·
        refine ⟨50146334623496615117725907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33430889748997743411817271 50146334623496615117725907)
        ·
          refine ⟨75219501935244922676588861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50146334623496615117725907 75219501935244922676588861)
          ·
            refine ⟨28207313225716846003720823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75219501935244922676588861 28207313225716846003720823)
            ·
              refine ⟨42310969838575269005581235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28207313225716846003720823 42310969838575269005581235)
              ·
                refine ⟨63466454757862903508371853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42310969838575269005581235 63466454757862903508371853)
                ·
                  refine ⟨23799920534198588815639445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63466454757862903508371853 23799920534198588815639445)
                  ·
                    refine ⟨1115621275040558850733099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23799920534198588815639445 1115621275040558850733099)
                    ·
                      rfl

theorem cell23_6517994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_6517994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6517994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6517994 prefixEnd_6517994 := by exact prefixLift 6517994
  have htrace : WordTrace (prefixWord ++ tailWord_6517994) baseStart_6517994 baseEnd_6517994 := by
    simpa [prefixWord, tailWord_6517994, baseEnd_6517994] using wordTrace_append hprefix tailTrace_6517994
  have hstable : (prefixWord ++ tailWord_6517994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6517994).length < 2 ^ (prefixWord ++ tailWord_6517994).sum := by decide
  have hdescent : baseEnd_6517994 < baseStart_6517994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6517994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518051 : List Nat := [1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 3]
def baseStart_6518051 : Nat := 118140960795 + 6518051 * 2 ^ 59
def prefixEnd_6518051 : Nat := 4983230072969 + 3 ^ 40 * 6518051 * 2
def baseEnd_6518051 : Nat := 3346893093518982829186535

theorem tailTrace_6518051 : CollatzResearch.WordTrace tailWord_6518051 prefixEnd_6518051 3346893093518982829186535 := by
  unfold tailWord_6518051
  simp only [CollatzResearch.WordTrace]
  refine ⟨237732850509221896329970007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158488567006147930886646671 237732850509221896329970007)
  ·
    refine ⟨356599275763832844494955011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237732850509221896329970007 356599275763832844494955011)
    ·
      refine ⟨534898913645749266742432517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356599275763832844494955011 534898913645749266742432517)
      ·
        refine ⟨100293546308577987514206097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 534898913645749266742432517 100293546308577987514206097)
        ·
          refine ⟨75220159731433490635654573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100293546308577987514206097 75220159731433490635654573)
          ·
            refine ⟨28207559899287558988370465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75220159731433490635654573 28207559899287558988370465)
            ·
              refine ⟨21155669924465669241277849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28207559899287558988370465 21155669924465669241277849)
              ·
                refine ⟨15866752443349251930958387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21155669924465669241277849 15866752443349251930958387)
                ·
                  refine ⟨23800128665023877896437581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15866752443349251930958387 23800128665023877896437581)
                  ·
                    refine ⟨8925048249383954211164093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23800128665023877896437581 8925048249383954211164093)
                    ·
                      refine ⟨3346893093518982829186535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8925048249383954211164093 3346893093518982829186535)
                      ·
                        rfl

theorem cell23_6518051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_6518051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518051 prefixEnd_6518051 := by exact prefixLift 6518051
  have htrace : WordTrace (prefixWord ++ tailWord_6518051) baseStart_6518051 baseEnd_6518051 := by
    simpa [prefixWord, tailWord_6518051, baseEnd_6518051] using wordTrace_append hprefix tailTrace_6518051
  have hstable : (prefixWord ++ tailWord_6518051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518051).length < 2 ^ (prefixWord ++ tailWord_6518051).sum := by decide
  have hdescent : baseEnd_6518051 < baseStart_6518051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518052 : List Nat := [2, 3, 1, 3, 1, 1, 4, 3, 1, 2, 2]
def baseStart_6518052 : Nat := 118140960795 + 6518052 * 2 ^ 59
def prefixEnd_6518052 : Nat := 4983230072969 + 3 ^ 40 * 6518052 * 2
def baseEnd_6518052 : Nat := 3346893606999637325274031

theorem tailTrace_6518052 : CollatzResearch.WordTrace tailWord_6518052 prefixEnd_6518052 3346893606999637325274031 := by
  unfold tailWord_6518052
  simp only [CollatzResearch.WordTrace]
  refine ⟨118866443491109136750378205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158488591321478849000504273 118866443491109136750378205)
  ·
    refine ⟨44574916309165926281391827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118866443491109136750378205 44574916309165926281391827)
    ·
      refine ⟨66862374463748889422087741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44574916309165926281391827 66862374463748889422087741)
      ·
        refine ⟨25073390423905833533282903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66862374463748889422087741 25073390423905833533282903)
        ·
          refine ⟨37610085635858750299924355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25073390423905833533282903 37610085635858750299924355)
          ·
            refine ⟨56415128453788125449886533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37610085635858750299924355 56415128453788125449886533)
            ·
              refine ⟨10577836585085273521853725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56415128453788125449886533 10577836585085273521853725)
              ·
                refine ⟨3966688719406977570695147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10577836585085273521853725 3966688719406977570695147)
                ·
                  refine ⟨5950033079110466356042721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966688719406977570695147 5950033079110466356042721)
                  ·
                    refine ⟨4462524809332849767032041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5950033079110466356042721 4462524809332849767032041)
                    ·
                      refine ⟨3346893606999637325274031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4462524809332849767032041 3346893606999637325274031)
                      ·
                        rfl

theorem cell23_6518052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_6518052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518052 prefixEnd_6518052 := by exact prefixLift 6518052
  have htrace : WordTrace (prefixWord ++ tailWord_6518052) baseStart_6518052 baseEnd_6518052 := by
    simpa [prefixWord, tailWord_6518052, baseEnd_6518052] using wordTrace_append hprefix tailTrace_6518052
  have hstable : (prefixWord ++ tailWord_6518052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518052).length < 2 ^ (prefixWord ++ tailWord_6518052).sum := by decide
  have hdescent : baseEnd_6518052 < baseStart_6518052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518125 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_6518125 : Nat := 118140960795 + 6518125 * 2 ^ 59
def prefixEnd_6518125 : Nat := 4983230072969 + 3 ^ 40 * 6518125 * 2
def baseEnd_6518125 : Nat := 3346931091087415539661195

theorem tailTrace_6518125 : CollatzResearch.WordTrace tailWord_6518125 prefixEnd_6518125 3346931091087415539661195 := by
  unfold tailWord_6518125
  simp only [CollatzResearch.WordTrace]
  refine ⟨237735549510953806968163829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158490366340635871312109219 237735549510953806968163829)
  ·
    refine ⟨22287707766651919403265359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 237735549510953806968163829 22287707766651919403265359)
    ·
      refine ⟨33431561649977879104898039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22287707766651919403265359 33431561649977879104898039)
      ·
        refine ⟨50147342474966818657347059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33431561649977879104898039 50147342474966818657347059)
        ·
          refine ⟨75221013712450227986020589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50147342474966818657347059 75221013712450227986020589)
          ·
            refine ⟨28207880142168835494757721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75221013712450227986020589 28207880142168835494757721)
            ·
              refine ⟨21155910106626626621068291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28207880142168835494757721 21155910106626626621068291)
              ·
                refine ⟨31733865159939939931602437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21155910106626626621068291 31733865159939939931602437)
                ·
                  refine ⟨5950099717488738737175457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31733865159939939931602437 5950099717488738737175457)
                  ·
                    refine ⟨4462574788116554052881593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5950099717488738737175457 4462574788116554052881593)
                    ·
                      refine ⟨3346931091087415539661195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4462574788116554052881593 3346931091087415539661195)
                      ·
                        rfl

theorem cell23_6518125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_6518125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518125 prefixEnd_6518125 := by exact prefixLift 6518125
  have htrace : WordTrace (prefixWord ++ tailWord_6518125) baseStart_6518125 baseEnd_6518125 := by
    simpa [prefixWord, tailWord_6518125, baseEnd_6518125] using wordTrace_append hprefix tailTrace_6518125
  have hstable : (prefixWord ++ tailWord_6518125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518125).length < 2 ^ (prefixWord ++ tailWord_6518125).sum := by decide
  have hdescent : baseEnd_6518125 < baseStart_6518125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518141 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_6518141 : Nat := 118140960795 + 6518141 * 2 ^ 59
def prefixEnd_6518141 : Nat := 4983230072969 + 3 ^ 40 * 6518141 * 2
def baseEnd_6518141 : Nat := 3346939306777887477061121

theorem tailTrace_6518141 : CollatzResearch.WordTrace tailWord_6518141 prefixEnd_6518141 3346939306777887477061121 := by
  unfold tailWord_6518141
  simp only [CollatzResearch.WordTrace]
  refine ⟨237736133078895841700746277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158490755385930561133830851 237736133078895841700746277)
  ·
    refine ⟨44575524952292970318889927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237736133078895841700746277 44575524952292970318889927)
    ·
      refine ⟨66863287428439455478334891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44575524952292970318889927 66863287428439455478334891)
      ·
        refine ⟨100294931142659183217502337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66863287428439455478334891 100294931142659183217502337)
        ·
          refine ⟨75221198356994387413126753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100294931142659183217502337 75221198356994387413126753)
          ·
            refine ⟨56415898767745790559845065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75221198356994387413126753 56415898767745790559845065)
            ·
              refine ⟨42311924075809342919883799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56415898767745790559845065 42311924075809342919883799)
              ·
                refine ⟨63467886113714014379825699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42311924075809342919883799 63467886113714014379825699)
                ·
                  refine ⟨95201829170571021569738549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63467886113714014379825699 95201829170571021569738549)
                  ·
                    refine ⟨8925171484741033272162989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 95201829170571021569738549 8925171484741033272162989)
                    ·
                      refine ⟨3346939306777887477061121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8925171484741033272162989 3346939306777887477061121)
                      ·
                        rfl

theorem cell23_6518141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_6518141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518141 prefixEnd_6518141 := by exact prefixLift 6518141
  have htrace : WordTrace (prefixWord ++ tailWord_6518141) baseStart_6518141 baseEnd_6518141 := by
    simpa [prefixWord, tailWord_6518141, baseEnd_6518141] using wordTrace_append hprefix tailTrace_6518141
  have hstable : (prefixWord ++ tailWord_6518141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518141).length < 2 ^ (prefixWord ++ tailWord_6518141).sum := by decide
  have hdescent : baseEnd_6518141 < baseStart_6518141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518144 : List Nat := [2, 1, 1, 2, 1, 2, 1, 3, 3, 7]
def baseStart_6518144 : Nat := 118140960795 + 6518144 * 2 ^ 59
def prefixEnd_6518144 : Nat := 4983230072969 + 3 ^ 40 * 6518144 * 2
def baseEnd_6518144 : Nat := 1115646949073283655107869

theorem tailTrace_6518144 : CollatzResearch.WordTrace tailWord_6518144 prefixEnd_6518144 1115646949073283655107869 := by
  unfold tailWord_6518144
  simp only [CollatzResearch.WordTrace]
  refine ⟨118868121248942486606552743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158490828331923315475403657 118868121248942486606552743)
  ·
    refine ⟨178302181873413729909829115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118868121248942486606552743 178302181873413729909829115)
    ·
      refine ⟨267453272810120594864743673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178302181873413729909829115 267453272810120594864743673)
      ·
        refine ⟨200589954607590446148557755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267453272810120594864743673 200589954607590446148557755)
        ·
          refine ⟨300884931911385669222836633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200589954607590446148557755 300884931911385669222836633)
          ·
            refine ⟨225663698933539251917127475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300884931911385669222836633 225663698933539251917127475)
            ·
              refine ⟨338495548400308877875691213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225663698933539251917127475 338495548400308877875691213)
              ·
                refine ⟨126935830650115829203384205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338495548400308877875691213 126935830650115829203384205)
                ·
                  refine ⟨47600936493793435951269077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 126935830650115829203384205 47600936493793435951269077)
                  ·
                    refine ⟨1115646949073283655107869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47600936493793435951269077 1115646949073283655107869)
                    ·
                      rfl

theorem cell23_6518144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_6518144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518144 prefixEnd_6518144 := by exact prefixLift 6518144
  have htrace : WordTrace (prefixWord ++ tailWord_6518144) baseStart_6518144 baseEnd_6518144 := by
    simpa [prefixWord, tailWord_6518144, baseEnd_6518144] using wordTrace_append hprefix tailTrace_6518144
  have hstable : (prefixWord ++ tailWord_6518144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518144).length < 2 ^ (prefixWord ++ tailWord_6518144).sum := by decide
  have hdescent : baseEnd_6518144 < baseStart_6518144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518178 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 2, 5]
def baseStart_6518178 : Nat := 118140960795 + 6518178 * 2 ^ 59
def prefixEnd_6518178 : Nat := 4983230072969 + 3 ^ 40 * 6518178 * 2
def baseEnd_6518178 : Nat := 1115652768520701277432817

theorem tailTrace_6518178 : CollatzResearch.WordTrace tailWord_6518178 prefixEnd_6518178 1115652768520701277432817 := by
  unfold tailWord_6518178
  simp only [CollatzResearch.WordTrace]
  refine ⟨59434370644940449254960797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158491655053174531346562125 59434370644940449254960797)
  ·
    refine ⟨22287888991852668470610299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59434370644940449254960797 22287888991852668470610299)
    ·
      refine ⟨33431833487779002705915449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22287888991852668470610299 33431833487779002705915449)
      ·
        refine ⟨25073875115834252029436587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33431833487779002705915449 25073875115834252029436587)
        ·
          refine ⟨37610812673751378044154881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25073875115834252029436587 37610812673751378044154881)
          ·
            refine ⟨28208109505313533533116161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37610812673751378044154881 28208109505313533533116161)
            ·
              refine ⟨21156082128985150149837121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28208109505313533533116161 21156082128985150149837121)
              ·
                refine ⟨15867061596738862612377841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21156082128985150149837121 15867061596738862612377841)
                ·
                  refine ⟨11900296197554146959283381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15867061596738862612377841 11900296197554146959283381)
                  ·
                    refine ⟨1115652768520701277432817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11900296197554146959283381 1115652768520701277432817)
                    ·
                      rfl

theorem cell23_6518178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_6518178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518178 prefixEnd_6518178 := by exact prefixLift 6518178
  have htrace : WordTrace (prefixWord ++ tailWord_6518178) baseStart_6518178 baseEnd_6518178 := by
    simpa [prefixWord, tailWord_6518178, baseEnd_6518178] using wordTrace_append hprefix tailTrace_6518178
  have hstable : (prefixWord ++ tailWord_6518178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518178).length < 2 ^ (prefixWord ++ tailWord_6518178).sum := by decide
  have hdescent : baseEnd_6518178 < baseStart_6518178 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518181 : List Nat := [1, 3, 1, 2, 1, 1, 2, 3, 4, 1, 4]
def baseStart_6518181 : Nat := 118140960795 + 6518181 * 2 ^ 59
def prefixEnd_6518181 : Nat := 4983230072969 + 3 ^ 40 * 6518181 * 2
def baseEnd_6518181 : Nat := 3346959846004067320560937

theorem tailTrace_6518181 : CollatzResearch.WordTrace tailWord_6518181 prefixEnd_6518181 3346959846004067320560937 := by
  unfold tailWord_6518181
  simp only [CollatzResearch.WordTrace]
  refine ⟨237737591998750928532202397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158491727999167285688134931 237737591998750928532202397)
  ·
    refine ⟨89151596999531598199575899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237737591998750928532202397 89151596999531598199575899)
    ·
      refine ⟨133727395499297397299363849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89151596999531598199575899 133727395499297397299363849)
      ·
        refine ⟨100295546624473047974522887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133727395499297397299363849 100295546624473047974522887)
        ·
          refine ⟨150443319936709571961784331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100295546624473047974522887 150443319936709571961784331)
          ·
            refine ⟨225664979905064357942676497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150443319936709571961784331 225664979905064357942676497)
            ·
              refine ⟨169248734928798268457007373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225664979905064357942676497 169248734928798268457007373)
              ·
                refine ⟨63468275598299350671377765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169248734928798268457007373 63468275598299350671377765)
                ·
                  refine ⟨11900301674681128250883331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63468275598299350671377765 11900301674681128250883331)
                  ·
                    refine ⟨17850452512021692376324997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11900301674681128250883331 17850452512021692376324997)
                    ·
                      refine ⟨3346959846004067320560937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17850452512021692376324997 3346959846004067320560937)
                      ·
                        rfl

theorem cell23_6518181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_6518181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518181 prefixEnd_6518181 := by exact prefixLift 6518181
  have htrace : WordTrace (prefixWord ++ tailWord_6518181) baseStart_6518181 baseEnd_6518181 := by
    simpa [prefixWord, tailWord_6518181, baseEnd_6518181] using wordTrace_append hprefix tailTrace_6518181
  have hstable : (prefixWord ++ tailWord_6518181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518181).length < 2 ^ (prefixWord ++ tailWord_6518181).sum := by decide
  have hdescent : baseEnd_6518181 < baseStart_6518181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518191 : List Nat := [1, 1, 2, 1, 2, 2, 1, 2, 7, 4]
def baseStart_6518191 : Nat := 118140960795 + 6518191 * 2 ^ 59
def prefixEnd_6518191 : Nat := 4983230072969 + 3 ^ 40 * 6518191 * 2
def baseEnd_6518191 : Nat := 1115654993603537427145297

theorem tailTrace_6518191 : CollatzResearch.WordTrace tailWord_6518191 prefixEnd_6518191 1115654993603537427145297 := by
  unfold tailWord_6518191
  simp only [CollatzResearch.WordTrace]
  refine ⟨237737956728714700240066427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158491971152476466826710951 237737956728714700240066427)
  ·
    refine ⟨356606935093072050360099641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237737956728714700240066427 356606935093072050360099641)
    ·
      refine ⟨267455201319804037770074731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356606935093072050360099641 267455201319804037770074731)
      ·
        refine ⟨401182801979706056655112097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267455201319804037770074731 401182801979706056655112097)
        ·
          refine ⟨300887101484779542491334073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401182801979706056655112097 300887101484779542491334073)
          ·
            refine ⟨225665326113584656868500555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300887101484779542491334073 225665326113584656868500555)
            ·
              refine ⟨338497989170376985302750833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225665326113584656868500555 338497989170376985302750833)
              ·
                refine ⟨253873491877782738977063125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338497989170376985302750833 253873491877782738977063125)
                ·
                  refine ⟨5950159965885532944774917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 253873491877782738977063125 5950159965885532944774917)
                  ·
                    refine ⟨1115654993603537427145297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5950159965885532944774917 1115654993603537427145297)
                    ·
                      rfl

theorem cell23_6518191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 2, 7, 4].length) (baseStart_6518191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518191 prefixEnd_6518191 := by exact prefixLift 6518191
  have htrace : WordTrace (prefixWord ++ tailWord_6518191) baseStart_6518191 baseEnd_6518191 := by
    simpa [prefixWord, tailWord_6518191, baseEnd_6518191] using wordTrace_append hprefix tailTrace_6518191
  have hstable : (prefixWord ++ tailWord_6518191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518191).length < 2 ^ (prefixWord ++ tailWord_6518191).sum := by decide
  have hdescent : baseEnd_6518191 < baseStart_6518191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518218 : List Nat := [3, 1, 2, 1, 2, 4, 1, 1, 1, 4, 3]
def baseStart_6518218 : Nat := 118140960795 + 6518218 * 2 ^ 59
def prefixEnd_6518218 : Nat := 4983230072969 + 3 ^ 40 * 6518218 * 2
def baseEnd_6518218 : Nat := 3346978844788283675798267

theorem tailTrace_6518218 : CollatzResearch.WordTrace tailWord_6518218 prefixEnd_6518218 3346978844788283675798267 := by
  unfold tailWord_6518218
  simp only [CollatzResearch.WordTrace]
  refine ⟨59434735374904220962824827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158492627666411255900866205 59434735374904220962824827)
  ·
    refine ⟨89152103062356331444237241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59434735374904220962824827 89152103062356331444237241)
    ·
      refine ⟨66864077296767248583177931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89152103062356331444237241 66864077296767248583177931)
      ·
        refine ⟨100296115945150872874766897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66864077296767248583177931 100296115945150872874766897)
        ·
          refine ⟨75222086958863154656075173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100296115945150872874766897 75222086958863154656075173)
          ·
            refine ⟨14104141304786841498014095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75222086958863154656075173 14104141304786841498014095)
            ·
              refine ⟨21156211957180262247021143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14104141304786841498014095 21156211957180262247021143)
              ·
                refine ⟨31734317935770393370531715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21156211957180262247021143 31734317935770393370531715)
                ·
                  refine ⟨47601476903655590055797573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31734317935770393370531715 47601476903655590055797573)
                  ·
                    refine ⟨8925276919435423135462045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47601476903655590055797573 8925276919435423135462045)
                    ·
                      refine ⟨3346978844788283675798267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8925276919435423135462045 3346978844788283675798267)
                      ·
                        rfl

theorem cell23_6518218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 1, 1, 1, 4, 3].length) (baseStart_6518218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518218 prefixEnd_6518218 := by exact prefixLift 6518218
  have htrace : WordTrace (prefixWord ++ tailWord_6518218) baseStart_6518218 baseEnd_6518218 := by
    simpa [prefixWord, tailWord_6518218, baseEnd_6518218] using wordTrace_append hprefix tailTrace_6518218
  have hstable : (prefixWord ++ tailWord_6518218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518218).length < 2 ^ (prefixWord ++ tailWord_6518218).sum := by decide
  have hdescent : baseEnd_6518218 < baseStart_6518218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518231 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 3]
def baseStart_6518231 : Nat := 118140960795 + 6518231 * 2 ^ 59
def prefixEnd_6518231 : Nat := 4983230072969 + 3 ^ 40 * 6518231 * 2
def baseEnd_6518231 : Nat := 3346985520036792124935707

theorem tailTrace_6518231 : CollatzResearch.WordTrace tailWord_6518231 prefixEnd_6518231 3346985520036792124935707 := by
  unfold tailWord_6518231
  simp only [CollatzResearch.WordTrace]
  refine ⟨237739415648569787071522547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158492943765713191381015031 237739415648569787071522547)
  ·
    refine ⟨356609123472854680607283821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237739415648569787071522547 356609123472854680607283821)
    ·
      refine ⟨133728421302320505227731433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356609123472854680607283821 133728421302320505227731433)
      ·
        refine ⟨100296315976740378920798575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133728421302320505227731433 100296315976740378920798575)
        ·
          refine ⟨150444473965110568381197863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100296315976740378920798575 150444473965110568381197863)
          ·
            refine ⟨225666710947665852571796795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150444473965110568381197863 225666710947665852571796795)
            ·
              refine ⟨338500066421498778857695193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225666710947665852571796795 338500066421498778857695193)
              ·
                refine ⟨253875049816124084143271395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338500066421498778857695193 253875049816124084143271395)
                ·
                  refine ⟨380812574724186126214907093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253875049816124084143271395 380812574724186126214907093)
                  ·
                    refine ⟨8925294720098112333161885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 380812574724186126214907093 8925294720098112333161885)
                    ·
                      refine ⟨3346985520036792124935707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8925294720098112333161885 3346985520036792124935707)
                      ·
                        rfl

theorem cell23_6518231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_6518231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518231 prefixEnd_6518231 := by exact prefixLift 6518231
  have htrace : WordTrace (prefixWord ++ tailWord_6518231) baseStart_6518231 baseEnd_6518231 := by
    simpa [prefixWord, tailWord_6518231, baseEnd_6518231] using wordTrace_append hprefix tailTrace_6518231
  have hstable : (prefixWord ++ tailWord_6518231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518231).length < 2 ^ (prefixWord ++ tailWord_6518231).sum := by decide
  have hdescent : baseEnd_6518231 < baseStart_6518231 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518241 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 6]
def baseStart_6518241 : Nat := 118140960795 + 6518241 * 2 ^ 59
def prefixEnd_6518241 : Nat := 4983230072969 + 3 ^ 40 * 6518241 * 2
def baseEnd_6518241 : Nat := 3346990654843337085810661

theorem tailTrace_6518241 : CollatzResearch.WordTrace tailWord_6518241 prefixEnd_6518241 3346990654843337085810661 := by
  unfold tailWord_6518241
  simp only [CollatzResearch.WordTrace]
  refine ⟨237739780378533558779386577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158493186919022372519591051 237739780378533558779386577)
  ·
    refine ⟨178304835283900169084539933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237739780378533558779386577 178304835283900169084539933)
    ·
      refine ⟨66864313231462563406702475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178304835283900169084539933 66864313231462563406702475)
      ·
        refine ⟨100296469847193845110053713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66864313231462563406702475 100296469847193845110053713)
        ·
          refine ⟨75222352385395383832540285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100296469847193845110053713 75222352385395383832540285)
          ·
            refine ⟨28208382144523268937202607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75222352385395383832540285 28208382144523268937202607)
            ·
              refine ⟨42312573216784903405803911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28208382144523268937202607 42312573216784903405803911)
              ·
                refine ⟨63468859825177355108705867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42312573216784903405803911 63468859825177355108705867)
                ·
                  refine ⟨95203289737766032663058801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63468859825177355108705867 95203289737766032663058801)
                  ·
                    refine ⟨71402467303324524497294101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95203289737766032663058801 71402467303324524497294101)
                    ·
                      refine ⟨3346990654843337085810661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71402467303324524497294101 3346990654843337085810661)
                      ·
                        rfl

theorem cell23_6518241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_6518241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518241 prefixEnd_6518241 := by exact prefixLift 6518241
  have htrace : WordTrace (prefixWord ++ tailWord_6518241) baseStart_6518241 baseEnd_6518241 := by
    simpa [prefixWord, tailWord_6518241, baseEnd_6518241] using wordTrace_append hprefix tailTrace_6518241
  have hstable : (prefixWord ++ tailWord_6518241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518241).length < 2 ^ (prefixWord ++ tailWord_6518241).sum := by decide
  have hdescent : baseEnd_6518241 < baseStart_6518241 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518251 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 3, 5]
def baseStart_6518251 : Nat := 118140960795 + 6518251 * 2 ^ 59
def prefixEnd_6518251 : Nat := 4983230072969 + 3 ^ 40 * 6518251 * 2
def baseEnd_6518251 : Nat := 1115665263216627348895205

theorem tailTrace_6518251 : CollatzResearch.WordTrace tailWord_6518251 prefixEnd_6518251 1115665263216627348895205 := by
  unfold tailWord_6518251
  simp only [CollatzResearch.WordTrace]
  refine ⟨237740145108497330487250607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158493430072331553658167071 237740145108497330487250607)
  ·
    refine ⟨356610217662745995730875911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237740145108497330487250607 356610217662745995730875911)
    ·
      refine ⟨534915326494118993596313867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356610217662745995730875911 534915326494118993596313867)
      ·
        refine ⟨802372989741178490394470801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534915326494118993596313867 802372989741178490394470801)
        ·
          refine ⟨601779742305883867795853101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 802372989741178490394470801 601779742305883867795853101)
          ·
            refine ⟨225667403364706450423444913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 601779742305883867795853101 225667403364706450423444913)
            ·
              refine ⟨169250552523529837817583685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225667403364706450423444913 169250552523529837817583685)
              ·
                refine ⟨31734478598161844590796941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 169250552523529837817583685 31734478598161844590796941)
                ·
                  refine ⟨11900429474310691721548853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31734478598161844590796941 11900429474310691721548853)
                  ·
                    refine ⟨1115665263216627348895205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11900429474310691721548853 1115665263216627348895205)
                    ·
                      rfl

theorem cell23_6518251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 5].length) (baseStart_6518251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518251 prefixEnd_6518251 := by exact prefixLift 6518251
  have htrace : WordTrace (prefixWord ++ tailWord_6518251) baseStart_6518251 baseEnd_6518251 := by
    simpa [prefixWord, tailWord_6518251, baseEnd_6518251] using wordTrace_append hprefix tailTrace_6518251
  have hstable : (prefixWord ++ tailWord_6518251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518251).length < 2 ^ (prefixWord ++ tailWord_6518251).sum := by decide
  have hdescent : baseEnd_6518251 < baseStart_6518251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518268 : List Nat := [2, 2, 2, 1, 2, 1, 3, 4, 1, 5]
def baseStart_6518268 : Nat := 118140960795 + 6518268 * 2 ^ 59
def prefixEnd_6518268 : Nat := 4983230072969 + 3 ^ 40 * 6518268 * 2
def baseEnd_6518268 : Nat := 1115668172940336160057679

theorem tailTrace_6518268 : CollatzResearch.WordTrace tailWord_6518268 prefixEnd_6518268 1115668172940336160057679 := by
  unfold tailWord_6518268
  simp only [CollatzResearch.WordTrace]
  refine ⟨118870382574717871195309729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158493843432957161593746305 118870382574717871195309729)
  ·
    refine ⟨89152786931038403396482297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118870382574717871195309729 89152786931038403396482297)
    ·
      refine ⟨66864590198278802547361723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89152786931038403396482297 66864590198278802547361723)
      ·
        refine ⟨100296885297418203821042585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66864590198278802547361723 100296885297418203821042585)
        ·
          refine ⟨75222663973063652865781939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100296885297418203821042585 75222663973063652865781939)
          ·
            refine ⟨112833995959595479298672909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75222663973063652865781939 112833995959595479298672909)
            ·
              refine ⟨42312748484848304737002341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112833995959595479298672909 42312748484848304737002341)
              ·
                refine ⟨7933640340909057138187939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42312748484848304737002341 7933640340909057138187939)
                ·
                  refine ⟨11900460511363585707281909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7933640340909057138187939 11900460511363585707281909)
                  ·
                    refine ⟨1115668172940336160057679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11900460511363585707281909 1115668172940336160057679)
                    ·
                      rfl

theorem cell23_6518268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_6518268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518268 prefixEnd_6518268 := by exact prefixLift 6518268
  have htrace : WordTrace (prefixWord ++ tailWord_6518268) baseStart_6518268 baseEnd_6518268 := by
    simpa [prefixWord, tailWord_6518268, baseEnd_6518268] using wordTrace_append hprefix tailTrace_6518268
  have hstable : (prefixWord ++ tailWord_6518268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518268).length < 2 ^ (prefixWord ++ tailWord_6518268).sum := by decide
  have hdescent : baseEnd_6518268 < baseStart_6518268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518276 : List Nat := [2, 3, 2, 3, 3, 1, 1, 3, 1, 4]
def baseStart_6518276 : Nat := 118140960795 + 6518276 * 2 ^ 59
def prefixEnd_6518276 : Nat := 4983230072969 + 3 ^ 40 * 6518276 * 2
def baseEnd_6518276 : Nat := 1115669542222081482957667

theorem tailTrace_6518276 : CollatzResearch.WordTrace tailWord_6518276 prefixEnd_6518276 1115669542222081482957667 := by
  unfold tailWord_6518276
  simp only [CollatzResearch.WordTrace]
  refine ⟨118870528466703379878455341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158494037955604506504607121 118870528466703379878455341)
  ·
    refine ⟨44576448175013767454420753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118870528466703379878455341 44576448175013767454420753)
    ·
      refine ⟨33432336131260325590815565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44576448175013767454420753 33432336131260325590815565)
      ·
        refine ⟨12537126049222622096555837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33432336131260325590815565 12537126049222622096555837)
        ·
          refine ⟨4701422268458483286208439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12537126049222622096555837 4701422268458483286208439)
          ·
            refine ⟨7052133402687724929312659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701422268458483286208439 7052133402687724929312659)
            ·
              refine ⟨10578200104031587393968989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7052133402687724929312659 10578200104031587393968989)
              ·
                refine ⟨3966825039011845272738371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10578200104031587393968989 3966825039011845272738371)
                ·
                  refine ⟨5950237558517767909107557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3966825039011845272738371 5950237558517767909107557)
                  ·
                    refine ⟨1115669542222081482957667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5950237558517767909107557 1115669542222081482957667)
                    ·
                      rfl

theorem cell23_6518276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_6518276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518276 prefixEnd_6518276 := by exact prefixLift 6518276
  have htrace : WordTrace (prefixWord ++ tailWord_6518276) baseStart_6518276 baseEnd_6518276 := by
    simpa [prefixWord, tailWord_6518276, baseEnd_6518276] using wordTrace_append hprefix tailTrace_6518276
  have hstable : (prefixWord ++ tailWord_6518276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518276).length < 2 ^ (prefixWord ++ tailWord_6518276).sum := by decide
  have hdescent : baseEnd_6518276 < baseStart_6518276 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518281 : List Nat := [1, 2, 1, 1, 3, 1, 4, 1, 3, 6]
def baseStart_6518281 : Nat := 118140960795 + 6518281 * 2 ^ 59
def prefixEnd_6518281 : Nat := 4983230072969 + 3 ^ 40 * 6518281 * 2
def baseEnd_6518281 : Nat := 1115670398023172309770159

theorem tailTrace_6518281 : CollatzResearch.WordTrace tailWord_6518281 prefixEnd_6518281 1115670398023172309770159 := by
  unfold tailWord_6518281
  simp only [CollatzResearch.WordTrace]
  refine ⟨237741239298388645610842697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158494159532259097073895131 237741239298388645610842697)
  ·
    refine ⟨178305929473791484208132023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237741239298388645610842697 178305929473791484208132023)
    ·
      refine ⟨267458894210687226312198035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178305929473791484208132023 267458894210687226312198035)
      ·
        refine ⟨401188341316030839468297053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267458894210687226312198035 401188341316030839468297053)
        ·
          refine ⟨150445627993511564800611395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401188341316030839468297053 150445627993511564800611395)
          ·
            refine ⟨225668441990267347200917093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150445627993511564800611395 225668441990267347200917093)
            ·
              refine ⟨42312832873175127600171955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 225668441990267347200917093 42312832873175127600171955)
              ·
                refine ⟨63469249309762691400257933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42312832873175127600171955 63469249309762691400257933)
                ·
                  refine ⟨23800968491161009275096725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63469249309762691400257933 23800968491161009275096725)
                  ·
                    refine ⟨1115670398023172309770159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23800968491161009275096725 1115670398023172309770159)
                    ·
                      rfl

theorem cell23_6518281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 6].length) (baseStart_6518281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518281 prefixEnd_6518281 := by exact prefixLift 6518281
  have htrace : WordTrace (prefixWord ++ tailWord_6518281) baseStart_6518281 baseEnd_6518281 := by
    simpa [prefixWord, tailWord_6518281, baseEnd_6518281] using wordTrace_append hprefix tailTrace_6518281
  have hstable : (prefixWord ++ tailWord_6518281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518281).length < 2 ^ (prefixWord ++ tailWord_6518281).sum := by decide
  have hdescent : baseEnd_6518281 < baseStart_6518281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518325 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_6518325 : Nat := 118140960795 + 6518325 * 2 ^ 59
def prefixEnd_6518325 : Nat := 4983230072969 + 3 ^ 40 * 6518325 * 2
def baseEnd_6518325 : Nat := 3347033787218314757160275

theorem tailTrace_6518325 : CollatzResearch.WordTrace tailWord_6518325 prefixEnd_6518325 3347033787218314757160275 := by
  unfold tailWord_6518325
  simp only [CollatzResearch.WordTrace]
  refine ⟨237742844110229241125444429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158495229406819494083629619 237742844110229241125444429)
  ·
    refine ⟨89153566541335965422041661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237742844110229241125444429 89153566541335965422041661)
    ·
      refine ⟨33432587453000987033265623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89153566541335965422041661 33432587453000987033265623)
      ·
        refine ⟨50148881179501480549898435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33432587453000987033265623 50148881179501480549898435)
        ·
          refine ⟨75223321769252220824847653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50148881179501480549898435 75223321769252220824847653)
          ·
            refine ⟨14104372831734791404658935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75223321769252220824847653 14104372831734791404658935)
            ·
              refine ⟨21156559247602187106988403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14104372831734791404658935 21156559247602187106988403)
              ·
                refine ⟨31734838871403280660482605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21156559247602187106988403 31734838871403280660482605)
                ·
                  refine ⟨11900564576776230247680977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31734838871403280660482605 11900564576776230247680977)
                  ·
                    refine ⟨8925423432582172685760733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11900564576776230247680977 8925423432582172685760733)
                    ·
                      refine ⟨3347033787218314757160275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8925423432582172685760733 3347033787218314757160275)
                      ·
                        rfl

theorem cell23_6518325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_6518325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518325 prefixEnd_6518325 := by exact prefixLift 6518325
  have htrace : WordTrace (prefixWord ++ tailWord_6518325) baseStart_6518325 baseEnd_6518325 := by
    simpa [prefixWord, tailWord_6518325, baseEnd_6518325] using wordTrace_append hprefix tailTrace_6518325
  have hstable : (prefixWord ++ tailWord_6518325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518325).length < 2 ^ (prefixWord ++ tailWord_6518325).sum := by decide
  have hdescent : baseEnd_6518325 < baseStart_6518325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518349 : List Nat := [1, 6, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_6518349 : Nat := 118140960795 + 6518349 * 2 ^ 59
def prefixEnd_6518349 : Nat := 4983230072969 + 3 ^ 40 * 6518349 * 2
def baseEnd_6518349 : Nat := 1115682036918007554420055

theorem tailTrace_6518349 : CollatzResearch.WordTrace tailWord_6518349 prefixEnd_6518349 1115682036918007554420055 := by
  unfold tailWord_6518349
  simp only [CollatzResearch.WordTrace]
  refine ⟨237743719462142293224318101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158495812974761528816212067 237743719462142293224318101)
  ·
    refine ⟨11144236849787919994889911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 237743719462142293224318101 11144236849787919994889911)
    ·
      refine ⟨16716355274681879992334867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11144236849787919994889911 16716355274681879992334867)
      ·
        refine ⟨25074532912022819988502301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16716355274681879992334867 25074532912022819988502301)
        ·
          refine ⟨9402949842008557495688363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25074532912022819988502301 9402949842008557495688363)
          ·
            refine ⟨14104424763012836243532545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9402949842008557495688363 14104424763012836243532545)
            ·
              refine ⟨10578318572259627182649409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14104424763012836243532545 10578318572259627182649409)
              ·
                refine ⟨7933738929194720386987057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10578318572259627182649409 7933738929194720386987057)
                ·
                  refine ⟨5950304196896040290240293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7933738929194720386987057 5950304196896040290240293)
                  ·
                    refine ⟨1115682036918007554420055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5950304196896040290240293 1115682036918007554420055)
                    ·
                      rfl

theorem cell23_6518349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_6518349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518349 prefixEnd_6518349 := by exact prefixLift 6518349
  have htrace : WordTrace (prefixWord ++ tailWord_6518349) baseStart_6518349 baseEnd_6518349 := by
    simpa [prefixWord, tailWord_6518349, baseEnd_6518349] using wordTrace_append hprefix tailTrace_6518349
  have hstable : (prefixWord ++ tailWord_6518349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518349).length < 2 ^ (prefixWord ++ tailWord_6518349).sum := by decide
  have hdescent : baseEnd_6518349 < baseStart_6518349 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518372 : List Nat := [2, 3, 1, 1, 2, 3, 2, 3, 2, 1, 3]
def baseStart_6518372 : Nat := 118140960795 + 6518372 * 2 ^ 59
def prefixEnd_6518372 : Nat := 4983230072969 + 3 ^ 40 * 6518372 * 2
def baseEnd_6518372 : Nat := 3347057920809076073272559

theorem tailTrace_6518372 : CollatzResearch.WordTrace tailWord_6518372 prefixEnd_6518372 3347057920809076073272559 := by
  unfold tailWord_6518372
  simp only [CollatzResearch.WordTrace]
  refine ⟨118872279170529484076202685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158496372227372645434936913 118872279170529484076202685)
  ·
    refine ⟨44577104688948556528576007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118872279170529484076202685 44577104688948556528576007)
    ·
      refine ⟨66865657033422834792864011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44577104688948556528576007 66865657033422834792864011)
      ·
        refine ⟨100298485550134252189296017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66865657033422834792864011 100298485550134252189296017)
        ·
          refine ⟨75223864162600689141972013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100298485550134252189296017 75223864162600689141972013)
          ·
            refine ⟨28208949060975258428239505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75223864162600689141972013 28208949060975258428239505)
            ·
              refine ⟨21156711795731443821179629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28208949060975258428239505 21156711795731443821179629)
              ·
                refine ⟨7933766923399291432942361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21156711795731443821179629 7933766923399291432942361)
                ·
                  refine ⟨5950325192549468574706771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7933766923399291432942361 5950325192549468574706771)
                  ·
                    refine ⟨8925487788824202862060157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5950325192549468574706771 8925487788824202862060157)
                    ·
                      refine ⟨3347057920809076073272559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8925487788824202862060157 3347057920809076073272559)
                      ·
                        rfl

theorem cell23_6518372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_6518372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518372 prefixEnd_6518372 := by exact prefixLift 6518372
  have htrace : WordTrace (prefixWord ++ tailWord_6518372) baseStart_6518372 baseEnd_6518372 := by
    simpa [prefixWord, tailWord_6518372, baseEnd_6518372] using wordTrace_append hprefix tailTrace_6518372
  have hstable : (prefixWord ++ tailWord_6518372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518372).length < 2 ^ (prefixWord ++ tailWord_6518372).sum := by decide
  have hdescent : baseEnd_6518372 < baseStart_6518372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518395 : List Nat := [1, 1, 1, 1, 1, 4, 3, 4, 1, 4, 2]
def baseStart_6518395 : Nat := 118140960795 + 6518395 * 2 ^ 59
def prefixEnd_6518395 : Nat := 4983230072969 + 3 ^ 40 * 6518395 * 2
def baseEnd_6518395 : Nat := 3347069730864129483284953

theorem tailTrace_6518395 : CollatzResearch.WordTrace tailWord_6518395 prefixEnd_6518395 3347069730864129483284953 := by
  unfold tailWord_6518395
  simp only [CollatzResearch.WordTrace]
  refine ⟨237745397219975643080492639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158496931479983762053661759 237745397219975643080492639)
  ·
    refine ⟨356618095829963464620738959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237745397219975643080492639 356618095829963464620738959)
    ·
      refine ⟨534927143744945196931108439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356618095829963464620738959 534927143744945196931108439)
      ·
        refine ⟨802390715617417795396662659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 534927143744945196931108439 802390715617417795396662659)
        ·
          refine ⟨1203586073426126693094993989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802390715617417795396662659 1203586073426126693094993989)
          ·
            refine ⟨225672388767398754955311373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1203586073426126693094993989 225672388767398754955311373)
            ·
              refine ⟨84627145787774533108241765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 225672388767398754955311373 84627145787774533108241765)
              ·
                refine ⟨15867589835207724957795331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84627145787774533108241765 15867589835207724957795331)
                ·
                  refine ⟨23801384752811587436692997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15867589835207724957795331 23801384752811587436692997)
                  ·
                    refine ⟨4462759641152172644379937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23801384752811587436692997 4462759641152172644379937)
                    ·
                      refine ⟨3347069730864129483284953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4462759641152172644379937 3347069730864129483284953)
                      ·
                        rfl

theorem cell23_6518395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 1, 4, 2].length) (baseStart_6518395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518395 prefixEnd_6518395 := by exact prefixLift 6518395
  have htrace : WordTrace (prefixWord ++ tailWord_6518395) baseStart_6518395 baseEnd_6518395 := by
    simpa [prefixWord, tailWord_6518395, baseEnd_6518395] using wordTrace_append hprefix tailTrace_6518395
  have hstable : (prefixWord ++ tailWord_6518395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518395).length < 2 ^ (prefixWord ++ tailWord_6518395).sum := by decide
  have hdescent : baseEnd_6518395 < baseStart_6518395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518412 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 4, 2, 2]
def baseStart_6518412 : Nat := 118140960795 + 6518412 * 2 ^ 59
def prefixEnd_6518412 : Nat := 4983230072969 + 3 ^ 40 * 6518412 * 2
def baseEnd_6518412 : Nat := 3347078460035255916772375

theorem tailTrace_6518412 : CollatzResearch.WordTrace tailWord_6518412 prefixEnd_6518412 3347078460035255916772375 := by
  unfold tailWord_6518412
  simp only [CollatzResearch.WordTrace]
  refine ⟨118873008630457027491930745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158497344840609369989240993 118873008630457027491930745)
  ·
    refine ⟨89154756472842770618948059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118873008630457027491930745 89154756472842770618948059)
    ·
      refine ⟨133732134709264155928422089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89154756472842770618948059 133732134709264155928422089)
      ·
        refine ⟨100299101031948116946316567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133732134709264155928422089 100299101031948116946316567)
        ·
          refine ⟨150448651547922175419474851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100299101031948116946316567 150448651547922175419474851)
          ·
            refine ⟨225672977321883263129212277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150448651547922175419474851 225672977321883263129212277)
            ·
              refine ⟨21156841623926555918363651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225672977321883263129212277 21156841623926555918363651)
              ·
                refine ⟨31735262435889833877545477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21156841623926555918363651 31735262435889833877545477)
                ·
                  refine ⟨5950361706729343852039777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31735262435889833877545477 5950361706729343852039777)
                  ·
                    refine ⟨4462771280047007889029833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5950361706729343852039777 4462771280047007889029833)
                    ·
                      refine ⟨3347078460035255916772375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4462771280047007889029833 3347078460035255916772375)
                      ·
                        rfl

theorem cell23_6518412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_6518412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518412 prefixEnd_6518412 := by exact prefixLift 6518412
  have htrace : WordTrace (prefixWord ++ tailWord_6518412) baseStart_6518412 baseEnd_6518412 := by
    simpa [prefixWord, tailWord_6518412, baseEnd_6518412] using wordTrace_append hprefix tailTrace_6518412
  have hstable : (prefixWord ++ tailWord_6518412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518412).length < 2 ^ (prefixWord ++ tailWord_6518412).sum := by decide
  have hdescent : baseEnd_6518412 < baseStart_6518412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518448 : List Nat := [2, 1, 1, 1, 2, 1, 6, 1, 1, 7]
def baseStart_6518448 : Nat := 118140960795 + 6518448 * 2 ^ 59
def prefixEnd_6518448 : Nat := 4983230072969 + 3 ^ 40 * 6518448 * 2
def baseEnd_6518448 : Nat := 1115698981779605925307403

theorem tailTrace_6518448 : CollatzResearch.WordTrace tailWord_6518448 prefixEnd_6518448 1115698981779605925307403 := by
  unfold tailWord_6518448
  simp only [CollatzResearch.WordTrace]
  refine ⟨118873665144391816566085999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158498220192522422088114665 118873665144391816566085999)
  ·
    refine ⟨178310497716587724849128999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118873665144391816566085999 178310497716587724849128999)
    ·
      refine ⟨267465746574881587273693499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178310497716587724849128999 267465746574881587273693499)
      ·
        refine ⟨401198619862322380910540249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267465746574881587273693499 401198619862322380910540249)
        ·
          refine ⟨300898964896741785682905187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401198619862322380910540249 300898964896741785682905187)
          ·
            refine ⟨451348447345112678524357781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300898964896741785682905187 451348447345112678524357781)
            ·
              refine ⟨21156958469302156805829271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 451348447345112678524357781 21156958469302156805829271)
              ·
                refine ⟨31735437703953235208743907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21156958469302156805829271 31735437703953235208743907)
                ·
                  refine ⟨47603156555929852813115861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31735437703953235208743907 47603156555929852813115861)
                  ·
                    refine ⟨1115698981779605925307403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47603156555929852813115861 1115698981779605925307403)
                    ·
                      rfl

theorem cell23_6518448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 1, 1, 7].length) (baseStart_6518448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518448 prefixEnd_6518448 := by exact prefixLift 6518448
  have htrace : WordTrace (prefixWord ++ tailWord_6518448) baseStart_6518448 baseEnd_6518448 := by
    simpa [prefixWord, tailWord_6518448, baseEnd_6518448] using wordTrace_append hprefix tailTrace_6518448
  have hstable : (prefixWord ++ tailWord_6518448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518448).length < 2 ^ (prefixWord ++ tailWord_6518448).sum := by decide
  have hdescent : baseEnd_6518448 < baseStart_6518448 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518495 : List Nat := [1, 1, 2, 3, 2, 2, 2, 1, 5, 4]
def baseStart_6518495 : Nat := 118140960795 + 6518495 * 2 ^ 59
def prefixEnd_6518495 : Nat := 4983230072969 + 3 ^ 40 * 6518495 * 2
def baseEnd_6518495 : Nat := 1115707026309859697344831

theorem tailTrace_6518495 : CollatzResearch.WordTrace tailWord_6518495 prefixEnd_6518495 1115707026309859697344831 := by
  unfold tailWord_6518495
  simp only [CollatzResearch.WordTrace]
  refine ⟨237749044519613360159132939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158499363013075573439421959 237749044519613360159132939)
  ·
    refine ⟨356623566779420040238699409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237749044519613360159132939 356623566779420040238699409)
    ·
      refine ⟨267467675084565030179024557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356623566779420040238699409 267467675084565030179024557)
      ·
        refine ⟨100300378156711886317134209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267467675084565030179024557 100300378156711886317134209)
        ·
          refine ⟨75225283617533914737850657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100300378156711886317134209 75225283617533914737850657)
          ·
            refine ⟨56418962713150436053387993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75225283617533914737850657 56418962713150436053387993)
            ·
              refine ⟨42314222034862827040040995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56418962713150436053387993 42314222034862827040040995)
              ·
                refine ⟨63471333052294240560061493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42314222034862827040040995 63471333052294240560061493)
                ·
                  refine ⟨5950437473652585052505765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63471333052294240560061493 5950437473652585052505765)
                  ·
                    refine ⟨1115707026309859697344831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5950437473652585052505765 1115707026309859697344831)
                    ·
                      rfl

theorem cell23_6518495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 5, 4].length) (baseStart_6518495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518495 prefixEnd_6518495 := by exact prefixLift 6518495
  have htrace : WordTrace (prefixWord ++ tailWord_6518495) baseStart_6518495 baseEnd_6518495 := by
    simpa [prefixWord, tailWord_6518495, baseEnd_6518495] using wordTrace_append hprefix tailTrace_6518495
  have hstable : (prefixWord ++ tailWord_6518495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518495).length < 2 ^ (prefixWord ++ tailWord_6518495).sum := by decide
  have hdescent : baseEnd_6518495 < baseStart_6518495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518508 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 10]
def baseStart_6518508 : Nat := 118140960795 + 6518508 * 2 ^ 59
def prefixEnd_6518508 : Nat := 4983230072969 + 3 ^ 40 * 6518508 * 2
def baseEnd_6518508 : Nat := 371903083797565282352437

theorem tailTrace_6518508 : CollatzResearch.WordTrace tailWord_6518508 prefixEnd_6518508 371903083797565282352437 := by
  unfold tailWord_6518508
  simp only [CollatzResearch.WordTrace]
  refine ⟨118874759334283131689678089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158499679112377508919570785 118874759334283131689678089)
  ·
    refine ⟨89156069500712348767258567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118874759334283131689678089 89156069500712348767258567)
    ·
      refine ⟨133734104251068523150887851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89156069500712348767258567 133734104251068523150887851)
      ·
        refine ⟨200601156376602784726331777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133734104251068523150887851 200601156376602784726331777)
        ·
          refine ⟨150450867282452088544748833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200601156376602784726331777 150450867282452088544748833)
          ·
            refine ⟨112838150461839066408561625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150450867282452088544748833 112838150461839066408561625)
            ·
              refine ⟨84628612846379299806421219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 112838150461839066408561625 84628612846379299806421219)
              ·
                refine ⟨126942919269568949709631829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84628612846379299806421219 126942919269568949709631829)
                ·
                  refine ⟨371903083797565282352437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 126942919269568949709631829 371903083797565282352437)
                  ·
                    rfl

theorem cell23_6518508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 10].length) (baseStart_6518508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518508 prefixEnd_6518508 := by exact prefixLift 6518508
  have htrace : WordTrace (prefixWord ++ tailWord_6518508) baseStart_6518508 baseEnd_6518508 := by
    simpa [prefixWord, tailWord_6518508, baseEnd_6518508] using wordTrace_append hprefix tailTrace_6518508
  have hstable : (prefixWord ++ tailWord_6518508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518508).length < 2 ^ (prefixWord ++ tailWord_6518508).sum := by decide
  have hdescent : baseEnd_6518508 < baseStart_6518508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518528 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 8]
def baseStart_6518528 : Nat := 118140960795 + 6518528 * 2 ^ 59
def prefixEnd_6518528 : Nat := 4983230072969 + 3 ^ 40 * 6518528 * 2
def baseEnd_6518528 : Nat := 3347138023791177462921841

theorem tailTrace_6518528 : CollatzResearch.WordTrace tailWord_6518528 prefixEnd_6518528 3347138023791177462921841 := by
  unfold tailWord_6518528
  simp only [CollatzResearch.WordTrace]
  refine ⟨118875124064246903397542119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158500165418995871196722825 118875124064246903397542119)
  ·
    refine ⟨178312686096370355096313179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118875124064246903397542119 178312686096370355096313179)
    ·
      refine ⟨267469029144555532644469769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178312686096370355096313179 267469029144555532644469769)
      ·
        refine ⟨200601771858416649483352327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267469029144555532644469769 200601771858416649483352327)
        ·
          refine ⟨300902657787624974225028491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200601771858416649483352327 300902657787624974225028491)
          ·
            refine ⟨451353986681437461337542737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300902657787624974225028491 451353986681437461337542737)
            ·
              refine ⟨338515490011078096003157053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451353986681437461337542737 338515490011078096003157053)
              ·
                refine ⟨126943308754154286001183895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338515490011078096003157053 126943308754154286001183895)
                ·
                  refine ⟨190414963131231429001775843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126943308754154286001183895 190414963131231429001775843)
                  ·
                    refine ⟨285622444696847143502663765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 190414963131231429001775843 285622444696847143502663765)
                    ·
                      refine ⟨3347138023791177462921841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 285622444696847143502663765 3347138023791177462921841)
                      ·
                        rfl

theorem cell23_6518528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_6518528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518528 prefixEnd_6518528 := by exact prefixLift 6518528
  have htrace : WordTrace (prefixWord ++ tailWord_6518528) baseStart_6518528 baseEnd_6518528 := by
    simpa [prefixWord, tailWord_6518528, baseEnd_6518528] using wordTrace_append hprefix tailTrace_6518528
  have hstable : (prefixWord ++ tailWord_6518528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518528).length < 2 ^ (prefixWord ++ tailWord_6518528).sum := by decide
  have hdescent : baseEnd_6518528 < baseStart_6518528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518552 : List Nat := [2, 1, 2, 3, 1, 1, 3, 1, 5, 1, 3]
def baseStart_6518552 : Nat := 118140960795 + 6518552 * 2 ^ 59
def prefixEnd_6518552 : Nat := 4983230072969 + 3 ^ 40 * 6518552 * 2
def baseEnd_6518552 : Nat := 3347150347326885369021731

theorem tailTrace_6518552 : CollatzResearch.WordTrace tailWord_6518552 prefixEnd_6518552 3347150347326885369021731 := by
  unfold tailWord_6518552
  simp only [CollatzResearch.WordTrace]
  refine ⟨118875561740203429446978955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158500748986937905929305273 118875561740203429446978955)
  ·
    refine ⟨178313342610305144170468433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118875561740203429446978955 178313342610305144170468433)
    ·
      refine ⟨133735006957728858127851325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178313342610305144170468433 133735006957728858127851325)
      ·
        refine ⟨50150627609148321797944247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133735006957728858127851325 50150627609148321797944247)
        ·
          refine ⟨75225941413722482696916371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50150627609148321797944247 75225941413722482696916371)
          ·
            refine ⟨112838912120583724045374557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75225941413722482696916371 112838912120583724045374557)
            ·
              refine ⟨42314592045218896517015459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 112838912120583724045374557 42314592045218896517015459)
              ·
                refine ⟨63471888067828344775523189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42314592045218896517015459 63471888067828344775523189)
                ·
                  refine ⟨5950489506358907322705299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63471888067828344775523189 5950489506358907322705299)
                  ·
                    refine ⟨8925734259538360984057949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5950489506358907322705299 8925734259538360984057949)
                    ·
                      refine ⟨3347150347326885369021731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8925734259538360984057949 3347150347326885369021731)
                      ·
                        rfl

theorem cell23_6518552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_6518552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518552 prefixEnd_6518552 := by exact prefixLift 6518552
  have htrace : WordTrace (prefixWord ++ tailWord_6518552) baseStart_6518552 baseEnd_6518552 := by
    simpa [prefixWord, tailWord_6518552, baseEnd_6518552] using wordTrace_append hprefix tailTrace_6518552
  have hstable : (prefixWord ++ tailWord_6518552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518552).length < 2 ^ (prefixWord ++ tailWord_6518552).sum := by decide
  have hdescent : baseEnd_6518552 < baseStart_6518552 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518572 : List Nat := [2, 2, 1, 1, 1, 6, 1, 3, 1, 5]
def baseStart_6518572 : Nat := 118140960795 + 6518572 * 2 ^ 59
def prefixEnd_6518572 : Nat := 4983230072969 + 3 ^ 40 * 6518572 * 2
def baseEnd_6518572 : Nat := 1115720205646658430257213

theorem tailTrace_6518572 : CollatzResearch.WordTrace tailWord_6518572 prefixEnd_6518572 1115720205646658430257213 := by
  unfold tailWord_6518572
  simp only [CollatzResearch.WordTrace]
  refine ⟨118875926470167201154842985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158501235293556268206457313 118875926470167201154842985)
  ·
    refine ⟨89156944852625400866132239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118875926470167201154842985 89156944852625400866132239)
    ·
      refine ⟨133735417278938101299198359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89156944852625400866132239 133735417278938101299198359)
      ·
        refine ⟨200603125918407151948797539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133735417278938101299198359 200603125918407151948797539)
        ·
          refine ⟨300904688877610727923196309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200603125918407151948797539 300904688877610727923196309)
          ·
            refine ⟨14104907291138002871399827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 300904688877610727923196309 14104907291138002871399827)
            ·
              refine ⟨21157360936707004307099741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14104907291138002871399827 21157360936707004307099741)
              ·
                refine ⟨7934010351265126615162403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21157360936707004307099741 7934010351265126615162403)
                ·
                  refine ⟨11901015526897689922743605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7934010351265126615162403 11901015526897689922743605)
                  ·
                    refine ⟨1115720205646658430257213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11901015526897689922743605 1115720205646658430257213)
                    ·
                      rfl

theorem cell23_6518572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_6518572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518572 prefixEnd_6518572 := by exact prefixLift 6518572
  have htrace : WordTrace (prefixWord ++ tailWord_6518572) baseStart_6518572 baseEnd_6518572 := by
    simpa [prefixWord, tailWord_6518572, baseEnd_6518572] using wordTrace_append hprefix tailTrace_6518572
  have hstable : (prefixWord ++ tailWord_6518572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518572).length < 2 ^ (prefixWord ++ tailWord_6518572).sum := by decide
  have hdescent : baseEnd_6518572 < baseStart_6518572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518586 : List Nat := [3, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3]
def baseStart_6518586 : Nat := 118140960795 + 6518586 * 2 ^ 59
def prefixEnd_6518586 : Nat := 4983230072969 + 3 ^ 40 * 6518586 * 2
def baseEnd_6518586 : Nat := 3347167805669138235996575

theorem tailTrace_6518586 : CollatzResearch.WordTrace tailWord_6518586 prefixEnd_6518586 3347167805669138235996575 := by
  unfold tailWord_6518586
  simp only [CollatzResearch.WordTrace]
  refine ⟨59438090890570920675173903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158501575708189121800463741 59438090890570920675173903)
  ·
    refine ⟨89157136335856381012760855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59438090890570920675173903 89157136335856381012760855)
    ·
      refine ⟨133735704503784571519141283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89157136335856381012760855 133735704503784571519141283)
      ·
        refine ⟨200603556755676857278711925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133735704503784571519141283 200603556755676857278711925)
        ·
          refine ⟨18806583445844705369879243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200603556755676857278711925 18806583445844705369879243)
          ·
            refine ⟨28209875168767058054818865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18806583445844705369879243 28209875168767058054818865)
            ·
              refine ⟨21157406376575293541114149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28209875168767058054818865 21157406376575293541114149)
              ·
                refine ⟨3967013695607867538958903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21157406376575293541114149 3967013695607867538958903)
                ·
                  refine ⟨5950520543411801308438355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967013695607867538958903 5950520543411801308438355)
                  ·
                    refine ⟨8925780815117701962657533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5950520543411801308438355 8925780815117701962657533)
                    ·
                      refine ⟨3347167805669138235996575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8925780815117701962657533 3347167805669138235996575)
                      ·
                        rfl

theorem cell23_6518586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 4, 1, 1, 3].length) (baseStart_6518586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518586 prefixEnd_6518586 := by exact prefixLift 6518586
  have htrace : WordTrace (prefixWord ++ tailWord_6518586) baseStart_6518586 baseEnd_6518586 := by
    simpa [prefixWord, tailWord_6518586, baseEnd_6518586] using wordTrace_append hprefix tailTrace_6518586
  have hstable : (prefixWord ++ tailWord_6518586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518586).length < 2 ^ (prefixWord ++ tailWord_6518586).sum := by decide
  have hdescent : baseEnd_6518586 < baseStart_6518586 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518595 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 5]
def baseStart_6518595 : Nat := 118140960795 + 6518595 * 2 ^ 59
def prefixEnd_6518595 : Nat := 4983230072969 + 3 ^ 40 * 6518595 * 2
def baseEnd_6518595 : Nat := 3347172426995028700784033

theorem tailTrace_6518595 : CollatzResearch.WordTrace tailWord_6518595 prefixEnd_6518595 3347172426995028700784033 := by
  unfold tailWord_6518595
  simp only [CollatzResearch.WordTrace]
  refine ⟨237752691819251077237773239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158501794546167384825182159 237752691819251077237773239)
  ·
    refine ⟨356629037728876615856659859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237752691819251077237773239 356629037728876615856659859)
    ·
      refine ⟨534943556593314923784989789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356629037728876615856659859 534943556593314923784989789)
      ·
        refine ⟨200603833722493096419371171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 534943556593314923784989789 200603833722493096419371171)
        ·
          refine ⟨300905750583739644629056757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200603833722493096419371171 300905750583739644629056757)
          ·
            refine ⟨28209914117225591683974071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 300905750583739644629056757 28209914117225591683974071)
            ·
              refine ⟨42314871175838387525961107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28209914117225591683974071 42314871175838387525961107)
              ·
                refine ⟨63472306763757581288941661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42314871175838387525961107 63472306763757581288941661)
                ·
                  refine ⟨23802115036409092983353123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63472306763757581288941661 23802115036409092983353123)
                  ·
                    refine ⟨35703172554613639475029685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23802115036409092983353123 35703172554613639475029685)
                    ·
                      refine ⟨3347172426995028700784033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35703172554613639475029685 3347172426995028700784033)
                      ·
                        rfl

theorem cell23_6518595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_6518595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518595 prefixEnd_6518595 := by exact prefixLift 6518595
  have htrace : WordTrace (prefixWord ++ tailWord_6518595) baseStart_6518595 baseEnd_6518595 := by
    simpa [prefixWord, tailWord_6518595, baseEnd_6518595] using wordTrace_append hprefix tailTrace_6518595
  have hstable : (prefixWord ++ tailWord_6518595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518595).length < 2 ^ (prefixWord ++ tailWord_6518595).sum := by decide
  have hdescent : baseEnd_6518595 < baseStart_6518595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518609 : List Nat := [1, 2, 2, 1, 5, 2, 2, 2, 1, 1, 4]
def baseStart_6518609 : Nat := 118140960795 + 6518609 * 2 ^ 59
def prefixEnd_6518609 : Nat := 4983230072969 + 3 ^ 40 * 6518609 * 2
def baseEnd_6518609 : Nat := 3347179615724191646008969

theorem tailTrace_6518609 : CollatzResearch.WordTrace tailWord_6518609 prefixEnd_6518609 3347179615724191646008969 := by
  unfold tailWord_6518609
  simp only [CollatzResearch.WordTrace]
  refine ⟨237753202441200357628782881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158502134960800238419188587 237753202441200357628782881)
  ·
    refine ⟨178314901830900268221587161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237753202441200357628782881 178314901830900268221587161)
    ·
      refine ⟨133736176373175201166190371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178314901830900268221587161 133736176373175201166190371)
      ·
        refine ⟨200604264559762801749285557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133736176373175201166190371 200604264559762801749285557)
        ·
          refine ⟨18806649802477762663995521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 200604264559762801749285557 18806649802477762663995521)
          ·
            refine ⟨14104987351858321997996641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18806649802477762663995521 14104987351858321997996641)
            ·
              refine ⟨10578740513893741498497481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14104987351858321997996641 10578740513893741498497481)
              ·
                refine ⟨7934055385420306123873111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10578740513893741498497481 7934055385420306123873111)
                ·
                  refine ⟨11901083078130459185809667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7934055385420306123873111 11901083078130459185809667)
                  ·
                    refine ⟨17851624617195688778714501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11901083078130459185809667 17851624617195688778714501)
                    ·
                      refine ⟨3347179615724191646008969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17851624617195688778714501 3347179615724191646008969)
                      ·
                        rfl

theorem cell23_6518609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 2, 2, 1, 1, 4].length) (baseStart_6518609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518609 prefixEnd_6518609 := by exact prefixLift 6518609
  have htrace : WordTrace (prefixWord ++ tailWord_6518609) baseStart_6518609 baseEnd_6518609 := by
    simpa [prefixWord, tailWord_6518609, baseEnd_6518609] using wordTrace_append hprefix tailTrace_6518609
  have hstable : (prefixWord ++ tailWord_6518609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518609).length < 2 ^ (prefixWord ++ tailWord_6518609).sum := by decide
  have hdescent : baseEnd_6518609 < baseStart_6518609 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518620 : List Nat := [2, 2, 4, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_6518620 : Nat := 118140960795 + 6518620 * 2 ^ 59
def prefixEnd_6518620 : Nat := 4983230072969 + 3 ^ 40 * 6518620 * 2
def baseEnd_6518620 : Nat := 3347185264011391102971419

theorem tailTrace_6518620 : CollatzResearch.WordTrace tailWord_6518620 prefixEnd_6518620 3347185264011391102971419 := by
  unfold tailWord_6518620
  simp only [CollatzResearch.WordTrace]
  refine ⟨118876801822080253253716657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158502402429440337671622209 118876801822080253253716657)
  ·
    refine ⟨89157601366560189940287493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118876801822080253253716657 89157601366560189940287493)
    ·
      refine ⟨16717050256230035613803905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89157601366560189940287493 16717050256230035613803905)
      ·
        refine ⟨12537787692172526710352929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16717050256230035613803905 12537787692172526710352929)
        ·
          refine ⟨9403340769129395032764697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12537787692172526710352929 9403340769129395032764697)
          ·
            refine ⟨7052505576847046274573523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9403340769129395032764697 7052505576847046274573523)
            ·
              refine ⟨10578758365270569411860285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7052505576847046274573523 10578758365270569411860285)
              ·
                refine ⟨3967034386976463529447607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10578758365270569411860285 3967034386976463529447607)
                ·
                  refine ⟨5950551580464695294171411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967034386976463529447607 5950551580464695294171411)
                  ·
                    refine ⟨8925827370697042941257117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5950551580464695294171411 8925827370697042941257117)
                    ·
                      refine ⟨3347185264011391102971419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8925827370697042941257117 3347185264011391102971419)
                      ·
                        rfl

theorem cell23_6518620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_6518620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518620 prefixEnd_6518620 := by exact prefixLift 6518620
  have htrace : WordTrace (prefixWord ++ tailWord_6518620) baseStart_6518620 baseEnd_6518620 := by
    simpa [prefixWord, tailWord_6518620, baseEnd_6518620] using wordTrace_append hprefix tailTrace_6518620
  have hstable : (prefixWord ++ tailWord_6518620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518620).length < 2 ^ (prefixWord ++ tailWord_6518620).sum := by decide
  have hdescent : baseEnd_6518620 < baseStart_6518620 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518652 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 1, 9, 2]
def baseStart_6518652 : Nat := 118140960795 + 6518652 * 2 ^ 59
def prefixEnd_6518652 : Nat := 4983230072969 + 3 ^ 40 * 6518652 * 2
def baseEnd_6518652 : Nat := 3347201695392334977771271

theorem tailTrace_6518652 : CollatzResearch.WordTrace tailWord_6518652 prefixEnd_6518652 3347201695392334977771271 := by
  unfold tailWord_6518652
  simp only [CollatzResearch.WordTrace]
  refine ⟨118877385390022287986299105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158503180520029717315065473 118877385390022287986299105)
  ·
    refine ⟨89158039042516715989724329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118877385390022287986299105 89158039042516715989724329)
    ·
      refine ⟨66868529281887536992293247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89158039042516715989724329 66868529281887536992293247)
      ·
        refine ⟨100302793922831305488439871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66868529281887536992293247 100302793922831305488439871)
        ·
          refine ⟨150454190884246958232659807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100302793922831305488439871 150454190884246958232659807)
          ·
            refine ⟨225681286326370437348989711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150454190884246958232659807 225681286326370437348989711)
            ·
              refine ⟨338521929489555656023484567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225681286326370437348989711 338521929489555656023484567)
              ·
                refine ⟨507782894234333484035226851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338521929489555656023484567 507782894234333484035226851)
                ·
                  refine ⟨761674341351500226052840277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507782894234333484035226851 761674341351500226052840277)
                  ·
                    refine ⟨4462935593856446637028361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 761674341351500226052840277 4462935593856446637028361)
                    ·
                      refine ⟨3347201695392334977771271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4462935593856446637028361 3347201695392334977771271)
                      ·
                        rfl

theorem cell23_6518652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_6518652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518652 prefixEnd_6518652 := by exact prefixLift 6518652
  have htrace : WordTrace (prefixWord ++ tailWord_6518652) baseStart_6518652 baseEnd_6518652 := by
    simpa [prefixWord, tailWord_6518652, baseEnd_6518652] using wordTrace_append hprefix tailTrace_6518652
  have hstable : (prefixWord ++ tailWord_6518652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518652).length < 2 ^ (prefixWord ++ tailWord_6518652).sum := by decide
  have hdescent : baseEnd_6518652 < baseStart_6518652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518663 : List Nat := [1, 1, 4, 2, 5, 1, 1, 2, 1, 2, 3]
def baseStart_6518663 : Nat := 118140960795 + 6518663 * 2 ^ 59
def prefixEnd_6518663 : Nat := 4983230072969 + 3 ^ 40 * 6518663 * 2
def baseEnd_6518663 : Nat := 3347207343679534434733721

theorem tailTrace_6518663 : CollatzResearch.WordTrace tailWord_6518663 prefixEnd_6518663 3347207343679534434733721 := by
  unfold tailWord_6518663
  simp only [CollatzResearch.WordTrace]
  refine ⟨237755171983004724851248643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158503447988669816567499095 237755171983004724851248643)
  ·
    refine ⟨356632757974507087276872965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237755171983004724851248643 356632757974507087276872965)
    ·
      refine ⟨66868642120220078864413681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 356632757974507087276872965 66868642120220078864413681)
      ·
        refine ⟨50151481590165059148310261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66868642120220078864413681 50151481590165059148310261)
        ·
          refine ⟨4701701399077974295154087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50151481590165059148310261 4701701399077974295154087)
          ·
            refine ⟨7052552098616961442731131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4701701399077974295154087 7052552098616961442731131)
            ·
              refine ⟨10578828147925442164096697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7052552098616961442731131 10578828147925442164096697)
              ·
                refine ⟨7934121110944081623072523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10578828147925442164096697 7934121110944081623072523)
                ·
                  refine ⟨11901181666416122434608785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7934121110944081623072523 11901181666416122434608785)
                  ·
                    refine ⟨8925886249812091825956589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11901181666416122434608785 8925886249812091825956589)
                    ·
                      refine ⟨3347207343679534434733721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8925886249812091825956589 3347207343679534434733721)
                      ·
                        rfl

theorem cell23_6518663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_6518663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518663 prefixEnd_6518663 := by exact prefixLift 6518663
  have htrace : WordTrace (prefixWord ++ tailWord_6518663) baseStart_6518663 baseEnd_6518663 := by
    simpa [prefixWord, tailWord_6518663, baseEnd_6518663] using wordTrace_append hprefix tailTrace_6518663
  have hstable : (prefixWord ++ tailWord_6518663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518663).length < 2 ^ (prefixWord ++ tailWord_6518663).sum := by decide
  have hdescent : baseEnd_6518663 < baseStart_6518663 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518712 : List Nat := [2, 1, 2, 1, 2, 3, 3, 1, 2, 2, 4]
def baseStart_6518712 : Nat := 118140960795 + 6518712 * 2 ^ 59
def prefixEnd_6518712 : Nat := 4983230072969 + 3 ^ 40 * 6518712 * 2
def baseEnd_6518712 : Nat := 3347232504231604743020995

theorem tailTrace_6518712 : CollatzResearch.WordTrace tailWord_6518712 prefixEnd_6518712 3347232504231604743020995 := by
  unfold tailWord_6518712
  simp only [CollatzResearch.WordTrace]
  refine ⟨118878479579913603109891195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158504639439884804146521593 118878479579913603109891195)
  ·
    refine ⟨178317719369870404664836793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118878479579913603109891195 178317719369870404664836793)
    ·
      refine ⟨133738289527402803498627595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178317719369870404664836793 133738289527402803498627595)
      ·
        refine ⟨200607434291104205247941393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133738289527402803498627595 200607434291104205247941393)
        ·
          refine ⟨150455575718328153935956045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200607434291104205247941393 150455575718328153935956045)
          ·
            refine ⟨56420840894373057725983517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150455575718328153935956045 56420840894373057725983517)
            ·
              refine ⟨21157815335389896647243819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56420840894373057725983517 21157815335389896647243819)
              ·
                refine ⟨31736723003084844970865729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21157815335389896647243819 31736723003084844970865729)
                ·
                  refine ⟨23802542252313633728149297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31736723003084844970865729 23802542252313633728149297)
                  ·
                    refine ⟨17851906689235225296111973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23802542252313633728149297 17851906689235225296111973)
                    ·
                      refine ⟨3347232504231604743020995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17851906689235225296111973 3347232504231604743020995)
                      ·
                        rfl

theorem cell23_6518712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 3, 1, 2, 2, 4].length) (baseStart_6518712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518712 prefixEnd_6518712 := by exact prefixLift 6518712
  have htrace : WordTrace (prefixWord ++ tailWord_6518712) baseStart_6518712 baseEnd_6518712 := by
    simpa [prefixWord, tailWord_6518712, baseEnd_6518712] using wordTrace_append hprefix tailTrace_6518712
  have hstable : (prefixWord ++ tailWord_6518712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518712).length < 2 ^ (prefixWord ++ tailWord_6518712).sum := by decide
  have hdescent : baseEnd_6518712 < baseStart_6518712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518752 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 2, 5]
def baseStart_6518752 : Nat := 118140960795 + 6518752 * 2 ^ 59
def prefixEnd_6518752 : Nat := 4983230072969 + 3 ^ 40 * 6518752 * 2
def baseEnd_6518752 : Nat := 1115751014485928195506937

theorem tailTrace_6518752 : CollatzResearch.WordTrace tailWord_6518752 prefixEnd_6518752 1115751014485928195506937 := by
  unfold tailWord_6518752
  simp only [CollatzResearch.WordTrace]
  refine ⟨118879209039841146525619255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158505612053121528700825673 118879209039841146525619255)
  ·
    refine ⟨178318813559761719788428883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118879209039841146525619255 178318813559761719788428883)
    ·
      refine ⟨267478220339642579682643325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178318813559761719788428883 267478220339642579682643325)
      ·
        refine ⟨100304332627365967380991247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267478220339642579682643325 100304332627365967380991247)
        ·
          refine ⟨150456498941048951071486871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100304332627365967380991247 150456498941048951071486871)
          ·
            refine ⟨225684748411573426607230307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150456498941048951071486871 225684748411573426607230307)
            ·
              refine ⟨338527122617360139910845461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225684748411573426607230307 338527122617360139910845461)
              ·
                refine ⟨15868458872688756558320881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 338527122617360139910845461 15868458872688756558320881)
                ·
                  refine ⟨11901344154516567418740661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15868458872688756558320881 11901344154516567418740661)
                  ·
                    refine ⟨1115751014485928195506937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11901344154516567418740661 1115751014485928195506937)
                    ·
                      rfl

theorem cell23_6518752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 2, 5].length) (baseStart_6518752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518752 prefixEnd_6518752 := by exact prefixLift 6518752
  have htrace : WordTrace (prefixWord ++ tailWord_6518752) baseStart_6518752 baseEnd_6518752 := by
    simpa [prefixWord, tailWord_6518752, baseEnd_6518752] using wordTrace_append hprefix tailTrace_6518752
  have hstable : (prefixWord ++ tailWord_6518752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518752).length < 2 ^ (prefixWord ++ tailWord_6518752).sum := by decide
  have hdescent : baseEnd_6518752 < baseStart_6518752 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518762 : List Nat := [3, 1, 3, 1, 2, 1, 2, 1, 1, 1, 7]
def baseStart_6518762 : Nat := 118140960795 + 6518762 * 2 ^ 59
def prefixEnd_6518762 : Nat := 4983230072969 + 3 ^ 40 * 6518762 * 2
def baseEnd_6518762 : Nat := 3347258178264329547395765

theorem tailTrace_6518762 : CollatzResearch.WordTrace tailWord_6518762 prefixEnd_6518762 3347258178264329547395765 := by
  unfold tailWord_6518762
  simp only [CollatzResearch.WordTrace]
  refine ⟨59439695702411516189775635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158505855206430709839401693 59439695702411516189775635)
  ·
    refine ⟨89159543553617274284663453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59439695702411516189775635 89159543553617274284663453)
    ·
      refine ⟨33434828832606477856748795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89159543553617274284663453 33434828832606477856748795)
      ·
        refine ⟨50152243248909716785123193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33434828832606477856748795 50152243248909716785123193)
        ·
          refine ⟨37614182436682287588842395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50152243248909716785123193 37614182436682287588842395)
          ·
            refine ⟨56421273655023431383263593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37614182436682287588842395 56421273655023431383263593)
            ·
              refine ⟨42315955241267573537447695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56421273655023431383263593 42315955241267573537447695)
              ·
                refine ⟨63473932861901360306171543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42315955241267573537447695 63473932861901360306171543)
                ·
                  refine ⟨95210899292852040459257315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63473932861901360306171543 95210899292852040459257315)
                  ·
                    refine ⟨142816348939278060688885973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95210899292852040459257315 142816348939278060688885973)
                    ·
                      refine ⟨3347258178264329547395765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142816348939278060688885973 3347258178264329547395765)
                      ·
                        rfl

theorem cell23_6518762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 1, 1, 1, 7].length) (baseStart_6518762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518762 prefixEnd_6518762 := by exact prefixLift 6518762
  have htrace : WordTrace (prefixWord ++ tailWord_6518762) baseStart_6518762 baseEnd_6518762 := by
    simpa [prefixWord, tailWord_6518762, baseEnd_6518762] using wordTrace_append hprefix tailTrace_6518762
  have hstable : (prefixWord ++ tailWord_6518762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518762).length < 2 ^ (prefixWord ++ tailWord_6518762).sum := by decide
  have hdescent : baseEnd_6518762 < baseStart_6518762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518873 : List Nat := [1, 2, 1, 2, 2, 1, 5, 4, 1, 1, 3]
def baseStart_6518873 : Nat := 118140960795 + 6518873 * 2 ^ 59
def prefixEnd_6518873 : Nat := 4983230072969 + 3 ^ 40 * 6518873 * 2
def baseEnd_6518873 : Nat := 3347315174616978613107755

theorem tailTrace_6518873 : CollatzResearch.WordTrace tailWord_6518873 prefixEnd_6518873 3347315174616978613107755 := by
  unfold tailWord_6518873
  simp only [CollatzResearch.WordTrace]
  refine ⟨237762831312243930716393273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158508554208162620477595515 237762831312243930716393273)
  ·
    refine ⟨178322123484182948037294955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237762831312243930716393273 178322123484182948037294955)
    ·
      refine ⟨267483185226274422055942433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178322123484182948037294955 267483185226274422055942433)
      ·
        refine ⟨200612388919705816541956825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267483185226274422055942433 200612388919705816541956825)
        ·
          refine ⟨150459291689779362406467619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200612388919705816541956825 150459291689779362406467619)
          ·
            refine ⟨225688937534669043609701429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150459291689779362406467619 225688937534669043609701429)
            ·
              refine ⟨21158337893875222838409509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 225688937534669043609701429 21158337893875222838409509)
              ·
                refine ⟨3967188355101604282201783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21158337893875222838409509 3967188355101604282201783)
                ·
                  refine ⟨5950782532652406423302675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967188355101604282201783 5950782532652406423302675)
                  ·
                    refine ⟨8926173798978609634954013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5950782532652406423302675 8926173798978609634954013)
                    ·
                      refine ⟨3347315174616978613107755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8926173798978609634954013 3347315174616978613107755)
                      ·
                        rfl

theorem cell23_6518873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 5, 4, 1, 1, 3].length) (baseStart_6518873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518873 prefixEnd_6518873 := by exact prefixLift 6518873
  have htrace : WordTrace (prefixWord ++ tailWord_6518873) baseStart_6518873 baseEnd_6518873 := by
    simpa [prefixWord, tailWord_6518873, baseEnd_6518873] using wordTrace_append hprefix tailTrace_6518873
  have hstable : (prefixWord ++ tailWord_6518873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518873).length < 2 ^ (prefixWord ++ tailWord_6518873).sum := by decide
  have hdescent : baseEnd_6518873 < baseStart_6518873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518889 : List Nat := [1, 2, 1, 1, 1, 5, 4, 1, 1, 6]
def baseStart_6518889 : Nat := 118140960795 + 6518889 * 2 ^ 59
def prefixEnd_6518889 : Nat := 4983230072969 + 3 ^ 40 * 6518889 * 2
def baseEnd_6518889 : Nat := 1115774463435816850169227

theorem tailTrace_6518889 : CollatzResearch.WordTrace tailWord_6518889 prefixEnd_6518889 1115774463435816850169227 := by
  unfold tailWord_6518889
  simp only [CollatzResearch.WordTrace]
  refine ⟨237763414880185965448975721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158508943253457310299317147 237763414880185965448975721)
  ·
    refine ⟨178322561160139474086731791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237763414880185965448975721 178322561160139474086731791)
    ·
      refine ⟨267483841740209211130097687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178322561160139474086731791 267483841740209211130097687)
      ·
        refine ⟨401225762610313816695146531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267483841740209211130097687 401225762610313816695146531)
        ·
          refine ⟨601838643915470725042719797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401225762610313816695146531 601838643915470725042719797)
          ·
            refine ⟨56422372867075380472754981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 601838643915470725042719797 56422372867075380472754981)
            ·
              refine ⟨10579194912576633838641559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56422372867075380472754981 10579194912576633838641559)
              ·
                refine ⟨15868792368864950757962339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10579194912576633838641559 15868792368864950757962339)
                ·
                  refine ⟨23803188553297426136943509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15868792368864950757962339 23803188553297426136943509)
                  ·
                    refine ⟨1115774463435816850169227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23803188553297426136943509 1115774463435816850169227)
                    ·
                      rfl

theorem cell23_6518889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 6].length) (baseStart_6518889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518889 prefixEnd_6518889 := by exact prefixLift 6518889
  have htrace : WordTrace (prefixWord ++ tailWord_6518889) baseStart_6518889 baseEnd_6518889 := by
    simpa [prefixWord, tailWord_6518889, baseEnd_6518889] using wordTrace_append hprefix tailTrace_6518889
  have hstable : (prefixWord ++ tailWord_6518889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518889).length < 2 ^ (prefixWord ++ tailWord_6518889).sum := by decide
  have hdescent : baseEnd_6518889 < baseStart_6518889 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518913 : List Nat := [1, 2, 4, 2, 3, 1, 1, 3, 1, 1, 4]
def baseStart_6518913 : Nat := 118140960795 + 6518913 * 2 ^ 59
def prefixEnd_6518913 : Nat := 4983230072969 + 3 ^ 40 * 6518913 * 2
def baseEnd_6518913 : Nat := 3347335713843158456607571

theorem tailTrace_6518913 : CollatzResearch.WordTrace tailWord_6518913 prefixEnd_6518913 3347335713843158456607571 := by
  unfold tailWord_6518913
  simp only [CollatzResearch.WordTrace]
  refine ⟨237764290232099017547849393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158509526821399345031899595 237764290232099017547849393)
  ·
    refine ⟨178323217674074263160887045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237764290232099017547849393 178323217674074263160887045)
    ·
      refine ⟨33435603313888924342666321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178323217674074263160887045 33435603313888924342666321)
      ·
        refine ⟨25076702485416693256999741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33435603313888924342666321 25076702485416693256999741)
        ·
          refine ⟨9403763432031259971374903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25076702485416693256999741 9403763432031259971374903)
          ·
            refine ⟨14105645148046889957062355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9403763432031259971374903 14105645148046889957062355)
            ·
              refine ⟨21158467722070334935593533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14105645148046889957062355 21158467722070334935593533)
              ·
                refine ⟨7934425395776375600847575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21158467722070334935593533 7934425395776375600847575)
                ·
                  refine ⟨11901638093664563401271363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7934425395776375600847575 11901638093664563401271363)
                  ·
                    refine ⟨17852457140496845101907045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11901638093664563401271363 17852457140496845101907045)
                    ·
                      refine ⟨3347335713843158456607571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17852457140496845101907045 3347335713843158456607571)
                      ·
                        rfl

theorem cell23_6518913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_6518913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518913 prefixEnd_6518913 := by exact prefixLift 6518913
  have htrace : WordTrace (prefixWord ++ tailWord_6518913) baseStart_6518913 baseEnd_6518913 := by
    simpa [prefixWord, tailWord_6518913, baseEnd_6518913] using wordTrace_append hprefix tailTrace_6518913
  have hstable : (prefixWord ++ tailWord_6518913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518913).length < 2 ^ (prefixWord ++ tailWord_6518913).sum := by decide
  have hdescent : baseEnd_6518913 < baseStart_6518913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518930 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 3, 2, 2]
def baseStart_6518930 : Nat := 118140960795 + 6518930 * 2 ^ 59
def prefixEnd_6518930 : Nat := 4983230072969 + 3 ^ 40 * 6518930 * 2
def baseEnd_6518930 : Nat := 3347344443014284890094993

theorem tailTrace_6518930 : CollatzResearch.WordTrace tailWord_6518930 prefixEnd_6518930 3347344443014284890094993 := by
  unfold tailWord_6518930
  simp only [CollatzResearch.WordTrace]
  refine ⟨59441227568259357362804561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158509940182024952967478829 59441227568259357362804561)
  ·
    refine ⟨44580920676194518022103421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59441227568259357362804561 44580920676194518022103421)
    ·
      refine ⟨16717845253572944258288783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44580920676194518022103421 16717845253572944258288783)
      ·
        refine ⟨25076767880359416387433175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16717845253572944258288783 25076767880359416387433175)
        ·
          refine ⟨37615151820539124581149763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25076767880359416387433175 37615151820539124581149763)
          ·
            refine ⟨56422727730808686871724645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37615151820539124581149763 56422727730808686871724645)
            ·
              refine ⟨10579261449526628788448371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56422727730808686871724645 10579261449526628788448371)
              ·
                refine ⟨15868892174289943182672557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10579261449526628788448371 15868892174289943182672557)
                ·
                  refine ⟨5950834565358728693502209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15868892174289943182672557 5950834565358728693502209)
                  ·
                    refine ⟨4463125924019046520126657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5950834565358728693502209 4463125924019046520126657)
                    ·
                      refine ⟨3347344443014284890094993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4463125924019046520126657 3347344443014284890094993)
                      ·
                        rfl

theorem cell23_6518930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_6518930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518930 prefixEnd_6518930 := by exact prefixLift 6518930
  have htrace : WordTrace (prefixWord ++ tailWord_6518930) baseStart_6518930 baseEnd_6518930 := by
    simpa [prefixWord, tailWord_6518930, baseEnd_6518930] using wordTrace_append hprefix tailTrace_6518930
  have hstable : (prefixWord ++ tailWord_6518930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518930).length < 2 ^ (prefixWord ++ tailWord_6518930).sum := by decide
  have hdescent : baseEnd_6518930 < baseStart_6518930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518943 : List Nat := [1, 1, 2, 6, 1, 3, 1, 1, 1, 2, 4]
def baseStart_6518943 : Nat := 118140960795 + 6518943 * 2 ^ 59
def prefixEnd_6518943 : Nat := 4983230072969 + 3 ^ 40 * 6518943 * 2
def baseEnd_6518943 : Nat := 3347351118262793339232433

theorem tailTrace_6518943 : CollatzResearch.WordTrace tailWord_6518943 prefixEnd_6518943 3347351118262793339232433 := by
  unfold tailWord_6518943
  simp only [CollatzResearch.WordTrace]
  refine ⟨237765384421990332671441483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158510256281326888447627655 237765384421990332671441483)
  ·
    refine ⟨356648076632985499007162225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237765384421990332671441483 356648076632985499007162225)
    ·
      refine ⟨267486057474739124255371669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356648076632985499007162225 267486057474739124255371669)
      ·
        refine ⟨12538408944128396449470547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 267486057474739124255371669 12538408944128396449470547)
        ·
          refine ⟨18807613416192594674205821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12538408944128396449470547 18807613416192594674205821)
          ·
            refine ⟨7052855031072223002827183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18807613416192594674205821 7052855031072223002827183)
            ·
              refine ⟨10579282546608334504240775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7052855031072223002827183 10579282546608334504240775)
              ·
                refine ⟨15868923819912501756361163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10579282546608334504240775 15868923819912501756361163)
                ·
                  refine ⟨23803385729868752634541745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15868923819912501756361163 23803385729868752634541745)
                  ·
                    refine ⟨17852539297401564475906309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23803385729868752634541745 17852539297401564475906309)
                    ·
                      refine ⟨3347351118262793339232433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17852539297401564475906309 3347351118262793339232433)
                      ·
                        rfl

theorem cell23_6518943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_6518943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518943 prefixEnd_6518943 := by exact prefixLift 6518943
  have htrace : WordTrace (prefixWord ++ tailWord_6518943) baseStart_6518943 baseEnd_6518943 := by
    simpa [prefixWord, tailWord_6518943, baseEnd_6518943] using wordTrace_append hprefix tailTrace_6518943
  have hstable : (prefixWord ++ tailWord_6518943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518943).length < 2 ^ (prefixWord ++ tailWord_6518943).sum := by decide
  have hdescent : baseEnd_6518943 < baseStart_6518943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518956 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 7, 3, 2]
def baseStart_6518956 : Nat := 118140960795 + 6518956 * 2 ^ 59
def prefixEnd_6518956 : Nat := 4983230072969 + 3 ^ 40 * 6518956 * 2
def baseEnd_6518956 : Nat := 3347357793511301788369873

theorem tailTrace_6518956 : CollatzResearch.WordTrace tailWord_6518956 prefixEnd_6518956 3347357793511301788369873 := by
  unfold tailWord_6518956
  simp only [CollatzResearch.WordTrace]
  refine ⟨118882929285471617945832361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158510572380628823927776481 118882929285471617945832361)
  ·
    refine ⟨89162196964103713459374271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118882929285471617945832361 89162196964103713459374271)
    ·
      refine ⟨133743295446155570189061407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89162196964103713459374271 133743295446155570189061407)
      ·
        refine ⟨200614943169233355283592111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133743295446155570189061407 200614943169233355283592111)
        ·
          refine ⟨300922414753850032925388167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200614943169233355283592111 300922414753850032925388167)
          ·
            refine ⟨451383622130775049388082251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300922414753850032925388167 451383622130775049388082251)
            ·
              refine ⟨677075433196162574082123377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451383622130775049388082251 677075433196162574082123377)
              ·
                refine ⟨507806574897121930561592533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677075433196162574082123377 507806574897121930561592533)
                ·
                  refine ⟨11901716599151295247537325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 507806574897121930561592533 11901716599151295247537325)
                  ·
                    refine ⟨4463143724681735717826497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11901716599151295247537325 4463143724681735717826497)
                    ·
                      refine ⟨3347357793511301788369873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4463143724681735717826497 3347357793511301788369873)
                      ·
                        rfl

theorem cell23_6518956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 3, 2].length) (baseStart_6518956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518956 prefixEnd_6518956 := by exact prefixLift 6518956
  have htrace : WordTrace (prefixWord ++ tailWord_6518956) baseStart_6518956 baseEnd_6518956 := by
    simpa [prefixWord, tailWord_6518956, baseEnd_6518956] using wordTrace_append hprefix tailTrace_6518956
  have hstable : (prefixWord ++ tailWord_6518956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518956).length < 2 ^ (prefixWord ++ tailWord_6518956).sum := by decide
  have hdescent : baseEnd_6518956 < baseStart_6518956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6518999 : List Nat := [1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 4]
def baseStart_6518999 : Nat := 118140960795 + 6518999 * 2 ^ 59
def prefixEnd_6518999 : Nat := 4983230072969 + 3 ^ 40 * 6518999 * 2
def baseEnd_6518999 : Nat := 3347379873179445120132175

theorem tailTrace_6518999 : CollatzResearch.WordTrace tailWord_6518999 prefixEnd_6518999 3347379873179445120132175 := by
  unfold tailWord_6518999
  simp only [CollatzResearch.WordTrace]
  refine ⟨237767426909787454235480051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158511617939858302823653367 237767426909787454235480051)
  ·
    refine ⟨356651140364681181353220077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237767426909787454235480051 356651140364681181353220077)
    ·
      refine ⟨133744177636755443007457529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356651140364681181353220077 133744177636755443007457529)
      ·
        refine ⟨100308133227566582255593147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133744177636755443007457529 100308133227566582255593147)
        ·
          refine ⟨150462199841349873383389721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100308133227566582255593147 150462199841349873383389721)
          ·
            refine ⟨112846649881012405037542291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150462199841349873383389721 112846649881012405037542291)
            ·
              refine ⟨169269974821518607556313437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112846649881012405037542291 169269974821518607556313437)
              ·
                refine ⟨63476240558069477833617539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169269974821518607556313437 63476240558069477833617539)
                ·
                  refine ⟨95214360837104216750426309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63476240558069477833617539 95214360837104216750426309)
                  ·
                    refine ⟨17852692656957040640704933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 95214360837104216750426309 17852692656957040640704933)
                    ·
                      refine ⟨3347379873179445120132175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17852692656957040640704933 3347379873179445120132175)
                      ·
                        rfl

theorem cell23_6518999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_6518999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6518999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6518999 prefixEnd_6518999 := by exact prefixLift 6518999
  have htrace : WordTrace (prefixWord ++ tailWord_6518999) baseStart_6518999 baseEnd_6518999 := by
    simpa [prefixWord, tailWord_6518999, baseEnd_6518999] using wordTrace_append hprefix tailTrace_6518999
  have hstable : (prefixWord ++ tailWord_6518999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6518999).length < 2 ^ (prefixWord ++ tailWord_6518999).sum := by decide
  have hdescent : baseEnd_6518999 < baseStart_6518999 := by decide
  rcases family_descends (prefixWord ++ tailWord_6518999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519009 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 9]
def baseStart_6519009 : Nat := 118140960795 + 6519009 * 2 ^ 59
def prefixEnd_6519009 : Nat := 4983230072969 + 3 ^ 40 * 6519009 * 2
def baseEnd_6519009 : Nat := 371931667553998897889681

theorem tailTrace_6519009 : CollatzResearch.WordTrace tailWord_6519009 prefixEnd_6519009 371931667553998897889681 := by
  unfold tailWord_6519009
  simp only [CollatzResearch.WordTrace]
  refine ⟨237767791639751225943344081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158511861093167483962229387 237767791639751225943344081)
  ·
    refine ⟨178325843729813419457508061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237767791639751225943344081 178325843729813419457508061)
    ·
      refine ⟨66872191398680032296565523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178325843729813419457508061 66872191398680032296565523)
      ·
        refine ⟨100308287098020048444848285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66872191398680032296565523 100308287098020048444848285)
        ·
          refine ⟨37615607661757518166818107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100308287098020048444848285 37615607661757518166818107)
          ·
            refine ⟨56423411492636277250227161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37615607661757518166818107 56423411492636277250227161)
            ·
              refine ⟨42317558619477207937670371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56423411492636277250227161 42317558619477207937670371)
              ·
                refine ⟨63476337929215811906505557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42317558619477207937670371 63476337929215811906505557)
                ·
                  refine ⟨371931667553998897889681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63476337929215811906505557 371931667553998897889681)
                  ·
                    rfl

theorem cell23_6519009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 9].length) (baseStart_6519009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519009 prefixEnd_6519009 := by exact prefixLift 6519009
  have htrace : WordTrace (prefixWord ++ tailWord_6519009) baseStart_6519009 baseEnd_6519009 := by
    simpa [prefixWord, tailWord_6519009, baseEnd_6519009] using wordTrace_append hprefix tailTrace_6519009
  have hstable : (prefixWord ++ tailWord_6519009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519009).length < 2 ^ (prefixWord ++ tailWord_6519009).sum := by decide
  have hdescent : baseEnd_6519009 < baseStart_6519009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519093 : List Nat := [1, 3, 3, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_6519093 : Nat := 118140960795 + 6519093 * 2 ^ 59
def prefixEnd_6519093 : Nat := 4983230072969 + 3 ^ 40 * 6519093 * 2
def baseEnd_6519093 : Nat := 3347428140360967752356743

theorem tailTrace_6519093 : CollatzResearch.WordTrace tailWord_6519093 prefixEnd_6519093 3347428140360967752356743 := by
  unfold tailWord_6519093
  simp only [CollatzResearch.WordTrace]
  refine ⟨237770855371446908289401933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158513903580964605526267955 237770855371446908289401933)
  ·
    refine ⟨89164070764292590608525725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 237770855371446908289401933 89164070764292590608525725)
    ·
      refine ⟨33436526536609721478197147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89164070764292590608525725 33436526536609721478197147)
      ·
        refine ⟨50154789804914582217295721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33436526536609721478197147 50154789804914582217295721)
        ·
          refine ⟨37616092353685936662971791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50154789804914582217295721 37616092353685936662971791)
          ·
            refine ⟨56424138530528904994457687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37616092353685936662971791 56424138530528904994457687)
            ·
              refine ⟨84636207795793357491686531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56424138530528904994457687 84636207795793357491686531)
              ·
                refine ⟨126954311693690036237529797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84636207795793357491686531 126954311693690036237529797)
                ·
                  refine ⟨23803933442566881794536837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 126954311693690036237529797 23803933442566881794536837)
                  ·
                    refine ⟨4463237520481290336475657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23803933442566881794536837 4463237520481290336475657)
                    ·
                      refine ⟨3347428140360967752356743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4463237520481290336475657 3347428140360967752356743)
                      ·
                        rfl

theorem cell23_6519093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_6519093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519093 prefixEnd_6519093 := by exact prefixLift 6519093
  have htrace : WordTrace (prefixWord ++ tailWord_6519093) baseStart_6519093 baseEnd_6519093 := by
    simpa [prefixWord, tailWord_6519093, baseEnd_6519093] using wordTrace_append hprefix tailTrace_6519093
  have hstable : (prefixWord ++ tailWord_6519093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519093).length < 2 ^ (prefixWord ++ tailWord_6519093).sum := by decide
  have hdescent : baseEnd_6519093 < baseStart_6519093 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519103 : List Nat := [1, 1, 2, 2, 4, 1, 4, 1, 3, 4]
def baseStart_6519103 : Nat := 118140960795 + 6519103 * 2 ^ 59
def prefixEnd_6519103 : Nat := 4983230072969 + 3 ^ 40 * 6519103 * 2
def baseEnd_6519103 : Nat := 1115811091722504237743899

theorem tailTrace_6519103 : CollatzResearch.WordTrace tailWord_6519103 prefixEnd_6519103 1115811091722504237743899 := by
  unfold tailWord_6519103
  simp only [CollatzResearch.WordTrace]
  refine ⟨237771220101410679997265963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158514146734273786664843975 237771220101410679997265963)
  ·
    refine ⟨356656830152116019995898945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237771220101410679997265963 356656830152116019995898945)
    ·
      refine ⟨267492622614087014996924209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356656830152116019995898945 267492622614087014996924209)
      ·
        refine ⟨200619466960565261247693157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267492622614087014996924209 200619466960565261247693157)
        ·
          refine ⟨37616150055105986483942467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200619466960565261247693157 37616150055105986483942467)
          ·
            refine ⟨56424225082658979725913701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37616150055105986483942467 56424225082658979725913701)
            ·
              refine ⟨10579542202998558698608819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56424225082658979725913701 10579542202998558698608819)
              ·
                refine ⟨15869313304497838047913229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10579542202998558698608819 15869313304497838047913229)
                ·
                  refine ⟨5950992489186689267967461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15869313304497838047913229 5950992489186689267967461)
                  ·
                    refine ⟨1115811091722504237743899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5950992489186689267967461 1115811091722504237743899)
                    ·
                      rfl

theorem cell23_6519103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 4, 1, 3, 4].length) (baseStart_6519103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519103 prefixEnd_6519103 := by exact prefixLift 6519103
  have htrace : WordTrace (prefixWord ++ tailWord_6519103) baseStart_6519103 baseEnd_6519103 := by
    simpa [prefixWord, tailWord_6519103, baseEnd_6519103] using wordTrace_append hprefix tailTrace_6519103
  have hstable : (prefixWord ++ tailWord_6519103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519103).length < 2 ^ (prefixWord ++ tailWord_6519103).sum := by decide
  have hdescent : baseEnd_6519103 < baseStart_6519103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519180 : List Nat := [2, 2, 1, 2, 1, 6, 1, 2, 1, 5]
def baseStart_6519180 : Nat := 118140960795 + 6519180 * 2 ^ 59
def prefixEnd_6519180 : Nat := 4983230072969 + 3 ^ 40 * 6519180 * 2
def baseEnd_6519180 : Nat := 1115824271059302970656281

theorem tailTrace_6519180 : CollatzResearch.WordTrace tailWord_6519180 prefixEnd_6519180 1115824271059302970656281 := by
  unfold tailWord_6519180
  simp only [CollatzResearch.WordTrace]
  refine ⟨118887014261065861073909497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158516019014754481431879329 118887014261065861073909497)
  ·
    refine ⟨89165260695799395805432123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118887014261065861073909497 89165260695799395805432123)
    ·
      refine ⟨133747891043699093708148185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89165260695799395805432123 133747891043699093708148185)
      ·
        refine ⟨100310918282774320281111139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133747891043699093708148185 100310918282774320281111139)
        ·
          refine ⟨150466377424161480421666709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100310918282774320281111139 150466377424161480421666709)
          ·
            refine ⟨7053111441757569394765627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150466377424161480421666709 7053111441757569394765627)
            ·
              refine ⟨10579667162636354092148441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7053111441757569394765627 10579667162636354092148441)
              ·
                refine ⟨7934750371977265569111331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10579667162636354092148441 7934750371977265569111331)
                ·
                  refine ⟨11902125557965898353666997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7934750371977265569111331 11902125557965898353666997)
                  ·
                    refine ⟨1115824271059302970656281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11902125557965898353666997 1115824271059302970656281)
                    ·
                      rfl

theorem cell23_6519180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_6519180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519180 prefixEnd_6519180 := by exact prefixLift 6519180
  have htrace : WordTrace (prefixWord ++ tailWord_6519180) baseStart_6519180 baseEnd_6519180 := by
    simpa [prefixWord, tailWord_6519180, baseEnd_6519180] using wordTrace_append hprefix tailTrace_6519180
  have hstable : (prefixWord ++ tailWord_6519180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519180).length < 2 ^ (prefixWord ++ tailWord_6519180).sum := by decide
  have hdescent : baseEnd_6519180 < baseStart_6519180 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519197 : List Nat := [1, 4, 2, 1, 4, 1, 3, 1, 1, 5]
def baseStart_6519197 : Nat := 118140960795 + 6519197 * 2 ^ 59
def prefixEnd_6519197 : Nat := 4983230072969 + 3 ^ 40 * 6519197 * 2
def baseEnd_6519197 : Nat := 1115827180783011781818755

theorem tailTrace_6519197 : CollatzResearch.WordTrace tailWord_6519197 prefixEnd_6519197 1115827180783011781818755 := by
  unfold tailWord_6519197
  simp only [CollatzResearch.WordTrace]
  refine ⟨237774648563070134051187845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158516432375380089367458563 237774648563070134051187845)
  ·
    refine ⟨44582746605575650134597721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237774648563070134051187845 44582746605575650134597721)
    ·
      refine ⟨33437059954181737600948291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44582746605575650134597721 33437059954181737600948291)
      ·
        refine ⟨50155589931272606401422437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33437059954181737600948291 50155589931272606401422437)
        ·
          refine ⟨9404173112113613700266707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50155589931272606401422437 9404173112113613700266707)
          ·
            refine ⟨14106259668170420550400061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9404173112113613700266707 14106259668170420550400061)
            ·
              refine ⟨5289847375563907706400023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14106259668170420550400061 5289847375563907706400023)
              ·
                refine ⟨7934771063345861559600035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5289847375563907706400023 7934771063345861559600035)
                ·
                  refine ⟨11902156595018792339400053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7934771063345861559600035 11902156595018792339400053)
                  ·
                    refine ⟨1115827180783011781818755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11902156595018792339400053 1115827180783011781818755)
                    ·
                      rfl

theorem cell23_6519197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_6519197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519197 prefixEnd_6519197 := by exact prefixLift 6519197
  have htrace : WordTrace (prefixWord ++ tailWord_6519197) baseStart_6519197 baseEnd_6519197 := by
    simpa [prefixWord, tailWord_6519197, baseEnd_6519197] using wordTrace_append hprefix tailTrace_6519197
  have hstable : (prefixWord ++ tailWord_6519197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519197).length < 2 ^ (prefixWord ++ tailWord_6519197).sum := by decide
  have hdescent : baseEnd_6519197 < baseStart_6519197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519203 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 5]
def baseStart_6519203 : Nat := 118140960795 + 6519203 * 2 ^ 59
def prefixEnd_6519203 : Nat := 4983230072969 + 3 ^ 40 * 6519203 * 2
def baseEnd_6519203 : Nat := 3347484623232962321981237

theorem tailTrace_6519203 : CollatzResearch.WordTrace tailWord_6519203 prefixEnd_6519203 3347484623232962321981237 := by
  unfold tailWord_6519203
  simp only [CollatzResearch.WordTrace]
  refine ⟨237774867401048397075906263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158516578267365598050604175 237774867401048397075906263)
  ·
    refine ⟨356662301101572595613859395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237774867401048397075906263 356662301101572595613859395)
    ·
      refine ⟨534993451652358893420789093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356662301101572595613859395 534993451652358893420789093)
      ·
        refine ⟨100311272184817292516397955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 534993451652358893420789093 100311272184817292516397955)
        ·
          refine ⟨150466908277225938774596933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100311272184817292516397955 150466908277225938774596933)
          ·
            refine ⟨28212545301979863520236925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150466908277225938774596933 28212545301979863520236925)
            ·
              refine ⟨10579704488242448820088847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28212545301979863520236925 10579704488242448820088847)
              ·
                refine ⟨15869556732363673230133271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10579704488242448820088847 15869556732363673230133271)
                ·
                  refine ⟨23804335098545509845199907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15869556732363673230133271 23804335098545509845199907)
                  ·
                    refine ⟨35706502647818264767799861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23804335098545509845199907 35706502647818264767799861)
                    ·
                      refine ⟨3347484623232962321981237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35706502647818264767799861 3347484623232962321981237)
                      ·
                        rfl

theorem cell23_6519203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_6519203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519203 prefixEnd_6519203 := by exact prefixLift 6519203
  have htrace : WordTrace (prefixWord ++ tailWord_6519203) baseStart_6519203 baseEnd_6519203 := by
    simpa [prefixWord, tailWord_6519203, baseEnd_6519203] using wordTrace_append hprefix tailTrace_6519203
  have hstable : (prefixWord ++ tailWord_6519203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519203).length < 2 ^ (prefixWord ++ tailWord_6519203).sum := by decide
  have hdescent : baseEnd_6519203 < baseStart_6519203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519223 : List Nat := [1, 1, 3, 1, 3, 5, 1, 8]
def baseStart_6519223 : Nat := 118140960795 + 6519223 * 2 ^ 59
def prefixEnd_6519223 : Nat := 4983230072969 + 3 ^ 40 * 6519223 * 2
def baseEnd_6519223 : Nat := 123981292327631564582635

theorem tailTrace_6519223 : CollatzResearch.WordTrace tailWord_6519223 prefixEnd_6519223 123981292327631564582635 := by
  unfold tailWord_6519223
  simp only [CollatzResearch.WordTrace]
  refine ⟨237775596860975940491634323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158517064573983960327756215 237775596860975940491634323)
  ·
    refine ⟨356663395291463910737451485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237775596860975940491634323 356663395291463910737451485)
    ·
      refine ⟨133748773234298966526544307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356663395291463910737451485 133748773234298966526544307)
      ·
        refine ⟨200623159851448449789816461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133748773234298966526544307 200623159851448449789816461)
        ·
          refine ⟨75233684944293168671181173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 200623159851448449789816461 75233684944293168671181173)
          ·
            refine ⟨7053157963527484562923235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75233684944293168671181173 7053157963527484562923235)
            ·
              refine ⟨10579736945291226844384853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7053157963527484562923235 10579736945291226844384853)
              ·
                refine ⟨123981292327631564582635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10579736945291226844384853 123981292327631564582635)
                ·
                  rfl

theorem cell23_6519223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 8].length) (baseStart_6519223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519223 prefixEnd_6519223 := by exact prefixLift 6519223
  have htrace : WordTrace (prefixWord ++ tailWord_6519223) baseStart_6519223 baseEnd_6519223 := by
    simpa [prefixWord, tailWord_6519223, baseEnd_6519223] using wordTrace_append hprefix tailTrace_6519223
  have hstable : (prefixWord ++ tailWord_6519223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519223).length < 2 ^ (prefixWord ++ tailWord_6519223).sum := by decide
  have hdescent : baseEnd_6519223 < baseStart_6519223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519226 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6]
def baseStart_6519226 : Nat := 118140960795 + 6519226 * 2 ^ 59
def prefixEnd_6519226 : Nat := 4983230072969 + 3 ^ 40 * 6519226 * 2
def baseEnd_6519226 : Nat := 3347496433288015731993631

theorem tailTrace_6519226 : CollatzResearch.WordTrace tailWord_6519226 prefixEnd_6519226 3347496433288015731993631 := by
  unfold tailWord_6519226
  simp only [CollatzResearch.WordTrace]
  refine ⟨59443926569991268000998383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158517137519976714669329021 59443926569991268000998383)
  ·
    refine ⟨89165889854986902001497575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59443926569991268000998383 89165889854986902001497575)
    ·
      refine ⟨133748834782480353002246363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89165889854986902001497575 133748834782480353002246363)
      ·
        refine ⟨200623252173720529503369545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133748834782480353002246363 200623252173720529503369545)
        ·
          refine ⟨150467439130290397127527159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200623252173720529503369545 150467439130290397127527159)
          ·
            refine ⟨225701158695435595691290739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150467439130290397127527159 225701158695435595691290739)
            ·
              refine ⟨338551738043153393536936109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225701158695435595691290739 338551738043153393536936109)
              ·
                refine ⟨126956901766182522576351041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 338551738043153393536936109 126956901766182522576351041)
                ·
                  refine ⟨95217676324636891932263281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126956901766182522576351041 95217676324636891932263281)
                  ·
                    refine ⟨71413257243477668949197461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 95217676324636891932263281 71413257243477668949197461)
                    ·
                      refine ⟨3347496433288015731993631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71413257243477668949197461 3347496433288015731993631)
                      ·
                        rfl

theorem cell23_6519226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 2, 2, 6].length) (baseStart_6519226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519226 prefixEnd_6519226 := by exact prefixLift 6519226
  have htrace : WordTrace (prefixWord ++ tailWord_6519226) baseStart_6519226 baseEnd_6519226 := by
    simpa [prefixWord, tailWord_6519226, baseEnd_6519226] using wordTrace_append hprefix tailTrace_6519226
  have hstable : (prefixWord ++ tailWord_6519226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519226).length < 2 ^ (prefixWord ++ tailWord_6519226).sum := by decide
  have hdescent : baseEnd_6519226 < baseStart_6519226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519267 : List Nat := [1, 1, 1, 6, 3, 1, 1, 1, 4, 1, 3]
def baseStart_6519267 : Nat := 118140960795 + 6519267 * 2 ^ 59
def prefixEnd_6519267 : Nat := 4983230072969 + 3 ^ 40 * 6519267 * 2
def baseEnd_6519267 : Nat := 3347517485994850071580943

theorem tailTrace_6519267 : CollatzResearch.WordTrace tailWord_6519267 prefixEnd_6519267 3347517485994850071580943 := by
  unfold tailWord_6519267
  simp only [CollatzResearch.WordTrace]
  refine ⟨237777201672816536006236055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158518134448544357337490703 237777201672816536006236055)
  ·
    refine ⟨356665802509224804009354083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237777201672816536006236055 356665802509224804009354083)
    ·
      refine ⟨534998703763837206014031125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356665802509224804009354083 534998703763837206014031125)
      ·
        refine ⟨25078064238929869031907709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 534998703763837206014031125 25078064238929869031907709)
        ·
          refine ⟨9404274089598700886965391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25078064238929869031907709 9404274089598700886965391)
          ·
            refine ⟨14106411134398051330448087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9404274089598700886965391 14106411134398051330448087)
            ·
              refine ⟨21159616701597076995672131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14106411134398051330448087 21159616701597076995672131)
              ·
                refine ⟨31739425052395615493508197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21159616701597076995672131 31739425052395615493508197)
                ·
                  refine ⟨5951142197324177905032787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31739425052395615493508197 5951142197324177905032787)
                  ·
                    refine ⟨8926713295986266857549181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5951142197324177905032787 8926713295986266857549181)
                    ·
                      refine ⟨3347517485994850071580943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8926713295986266857549181 3347517485994850071580943)
                      ·
                        rfl

theorem cell23_6519267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_6519267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519267 prefixEnd_6519267 := by exact prefixLift 6519267
  have htrace : WordTrace (prefixWord ++ tailWord_6519267) baseStart_6519267 baseEnd_6519267 := by
    simpa [prefixWord, tailWord_6519267, baseEnd_6519267] using wordTrace_append hprefix tailTrace_6519267
  have hstable : (prefixWord ++ tailWord_6519267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519267).length < 2 ^ (prefixWord ++ tailWord_6519267).sum := by decide
  have hdescent : baseEnd_6519267 < baseStart_6519267 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519290 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2]
def baseStart_6519290 : Nat := 118140960795 + 6519290 * 2 ^ 59
def prefixEnd_6519290 : Nat := 4983230072969 + 3 ^ 40 * 6519290 * 2
def baseEnd_6519290 : Nat := 3347529296049903481593337

theorem tailTrace_6519290 : CollatzResearch.WordTrace tailWord_6519290 prefixEnd_6519290 3347529296049903481593337 := by
  unfold tailWord_6519290
  simp only [CollatzResearch.WordTrace]
  refine ⟨59444510137933302733580831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158518693701155473956215549 59444510137933302733580831)
  ·
    refine ⟨89166765206899954100371247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59444510137933302733580831 89166765206899954100371247)
    ·
      refine ⟨133750147810349931150556871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89166765206899954100371247 133750147810349931150556871)
      ·
        refine ⟨200625221715524896725835307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133750147810349931150556871 200625221715524896725835307)
        ·
          refine ⟨300937832573287345088752961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200625221715524896725835307 300937832573287345088752961)
          ·
            refine ⟨225703374429965508816564721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300937832573287345088752961 225703374429965508816564721)
            ·
              refine ⟨169277530822474131612423541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225703374429965508816564721 169277530822474131612423541)
              ·
                refine ⟨15869768514606949838664707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169277530822474131612423541 15869768514606949838664707)
                ·
                  refine ⟨23804652771910424757997061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15869768514606949838664707 23804652771910424757997061)
                  ·
                    refine ⟨4463372394733204642124449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23804652771910424757997061 4463372394733204642124449)
                    ·
                      refine ⟨3347529296049903481593337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4463372394733204642124449 3347529296049903481593337)
                      ·
                        rfl

theorem cell23_6519290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2].length) (baseStart_6519290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519290 prefixEnd_6519290 := by exact prefixLift 6519290
  have htrace : WordTrace (prefixWord ++ tailWord_6519290) baseStart_6519290 baseEnd_6519290 := by
    simpa [prefixWord, tailWord_6519290, baseEnd_6519290] using wordTrace_append hprefix tailTrace_6519290
  have hstable : (prefixWord ++ tailWord_6519290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519290).length < 2 ^ (prefixWord ++ tailWord_6519290).sum := by decide
  have hdescent : baseEnd_6519290 < baseStart_6519290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519293 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_6519293 : Nat := 118140960795 + 6519293 * 2 ^ 59
def prefixEnd_6519293 : Nat := 4983230072969 + 3 ^ 40 * 6519293 * 2
def baseEnd_6519293 : Nat := 3347530836491866969855823

theorem tailTrace_6519293 : CollatzResearch.WordTrace tailWord_6519293 prefixEnd_6519293 3347530836491866969855823 := by
  unfold tailWord_6519293
  simp only [CollatzResearch.WordTrace]
  refine ⟨237778149970722342446682533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158518766647148228297788355 237778149970722342446682533)
  ·
    refine ⟨44583403119510439208752975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 237778149970722342446682533 44583403119510439208752975)
    ·
      refine ⟨66875104679265658813129463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44583403119510439208752975 66875104679265658813129463)
      ·
        refine ⟨100312657018898488219694195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66875104679265658813129463 100312657018898488219694195)
        ·
          refine ⟨150468985528347732329541293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100312657018898488219694195 150468985528347732329541293)
          ·
            refine ⟨56425869573130399623577985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150468985528347732329541293 56425869573130399623577985)
            ·
              refine ⟨42319402179847799717683489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56425869573130399623577985 42319402179847799717683489)
              ·
                refine ⟨31739551634885849788262617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42319402179847799717683489 31739551634885849788262617)
                ·
                  refine ⟨23804663726164387341196963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31739551634885849788262617 23804663726164387341196963)
                  ·
                    refine ⟨35706995589246581011795445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23804663726164387341196963 35706995589246581011795445)
                    ·
                      refine ⟨3347530836491866969855823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35706995589246581011795445 3347530836491866969855823)
                      ·
                        rfl

theorem cell23_6519293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_6519293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519293 prefixEnd_6519293 := by exact prefixLift 6519293
  have htrace : WordTrace (prefixWord ++ tailWord_6519293) baseStart_6519293 baseEnd_6519293 := by
    simpa [prefixWord, tailWord_6519293, baseEnd_6519293] using wordTrace_append hprefix tailTrace_6519293
  have hstable : (prefixWord ++ tailWord_6519293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519293).length < 2 ^ (prefixWord ++ tailWord_6519293).sum := by decide
  have hdescent : baseEnd_6519293 < baseStart_6519293 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519302 : List Nat := [6, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_6519302 : Nat := 118140960795 + 6519302 * 2 ^ 59
def prefixEnd_6519302 : Nat := 4983230072969 + 3 ^ 40 * 6519302 * 2
def baseEnd_6519302 : Nat := 3347535457817757434643283

theorem tailTrace_6519302 : CollatzResearch.WordTrace tailWord_6519302 prefixEnd_6519302 3347535457817757434643283 := by
  unfold tailWord_6519302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7430577444615304280742505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158518985485126491322506773 7430577444615304280742505)
  ·
    refine ⟨5572933083461478210556879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7430577444615304280742505 5572933083461478210556879)
    ·
      refine ⟨8359399625192217315835319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5572933083461478210556879 8359399625192217315835319)
      ·
        refine ⟨12539099437788325973752979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8359399625192217315835319 12539099437788325973752979)
        ·
          refine ⟨18808649156682488960629469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12539099437788325973752979 18808649156682488960629469)
          ·
            refine ⟨7053243433755933360236051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18808649156682488960629469 7053243433755933360236051)
            ·
              refine ⟨10579865150633900040354077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7053243433755933360236051 10579865150633900040354077)
              ·
                refine ⟨3967449431487712515132779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10579865150633900040354077 3967449431487712515132779)
                ·
                  refine ⟨5951174147231568772699169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967449431487712515132779 5951174147231568772699169)
                  ·
                    refine ⟨4463380610423676579524377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5951174147231568772699169 4463380610423676579524377)
                    ·
                      refine ⟨3347535457817757434643283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4463380610423676579524377 3347535457817757434643283)
                      ·
                        rfl

theorem cell23_6519302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_6519302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519302 prefixEnd_6519302 := by exact prefixLift 6519302
  have htrace : WordTrace (prefixWord ++ tailWord_6519302) baseStart_6519302 baseEnd_6519302 := by
    simpa [prefixWord, tailWord_6519302, baseEnd_6519302] using wordTrace_append hprefix tailTrace_6519302
  have hstable : (prefixWord ++ tailWord_6519302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519302).length < 2 ^ (prefixWord ++ tailWord_6519302).sum := by decide
  have hdescent : baseEnd_6519302 < baseStart_6519302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519307 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 4, 2, 2]
def baseStart_6519307 : Nat := 118140960795 + 6519307 * 2 ^ 59
def prefixEnd_6519307 : Nat := 4983230072969 + 3 ^ 40 * 6519307 * 2
def baseEnd_6519307 : Nat := 3347538025221029915080759

theorem tailTrace_6519307 : CollatzResearch.WordTrace tailWord_6519307 prefixEnd_6519307 3347538025221029915080759 := by
  unfold tailWord_6519307
  simp only [CollatzResearch.WordTrace]
  refine ⟨237778660592671622837692175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158519107061781081891794783 237778660592671622837692175)
  ·
    refine ⟨356667990889007434256538263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237778660592671622837692175 356667990889007434256538263)
    ·
      refine ⟨535001986333511151384807395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356667990889007434256538263 535001986333511151384807395)
      ·
        refine ⟨802502979500266727077211093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535001986333511151384807395 802502979500266727077211093)
        ·
          refine ⟨18808663582037501415872135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 802502979500266727077211093 18808663582037501415872135)
          ·
            refine ⟨28212995373056252123808203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18808663582037501415872135 28212995373056252123808203)
            ·
              refine ⟨42319493059584378185712305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28212995373056252123808203 42319493059584378185712305)
              ·
                refine ⟨31739619794688283639284229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42319493059584378185712305 31739619794688283639284229)
                ·
                  refine ⟨5951178711504053182365793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31739619794688283639284229 5951178711504053182365793)
                  ·
                    refine ⟨4463384033628039886774345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5951178711504053182365793 4463384033628039886774345)
                    ·
                      refine ⟨3347538025221029915080759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4463384033628039886774345 3347538025221029915080759)
                      ·
                        rfl

theorem cell23_6519307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 2, 2].length) (baseStart_6519307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519307 prefixEnd_6519307 := by exact prefixLift 6519307
  have htrace : WordTrace (prefixWord ++ tailWord_6519307) baseStart_6519307 baseEnd_6519307 := by
    simpa [prefixWord, tailWord_6519307, baseEnd_6519307] using wordTrace_append hprefix tailTrace_6519307
  have hstable : (prefixWord ++ tailWord_6519307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519307).length < 2 ^ (prefixWord ++ tailWord_6519307).sum := by decide
  have hdescent : baseEnd_6519307 < baseStart_6519307 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519310 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_6519310 : Nat := 118140960795 + 6519310 * 2 ^ 59
def prefixEnd_6519310 : Nat := 4983230072969 + 3 ^ 40 * 6519310 * 2
def baseEnd_6519310 : Nat := 3347539565662993403343245

theorem tailTrace_6519310 : CollatzResearch.WordTrace tailWord_6519310 prefixEnd_6519310 3347539565662993403343245 := by
  unfold tailWord_6519310
  simp only [CollatzResearch.WordTrace]
  refine ⟨29722346251457594293756423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158519180007773836233367589 29722346251457594293756423)
  ·
    refine ⟨44583519377186391440634635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29722346251457594293756423 44583519377186391440634635)
    ·
      refine ⟨66875279065779587160951953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44583519377186391440634635 66875279065779587160951953)
      ·
        refine ⟨50156459299334690370713965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66875279065779587160951953 50156459299334690370713965)
        ·
          refine ⟨18808672237250508889017737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50156459299334690370713965 18808672237250508889017737)
          ·
            refine ⟨14106504177937881666763303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18808672237250508889017737 14106504177937881666763303)
            ·
              refine ⟨21159756266906822500144955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14106504177937881666763303 21159756266906822500144955)
              ·
                refine ⟨31739634400360233750217433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21159756266906822500144955 31739634400360233750217433)
                ·
                  refine ⟨23804725800270175312663075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31739634400360233750217433 23804725800270175312663075)
                  ·
                    refine ⟨35707088700405262968994613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23804725800270175312663075 35707088700405262968994613)
                    ·
                      refine ⟨3347539565662993403343245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35707088700405262968994613 3347539565662993403343245)
                      ·
                        rfl

theorem cell23_6519310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_6519310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519310 prefixEnd_6519310 := by exact prefixLift 6519310
  have htrace : WordTrace (prefixWord ++ tailWord_6519310) baseStart_6519310 baseEnd_6519310 := by
    simpa [prefixWord, tailWord_6519310, baseEnd_6519310] using wordTrace_append hprefix tailTrace_6519310
  have hstable : (prefixWord ++ tailWord_6519310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519310).length < 2 ^ (prefixWord ++ tailWord_6519310).sum := by decide
  have hdescent : baseEnd_6519310 < baseStart_6519310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519335 : List Nat := [1, 1, 7, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_6519335 : Nat := 118140960795 + 6519335 * 2 ^ 59
def prefixEnd_6519335 : Nat := 4983230072969 + 3 ^ 40 * 6519335 * 2
def baseEnd_6519335 : Nat := 3347552402679355805530631

theorem tailTrace_6519335 : CollatzResearch.WordTrace tailWord_6519335 prefixEnd_6519335 3347552402679355805530631 := by
  unfold tailWord_6519335
  simp only [CollatzResearch.WordTrace]
  refine ⟨237779681836570183619711459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158519787891046789079807639 237779681836570183619711459)
  ·
    refine ⟨356669522754855275429567189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237779681836570183619711459 356669522754855275429567189)
    ·
      refine ⟨8359441939566920517880481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 356669522754855275429567189 8359441939566920517880481)
      ·
        refine ⟨6269581454675190388410361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8359441939566920517880481 6269581454675190388410361)
        ·
          refine ⟨4702186091006392791307771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6269581454675190388410361 4702186091006392791307771)
          ·
            refine ⟨7053279136509589186961657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4702186091006392791307771 7053279136509589186961657)
            ·
              refine ⟨5289959352382191890221243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7053279136509589186961657 5289959352382191890221243)
              ·
                refine ⟨7934939028573287835331865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5289959352382191890221243 7934939028573287835331865)
                ·
                  refine ⟨5951204271429965876498899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7934939028573287835331865 5951204271429965876498899)
                  ·
                    refine ⟨8926806407144948814748349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5951204271429965876498899 8926806407144948814748349)
                    ·
                      refine ⟨3347552402679355805530631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8926806407144948814748349 3347552402679355805530631)
                      ·
                        rfl

theorem cell23_6519335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_6519335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519335 prefixEnd_6519335 := by exact prefixLift 6519335
  have htrace : WordTrace (prefixWord ++ tailWord_6519335) baseStart_6519335 baseEnd_6519335 := by
    simpa [prefixWord, tailWord_6519335, baseEnd_6519335] using wordTrace_append hprefix tailTrace_6519335
  have hstable : (prefixWord ++ tailWord_6519335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519335).length < 2 ^ (prefixWord ++ tailWord_6519335).sum := by decide
  have hdescent : baseEnd_6519335 < baseStart_6519335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519353 : List Nat := [1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 7]
def baseStart_6519353 : Nat := 118140960795 + 6519353 * 2 ^ 59
def prefixEnd_6519353 : Nat := 4983230072969 + 3 ^ 40 * 6519353 * 2
def baseEnd_6519353 : Nat := 3347561645331136735105547

theorem tailTrace_6519353 : CollatzResearch.WordTrace tailWord_6519353 prefixEnd_6519353 3347561645331136735105547 := by
  unfold tailWord_6519353
  simp only [CollatzResearch.WordTrace]
  refine ⟨237780338350504972693866713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158520225567003315129244475 237780338350504972693866713)
  ·
    refine ⟨178335253762878729520400035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237780338350504972693866713 178335253762878729520400035)
    ·
      refine ⟨267502880644318094280600053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178335253762878729520400035 267502880644318094280600053)
      ·
        refine ⟨25078395060404821338806255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 267502880644318094280600053 25078395060404821338806255)
        ·
          refine ⟨37617592590607232008209383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25078395060404821338806255 37617592590607232008209383)
          ·
            refine ⟨56426388885910848012314075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37617592590607232008209383 56426388885910848012314075)
            ·
              refine ⟨84639583328866272018471113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56426388885910848012314075 84639583328866272018471113)
              ·
                refine ⟨63479687496649704013853335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84639583328866272018471113 63479687496649704013853335)
                ·
                  refine ⟨95219531244974556020780003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63479687496649704013853335 95219531244974556020780003)
                  ·
                    refine ⟨142829296867461834031170005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 95219531244974556020780003 142829296867461834031170005)
                    ·
                      refine ⟨3347561645331136735105547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 142829296867461834031170005 3347561645331136735105547)
                      ·
                        rfl

theorem cell23_6519353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_6519353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519353 prefixEnd_6519353 := by exact prefixLift 6519353
  have htrace : WordTrace (prefixWord ++ tailWord_6519353) baseStart_6519353 baseEnd_6519353 := by
    simpa [prefixWord, tailWord_6519353, baseEnd_6519353] using wordTrace_append hprefix tailTrace_6519353
  have hstable : (prefixWord ++ tailWord_6519353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519353).length < 2 ^ (prefixWord ++ tailWord_6519353).sum := by decide
  have hdescent : baseEnd_6519353 < baseStart_6519353 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519363 : List Nat := [1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 4]
def baseStart_6519363 : Nat := 118140960795 + 6519363 * 2 ^ 59
def prefixEnd_6519363 : Nat := 4983230072969 + 3 ^ 40 * 6519363 * 2
def baseEnd_6519363 : Nat := 3347566780137681695980501

theorem tailTrace_6519363 : CollatzResearch.WordTrace tailWord_6519363 prefixEnd_6519363 3347566780137681695980501 := by
  unfold tailWord_6519363
  simp only [CollatzResearch.WordTrace]
  refine ⟨237780703080468744401730743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158520468720312496267820495 237780703080468744401730743)
  ·
    refine ⟨356671054620703116602596115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237780703080468744401730743 356671054620703116602596115)
    ·
      refine ⟨535006581931054674903894173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356671054620703116602596115 535006581931054674903894173)
      ·
        refine ⟨200627468224145503088960315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 535006581931054674903894173 200627468224145503088960315)
        ·
          refine ⟨300941202336218254633440473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200627468224145503088960315 300941202336218254633440473)
          ·
            refine ⟨225705901752163690975080355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 300941202336218254633440473 225705901752163690975080355)
            ·
              refine ⟨338558852628245536462620533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225705901752163690975080355 338558852628245536462620533)
              ·
                refine ⟨31739892433898019043370675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 338558852628245536462620533 31739892433898019043370675)
                ·
                  refine ⟨47609838650847028565056013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31739892433898019043370675 47609838650847028565056013)
                  ·
                    refine ⟨17853689494067635711896005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 47609838650847028565056013 17853689494067635711896005)
                    ·
                      refine ⟨3347566780137681695980501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17853689494067635711896005 3347566780137681695980501)
                      ·
                        rfl

theorem cell23_6519363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_6519363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519363 prefixEnd_6519363 := by exact prefixLift 6519363
  have htrace : WordTrace (prefixWord ++ tailWord_6519363) baseStart_6519363 baseEnd_6519363 := by
    simpa [prefixWord, tailWord_6519363, baseEnd_6519363] using wordTrace_append hprefix tailTrace_6519363
  have hstable : (prefixWord ++ tailWord_6519363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519363).length < 2 ^ (prefixWord ++ tailWord_6519363).sum := by decide
  have hdescent : baseEnd_6519363 < baseStart_6519363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519383 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 5]
def baseStart_6519383 : Nat := 118140960795 + 6519383 * 2 ^ 59
def prefixEnd_6519383 : Nat := 4983230072969 + 3 ^ 40 * 6519383 * 2
def baseEnd_6519383 : Nat := 3347577049750771617730409

theorem tailTrace_6519383 : CollatzResearch.WordTrace tailWord_6519383 prefixEnd_6519383 3347577049750771617730409 := by
  unfold tailWord_6519383
  simp only [CollatzResearch.WordTrace]
  refine ⟨237781432540396287817458803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158520955026930858544972535 237781432540396287817458803)
  ·
    refine ⟨356672148810594431726188205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237781432540396287817458803 356672148810594431726188205)
    ·
      refine ⟨133752055803972911897320577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356672148810594431726188205 133752055803972911897320577)
      ·
        refine ⟨100314041852979683922990433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133752055803972911897320577 100314041852979683922990433)
        ·
          refine ⟨75235531389734762942242825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100314041852979683922990433 75235531389734762942242825)
          ·
            refine ⟨56426648542301072206682119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75235531389734762942242825 56426648542301072206682119)
            ·
              refine ⟨84639972813451608310023179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56426648542301072206682119 84639972813451608310023179)
              ·
                refine ⟨126959959220177412465034769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84639972813451608310023179 126959959220177412465034769)
                ·
                  refine ⟨95219969415133059348776077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 126959959220177412465034769 95219969415133059348776077)
                  ·
                    refine ⟨35707488530674897255791029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 95219969415133059348776077 35707488530674897255791029)
                    ·
                      refine ⟨3347577049750771617730409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35707488530674897255791029 3347577049750771617730409)
                      ·
                        rfl

theorem cell23_6519383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_6519383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519383 prefixEnd_6519383 := by exact prefixLift 6519383
  have htrace : WordTrace (prefixWord ++ tailWord_6519383) baseStart_6519383 baseEnd_6519383 := by
    simpa [prefixWord, tailWord_6519383, baseEnd_6519383] using wordTrace_append hprefix tailTrace_6519383
  have hstable : (prefixWord ++ tailWord_6519383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519383).length < 2 ^ (prefixWord ++ tailWord_6519383).sum := by decide
  have hdescent : baseEnd_6519383 < baseStart_6519383 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519417 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 2, 2, 3]
def baseStart_6519417 : Nat := 118140960795 + 6519417 * 2 ^ 59
def prefixEnd_6519417 : Nat := 4983230072969 + 3 ^ 40 * 6519417 * 2
def baseEnd_6519417 : Nat := 3347594508093024484705253

theorem tailTrace_6519417 : CollatzResearch.WordTrace tailWord_6519417 prefixEnd_6519417 3347594508093024484705253 := by
  unfold tailWord_6519417
  simp only [CollatzResearch.WordTrace]
  refine ⟨237782672622273111624196505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158521781748182074416131003 237782672622273111624196505)
  ·
    refine ⟨178337004466704833718147379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237782672622273111624196505 178337004466704833718147379)
    ·
      refine ⟨267505506700057250577221069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178337004466704833718147379 267505506700057250577221069)
      ·
        refine ⟨100314565012521468966457901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267505506700057250577221069 100314565012521468966457901)
        ·
          refine ⟨37617961879695550862421713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100314565012521468966457901 37617961879695550862421713)
          ·
            refine ⟨28213471409771663146816285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37617961879695550862421713 28213471409771663146816285)
            ·
              refine ⟨10580051778664373680056107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28213471409771663146816285 10580051778664373680056107)
              ·
                refine ⟨15870077667996560520084161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10580051778664373680056107 15870077667996560520084161)
                ·
                  refine ⟨11902558250997420390063121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15870077667996560520084161 11902558250997420390063121)
                  ·
                    refine ⟨8926918688248065292547341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11902558250997420390063121 8926918688248065292547341)
                    ·
                      refine ⟨3347594508093024484705253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8926918688248065292547341 3347594508093024484705253)
                      ·
                        rfl

theorem cell23_6519417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 2, 2, 3].length) (baseStart_6519417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519417 prefixEnd_6519417 := by exact prefixLift 6519417
  have htrace : WordTrace (prefixWord ++ tailWord_6519417) baseStart_6519417 baseEnd_6519417 := by
    simpa [prefixWord, tailWord_6519417, baseEnd_6519417] using wordTrace_append hprefix tailTrace_6519417
  have hstable : (prefixWord ++ tailWord_6519417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519417).length < 2 ^ (prefixWord ++ tailWord_6519417).sum := by decide
  have hdescent : baseEnd_6519417 < baseStart_6519417 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519424 : List Nat := [2, 1, 1, 2, 1, 6, 2, 3, 1, 4]
def baseStart_6519424 : Nat := 118140960795 + 6519424 * 2 ^ 59
def prefixEnd_6519424 : Nat := 4983230072969 + 3 ^ 40 * 6519424 * 2
def baseEnd_6519424 : Nat := 1115866034152535319105907

theorem tailTrace_6519424 : CollatzResearch.WordTrace tailWord_6519424 prefixEnd_6519424 1115866034152535319105907 := by
  unfold tailWord_6519424
  simp only [CollatzResearch.WordTrace]
  refine ⟨118891463966623875909850663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158521951955498501213134217 118891463966623875909850663)
  ·
    refine ⟨178337195949935813864775995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118891463966623875909850663 178337195949935813864775995)
    ·
      refine ⟨267505793924903720797163993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178337195949935813864775995 267505793924903720797163993)
      ·
        refine ⟨200629345443677790597872995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267505793924903720797163993 200629345443677790597872995)
        ·
          refine ⟨300944018165516685896809493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200629345443677790597872995 300944018165516685896809493)
          ·
            refine ⟨14106750851508594651412945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 300944018165516685896809493 14106750851508594651412945)
            ·
              refine ⟨10580063138631445988559709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14106750851508594651412945 10580063138631445988559709)
              ·
                refine ⟨3967523676986792245709891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10580063138631445988559709 3967523676986792245709891)
                ·
                  refine ⟨5951285515480188368564837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967523676986792245709891 5951285515480188368564837)
                  ·
                    refine ⟨1115866034152535319105907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5951285515480188368564837 1115866034152535319105907)
                    ·
                      rfl

theorem cell23_6519424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 2, 3, 1, 4].length) (baseStart_6519424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519424 prefixEnd_6519424 := by exact prefixLift 6519424
  have htrace : WordTrace (prefixWord ++ tailWord_6519424) baseStart_6519424 baseEnd_6519424 := by
    simpa [prefixWord, tailWord_6519424, baseEnd_6519424] using wordTrace_append hprefix tailTrace_6519424
  have hstable : (prefixWord ++ tailWord_6519424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519424).length < 2 ^ (prefixWord ++ tailWord_6519424).sum := by decide
  have hdescent : baseEnd_6519424 < baseStart_6519424 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519443 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 5]
def baseStart_6519443 : Nat := 118140960795 + 6519443 * 2 ^ 59
def prefixEnd_6519443 : Nat := 4983230072969 + 3 ^ 40 * 6519443 * 2
def baseEnd_6519443 : Nat := 3347607858590041382980133

theorem tailTrace_6519443 : CollatzResearch.WordTrace tailWord_6519443 prefixEnd_6519443 3347607858590041382980133 := by
  unfold tailWord_6519443
  simp only [CollatzResearch.WordTrace]
  refine ⟨237783620920178918064642983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158522413946785945376428655 237783620920178918064642983)
  ·
    refine ⟨356675431380268377096964475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237783620920178918064642983 356675431380268377096964475)
    ·
      refine ⟨535013147070402565645446713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356675431380268377096964475 535013147070402565645446713)
      ·
        refine ⟨401259860302801924234085035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535013147070402565645446713 401259860302801924234085035)
        ·
          refine ⟨601889790454202886351127553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401259860302801924234085035 601889790454202886351127553)
          ·
            refine ⟨451417342840652164763345665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 601889790454202886351127553 451417342840652164763345665)
            ·
              refine ⟨338563007130489123572509249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451417342840652164763345665 338563007130489123572509249)
              ·
                refine ⟨253922255347866842679381937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338563007130489123572509249 253922255347866842679381937)
                ·
                  refine ⟨190441691510900132009536453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 253922255347866842679381937 190441691510900132009536453)
                  ·
                    refine ⟨35707817158293774751788085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 190441691510900132009536453 35707817158293774751788085)
                    ·
                      refine ⟨3347607858590041382980133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 35707817158293774751788085 3347607858590041382980133)
                      ·
                        rfl

theorem cell23_6519443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_6519443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519443 prefixEnd_6519443 := by exact prefixLift 6519443
  have htrace : WordTrace (prefixWord ++ tailWord_6519443) baseStart_6519443 baseEnd_6519443 := by
    simpa [prefixWord, tailWord_6519443, baseEnd_6519443] using wordTrace_append hprefix tailTrace_6519443
  have hstable : (prefixWord ++ tailWord_6519443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519443).length < 2 ^ (prefixWord ++ tailWord_6519443).sum := by decide
  have hdescent : baseEnd_6519443 < baseStart_6519443 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519454 : List Nat := [4, 3, 1, 1, 1, 1, 5, 1, 6]
def baseStart_6519454 : Nat := 118140960795 + 6519454 * 2 ^ 59
def prefixEnd_6519454 : Nat := 4983230072969 + 3 ^ 40 * 6519454 * 2
def baseEnd_6519454 : Nat := 371957056319693426660287

theorem tailTrace_6519454 : CollatzResearch.WordTrace tailWord_6519454 prefixEnd_6519454 371957056319693426660287 := by
  unfold tailWord_6519454
  simp only [CollatzResearch.WordTrace]
  refine ⟨29723002765392383367911677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158522681415426044628862277 29723002765392383367911677)
  ·
    refine ⟨11146126037022143762966879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29723002765392383367911677 11146126037022143762966879)
    ·
      refine ⟨16719189055533215644450319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11146126037022143762966879 16719189055533215644450319)
      ·
        refine ⟨25078783583299823466675479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16719189055533215644450319 25078783583299823466675479)
        ·
          refine ⟨37618175374949735200013219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25078783583299823466675479 37618175374949735200013219)
          ·
            refine ⟨56427263062424602800019829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37618175374949735200013219 56427263062424602800019829)
            ·
              refine ⟨5290055912102306512501859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56427263062424602800019829 5290055912102306512501859)
              ·
                refine ⟨7935083868153459768752789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5290055912102306512501859 7935083868153459768752789)
                ·
                  refine ⟨371957056319693426660287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7935083868153459768752789 371957056319693426660287)
                  ·
                    rfl

theorem cell23_6519454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_6519454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519454 prefixEnd_6519454 := by exact prefixLift 6519454
  have htrace : WordTrace (prefixWord ++ tailWord_6519454) baseStart_6519454 baseEnd_6519454 := by
    simpa [prefixWord, tailWord_6519454, baseEnd_6519454] using wordTrace_append hprefix tailTrace_6519454
  have hstable : (prefixWord ++ tailWord_6519454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519454).length < 2 ^ (prefixWord ++ tailWord_6519454).sum := by decide
  have hdescent : baseEnd_6519454 < baseStart_6519454 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519487 : List Nat := [1, 1, 2, 2, 2, 4, 2, 3, 1, 1, 4]
def baseStart_6519487 : Nat := 118140960795 + 6519487 * 2 ^ 59
def prefixEnd_6519487 : Nat := 4983230072969 + 3 ^ 40 * 6519487 * 2
def baseEnd_6519487 : Nat := 3347630451738839210829931

theorem tailTrace_6519487 : CollatzResearch.WordTrace tailWord_6519487 prefixEnd_6519487 3347630451738839210829931 := by
  unfold tailWord_6519487
  simp only [CollatzResearch.WordTrace]
  refine ⟨237785225732019513579244715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158523483821346342386163143 237785225732019513579244715)
  ·
    refine ⟨356677838598029270368867073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237785225732019513579244715 356677838598029270368867073)
    ·
      refine ⟨267508378948521952776650305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356677838598029270368867073 267508378948521952776650305)
      ·
        refine ⟨200631284211391464582487729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267508378948521952776650305 200631284211391464582487729)
        ·
          refine ⟨150473463158543598436865797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 200631284211391464582487729 150473463158543598436865797)
          ·
            refine ⟨28213774342226924706912337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150473463158543598436865797 28213774342226924706912337)
            ·
              refine ⟨21160330756670193530184253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28213774342226924706912337 21160330756670193530184253)
              ·
                refine ⟨7935124033751322573819095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21160330756670193530184253 7935124033751322573819095)
                ·
                  refine ⟨11902686050626983860728643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7935124033751322573819095 11902686050626983860728643)
                  ·
                    refine ⟨17854029075940475791092965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11902686050626983860728643 17854029075940475791092965)
                    ·
                      refine ⟨3347630451738839210829931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17854029075940475791092965 3347630451738839210829931)
                      ·
                        rfl

theorem cell23_6519487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 1, 4].length) (baseStart_6519487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519487 prefixEnd_6519487 := by exact prefixLift 6519487
  have htrace : WordTrace (prefixWord ++ tailWord_6519487) baseStart_6519487 baseEnd_6519487 := by
    simpa [prefixWord, tailWord_6519487, baseEnd_6519487] using wordTrace_append hprefix tailTrace_6519487
  have hstable : (prefixWord ++ tailWord_6519487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519487).length < 2 ^ (prefixWord ++ tailWord_6519487).sum := by decide
  have hdescent : baseEnd_6519487 < baseStart_6519487 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519498 : List Nat := [3, 1, 2, 1, 4, 2, 3, 2, 1, 1, 3]
def baseStart_6519498 : Nat := 118140960795 + 6519498 * 2 ^ 59
def prefixEnd_6519498 : Nat := 4983230072969 + 3 ^ 40 * 6519498 * 2
def baseEnd_6519498 : Nat := 3347636100026038667792381

theorem tailTrace_6519498 : CollatzResearch.WordTrace tailWord_6519498 prefixEnd_6519498 3347636100026038667792381 := by
  unfold tailWord_6519498
  simp only [CollatzResearch.WordTrace]
  refine ⟨59446406733744915614473787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158523751289986441638596765 59446406733744915614473787)
  ·
    refine ⟨89169610100617373421710681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59446406733744915614473787 89169610100617373421710681)
    ·
      refine ⟨66877207575463030066283011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89169610100617373421710681 66877207575463030066283011)
      ·
        refine ⟨100315811363194545099424517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66877207575463030066283011 100315811363194545099424517)
        ·
          refine ⟨18809214630598977206142097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100315811363194545099424517 18809214630598977206142097)
          ·
            refine ⟨14106910972949232904606573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18809214630598977206142097 14106910972949232904606573)
            ·
              refine ⟨5290091614855962339227465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14106910972949232904606573 5290091614855962339227465)
              ·
                refine ⟨3967568711141971754420599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5290091614855962339227465 3967568711141971754420599)
                ·
                  refine ⟨5951353066712957631630899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967568711141971754420599 5951353066712957631630899)
                  ·
                    refine ⟨8927029600069436447446349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5951353066712957631630899 8927029600069436447446349)
                    ·
                      refine ⟨3347636100026038667792381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8927029600069436447446349 3347636100026038667792381)
                      ·
                        rfl

theorem cell23_6519498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3, 2, 1, 1, 3].length) (baseStart_6519498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519498 prefixEnd_6519498 := by exact prefixLift 6519498
  have htrace : WordTrace (prefixWord ++ tailWord_6519498) baseStart_6519498 baseEnd_6519498 := by
    simpa [prefixWord, tailWord_6519498, baseEnd_6519498] using wordTrace_append hprefix tailTrace_6519498
  have hstable : (prefixWord ++ tailWord_6519498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519498).length < 2 ^ (prefixWord ++ tailWord_6519498).sum := by decide
  have hdescent : baseEnd_6519498 < baseStart_6519498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519524 : List Nat := [2, 3, 1, 1, 1, 4, 3, 2, 1, 2, 3]
def baseStart_6519524 : Nat := 118140960795 + 6519524 * 2 ^ 59
def prefixEnd_6519524 : Nat := 4983230072969 + 3 ^ 40 * 6519524 * 2
def baseEnd_6519524 : Nat := 3347649450523055566067261

theorem tailTrace_6519524 : CollatzResearch.WordTrace tailWord_6519524 prefixEnd_6519524 3347649450523055566067261 := by
  unfold tailWord_6519524
  simp only [CollatzResearch.WordTrace]
  refine ⟨118893287616442734449170813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158524383488590312598894417 118893287616442734449170813)
  ·
    refine ⟨44584982856166025418439055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118893287616442734449170813 44584982856166025418439055)
    ·
      refine ⟨66877474284249038127658583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44584982856166025418439055 66877474284249038127658583)
      ·
        refine ⟨100316211426373557191487875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66877474284249038127658583 100316211426373557191487875)
        ·
          refine ⟨150474317139560335787231813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100316211426373557191487875 150474317139560335787231813)
          ·
            refine ⟨28213934463667562960105965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 150474317139560335787231813 28213934463667562960105965)
            ·
              refine ⟨10580225423875336110039737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28213934463667562960105965 10580225423875336110039737)
              ·
                refine ⟨7935169067906502082529803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10580225423875336110039737 7935169067906502082529803)
                ·
                  refine ⟨11902753601859753123794705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7935169067906502082529803 11902753601859753123794705)
                  ·
                    refine ⟨8927065201394814842846029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11902753601859753123794705 8927065201394814842846029)
                    ·
                      refine ⟨3347649450523055566067261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8927065201394814842846029 3347649450523055566067261)
                      ·
                        rfl

theorem cell23_6519524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_6519524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519524 prefixEnd_6519524 := by exact prefixLift 6519524
  have htrace : WordTrace (prefixWord ++ tailWord_6519524) baseStart_6519524 baseEnd_6519524 := by
    simpa [prefixWord, tailWord_6519524, baseEnd_6519524] using wordTrace_append hprefix tailTrace_6519524
  have hstable : (prefixWord ++ tailWord_6519524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519524).length < 2 ^ (prefixWord ++ tailWord_6519524).sum := by decide
  have hdescent : baseEnd_6519524 < baseStart_6519524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519537 : List Nat := [1, 2, 2, 2, 2, 2, 3, 2, 1, 3, 3]
def baseStart_6519537 : Nat := 118140960795 + 6519537 * 2 ^ 59
def prefixEnd_6519537 : Nat := 4983230072969 + 3 ^ 40 * 6519537 * 2
def baseEnd_6519537 : Nat := 3347656125771564015204701

theorem tailTrace_6519537 : CollatzResearch.WordTrace tailWord_6519537 prefixEnd_6519537 3347656125771564015204701 := by
  unfold tailWord_6519537
  simp only [CollatzResearch.WordTrace]
  refine ⟨237787049381838372118564865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158524699587892248079043243 237787049381838372118564865)
  ·
    refine ⟨178340287036378779088923649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237787049381838372118564865 178340287036378779088923649)
    ·
      refine ⟨133755215277284084316692737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178340287036378779088923649 133755215277284084316692737)
      ·
        refine ⟨100316411457963063237519553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133755215277284084316692737 100316411457963063237519553)
        ·
          refine ⟨75237308593472297428139665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100316411457963063237519553 75237308593472297428139665)
          ·
            refine ⟨56427981445104223071104749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75237308593472297428139665 56427981445104223071104749)
            ·
              refine ⟨21160493041914083651664281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56427981445104223071104749 21160493041914083651664281)
              ·
                refine ⟨15870369781435562738748211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21160493041914083651664281 15870369781435562738748211)
                ·
                  refine ⟨23805554672153344108122317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15870369781435562738748211 23805554672153344108122317)
                  ·
                    refine ⟨8927083002057504040545869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23805554672153344108122317 8927083002057504040545869)
                    ·
                      refine ⟨3347656125771564015204701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8927083002057504040545869 3347656125771564015204701)
                      ·
                        rfl

theorem cell23_6519537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 3, 3].length) (baseStart_6519537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519537 prefixEnd_6519537 := by exact prefixLift 6519537
  have htrace : WordTrace (prefixWord ++ tailWord_6519537) baseStart_6519537 baseEnd_6519537 := by
    simpa [prefixWord, tailWord_6519537, baseEnd_6519537] using wordTrace_append hprefix tailTrace_6519537
  have hstable : (prefixWord ++ tailWord_6519537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519537).length < 2 ^ (prefixWord ++ tailWord_6519537).sum := by decide
  have hdescent : baseEnd_6519537 < baseStart_6519537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519598 : List Nat := [4, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_6519598 : Nat := 118140960795 + 6519598 * 2 ^ 59
def prefixEnd_6519598 : Nat := 4983230072969 + 3 ^ 40 * 6519598 * 2
def baseEnd_6519598 : Nat := 3347687448091488276541921

theorem tailTrace_6519598 : CollatzResearch.WordTrace tailWord_6519598 prefixEnd_6519598 3347687448091488276541921 := by
  unfold tailWord_6519598
  simp only [CollatzResearch.WordTrace]
  refine ⟨29723659279327172442066931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158526182823078253024356965 29723659279327172442066931)
  ·
    refine ⟨44585488918990758663100397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29723659279327172442066931 44585488918990758663100397)
    ·
      refine ⟨16719558344621534498662649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44585488918990758663100397 16719558344621534498662649)
      ·
        refine ⟨12539668758466150873996987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16719558344621534498662649 12539668758466150873996987)
        ·
          refine ⟨18809503137699226310995481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12539668758466150873996987 18809503137699226310995481)
          ·
            refine ⟨14107127353274419733246611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18809503137699226310995481 14107127353274419733246611)
            ·
              refine ⟨21160691029911629599869917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14107127353274419733246611 21160691029911629599869917)
              ·
                refine ⟨7935259136216861099951219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21160691029911629599869917 7935259136216861099951219)
                ·
                  refine ⟨11902888704325291649926829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7935259136216861099951219 11902888704325291649926829)
                  ·
                    refine ⟨4463583264121984368722561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11902888704325291649926829 4463583264121984368722561)
                    ·
                      refine ⟨3347687448091488276541921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4463583264121984368722561 3347687448091488276541921)
                      ·
                        rfl

theorem cell23_6519598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_6519598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519598 prefixEnd_6519598 := by exact prefixLift 6519598
  have htrace : WordTrace (prefixWord ++ tailWord_6519598) baseStart_6519598 baseEnd_6519598 := by
    simpa [prefixWord, tailWord_6519598, baseEnd_6519598] using wordTrace_append hprefix tailTrace_6519598
  have hstable : (prefixWord ++ tailWord_6519598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519598).length < 2 ^ (prefixWord ++ tailWord_6519598).sum := by decide
  have hdescent : baseEnd_6519598 < baseStart_6519598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519622 : List Nat := [6, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_6519622 : Nat := 118140960795 + 6519622 * 2 ^ 59
def prefixEnd_6519622 : Nat := 4983230072969 + 3 ^ 40 * 6519622 * 2
def baseEnd_6519622 : Nat := 3347699771627196182641811

theorem tailTrace_6519622 : CollatzResearch.WordTrace tailWord_6519622 prefixEnd_6519622 3347699771627196182641811 := by
  unfold tailWord_6519622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7430942174579075988606535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158526766391020287756939413 7430942174579075988606535)
  ·
    refine ⟨11146413261868613982909803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7430942174579075988606535 11146413261868613982909803)
    ·
      refine ⟨16719619892802920974364705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11146413261868613982909803 16719619892802920974364705)
      ·
        refine ⟨12539714919602190730773529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16719619892802920974364705 12539714919602190730773529)
        ·
          refine ⟨9404786189701643048080147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12539714919602190730773529 9404786189701643048080147)
          ·
            refine ⟨14107179284552464572120221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9404786189701643048080147 14107179284552464572120221)
            ·
              refine ⟨5290192231707174214545083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14107179284552464572120221 5290192231707174214545083)
              ·
                refine ⟨7935288347560761321817625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5290192231707174214545083 7935288347560761321817625)
                ·
                  refine ⟨5951466260670570991363219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7935288347560761321817625 5951466260670570991363219)
                  ·
                    refine ⟨8927199391005856487044829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5951466260670570991363219 8927199391005856487044829)
                    ·
                      refine ⟨3347699771627196182641811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8927199391005856487044829 3347699771627196182641811)
                      ·
                        rfl

theorem cell23_6519622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_6519622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519622 prefixEnd_6519622 := by exact prefixLift 6519622
  have htrace : WordTrace (prefixWord ++ tailWord_6519622) baseStart_6519622 baseEnd_6519622 := by
    simpa [prefixWord, tailWord_6519622, baseEnd_6519622] using wordTrace_append hprefix tailTrace_6519622
  have hstable : (prefixWord ++ tailWord_6519622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519622).length < 2 ^ (prefixWord ++ tailWord_6519622).sum := by decide
  have hdescent : baseEnd_6519622 < baseStart_6519622 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519647 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 2, 5]
def baseStart_6519647 : Nat := 118140960795 + 6519647 * 2 ^ 59
def prefixEnd_6519647 : Nat := 4983230072969 + 3 ^ 40 * 6519647 * 2
def baseEnd_6519647 : Nat := 1115904202881186194943065

theorem tailTrace_6519647 : CollatzResearch.WordTrace tailWord_6519647 prefixEnd_6519647 1115904202881186194943065 := by
  unfold tailWord_6519647
  simp only [CollatzResearch.WordTrace]
  refine ⟨237791061411439860905069195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158527374274293240603379463 237791061411439860905069195)
  ·
    refine ⟨356686592117159791357603793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237791061411439860905069195 356686592117159791357603793)
    ·
      refine ⟨267514944087869843518202845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 356686592117159791357603793 267514944087869843518202845)
      ·
        refine ⟨100318104032951191319326067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267514944087869843518202845 100318104032951191319326067)
        ·
          refine ⟨150477156049426786978989101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100318104032951191319326067 150477156049426786978989101)
          ·
            refine ⟨56428933518535045117120913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150477156049426786978989101 56428933518535045117120913)
            ·
              refine ⟨42321700138901283837840685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56428933518535045117120913 42321700138901283837840685)
              ·
                refine ⟨15870637552087981439190257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42321700138901283837840685 15870637552087981439190257)
                ·
                  refine ⟨11902978164065986079392693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15870637552087981439190257 11902978164065986079392693)
                  ·
                    refine ⟨1115904202881186194943065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11902978164065986079392693 1115904202881186194943065)
                    ·
                      rfl

theorem cell23_6519647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 5].length) (baseStart_6519647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519647 prefixEnd_6519647 := by exact prefixLift 6519647
  have htrace : WordTrace (prefixWord ++ tailWord_6519647) baseStart_6519647 baseEnd_6519647 := by
    simpa [prefixWord, tailWord_6519647, baseEnd_6519647] using wordTrace_append hprefix tailTrace_6519647
  have hstable : (prefixWord ++ tailWord_6519647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519647).length < 2 ^ (prefixWord ++ tailWord_6519647).sum := by decide
  have hdescent : baseEnd_6519647 < baseStart_6519647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519651 : List Nat := [1, 1, 1, 5, 3, 3, 1, 3, 5]
def baseStart_6519651 : Nat := 118140960795 + 6519651 * 2 ^ 59
def prefixEnd_6519651 : Nat := 4983230072969 + 3 ^ 40 * 6519651 * 2
def baseEnd_6519651 : Nat := 371968295840686285464353

theorem tailTrace_6519651 : CollatzResearch.WordTrace tailWord_6519651 prefixEnd_6519651 371968295840686285464353 := by
  unfold tailWord_6519651
  simp only [CollatzResearch.WordTrace]
  refine ⟨237791207303425369588214807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158527471535616913058809871 237791207303425369588214807)
  ·
    refine ⟨356686810955138054382322211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237791207303425369588214807 356686810955138054382322211)
    ·
      refine ⟨535030216432707081573483317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356686810955138054382322211 535030216432707081573483317)
      ·
        refine ⟨50159082790566288897514061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 535030216432707081573483317 50159082790566288897514061)
        ·
          refine ⟨18809656046462358336567773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50159082790566288897514061 18809656046462358336567773)
          ·
            refine ⟨7053621017423384376212915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18809656046462358336567773 7053621017423384376212915)
            ·
              refine ⟨10580431526135076564319373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7053621017423384376212915 10580431526135076564319373)
              ·
                refine ⟨3967661822300653711619765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10580431526135076564319373 3967661822300653711619765)
                ·
                  refine ⟨371968295840686285464353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3967661822300653711619765 371968295840686285464353)
                  ·
                    rfl

theorem cell23_6519651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 1, 3, 5].length) (baseStart_6519651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519651 prefixEnd_6519651 := by exact prefixLift 6519651
  have htrace : WordTrace (prefixWord ++ tailWord_6519651) baseStart_6519651 baseEnd_6519651 := by
    simpa [prefixWord, tailWord_6519651, baseEnd_6519651] using wordTrace_append hprefix tailTrace_6519651
  have hstable : (prefixWord ++ tailWord_6519651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519651).length < 2 ^ (prefixWord ++ tailWord_6519651).sum := by decide
  have hdescent : baseEnd_6519651 < baseStart_6519651 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519667 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 4]
def baseStart_6519667 : Nat := 118140960795 + 6519667 * 2 ^ 59
def prefixEnd_6519667 : Nat := 4983230072969 + 3 ^ 40 * 6519667 * 2
def baseEnd_6519667 : Nat := 3347722878256648506579103

theorem tailTrace_6519667 : CollatzResearch.WordTrace tailWord_6519667 prefixEnd_6519667 3347722878256648506579103 := by
  unfold tailWord_6519667
  simp only [CollatzResearch.WordTrace]
  refine ⟨237791790871367404320797255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158527860580911602880531503 237791790871367404320797255)
  ·
    refine ⟨356687686307051106481195883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237791790871367404320797255 356687686307051106481195883)
    ·
      refine ⟨535031529460576659721793825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356687686307051106481195883 535031529460576659721793825)
      ·
        refine ⟨401273647095432494791345369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535031529460576659721793825 401273647095432494791345369)
        ·
          refine ⟨300955235321574371093509027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401273647095432494791345369 300955235321574371093509027)
          ·
            refine ⟨451432852982361556640263541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300955235321574371093509027 451432852982361556640263541)
            ·
              refine ⟨42321829967096395935024707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 451432852982361556640263541 42321829967096395935024707)
              ·
                refine ⟨63482744950644593902537061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42321829967096395935024707 63482744950644593902537061)
                ·
                  refine ⟨11903014678245861356725699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63482744950644593902537061 11903014678245861356725699)
                  ·
                    refine ⟨17854522017368792035088549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11903014678245861356725699 17854522017368792035088549)
                    ·
                      refine ⟨3347722878256648506579103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17854522017368792035088549 3347722878256648506579103)
                      ·
                        rfl

theorem cell23_6519667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_6519667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519667 prefixEnd_6519667 := by exact prefixLift 6519667
  have htrace : WordTrace (prefixWord ++ tailWord_6519667) baseStart_6519667 baseEnd_6519667 := by
    simpa [prefixWord, tailWord_6519667, baseEnd_6519667] using wordTrace_append hprefix tailTrace_6519667
  have hstable : (prefixWord ++ tailWord_6519667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519667).length < 2 ^ (prefixWord ++ tailWord_6519667).sum := by decide
  have hdescent : baseEnd_6519667 < baseStart_6519667 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519684 : List Nat := [2, 3, 2, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_6519684 : Nat := 118140960795 + 6519684 * 2 ^ 59
def prefixEnd_6519684 : Nat := 4983230072969 + 3 ^ 40 * 6519684 * 2
def baseEnd_6519684 : Nat := 3347731607427774940066525

theorem tailTrace_6519684 : CollatzResearch.WordTrace tailWord_6519684 prefixEnd_6519684 3347731607427774940066525 := by
  unfold tailWord_6519684
  simp only [CollatzResearch.WordTrace]
  refine ⟨118896205456152908112083053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158528273941537210816110737 118896205456152908112083053)
  ·
    refine ⟨44586077046057340542031145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 118896205456152908112083053 44586077046057340542031145)
    ·
      refine ⟨33439557784543005406523359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44586077046057340542031145 33439557784543005406523359)
      ·
        refine ⟨50159336676814508109785039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33439557784543005406523359 50159336676814508109785039)
        ·
          refine ⟨75239005015221762164677559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50159336676814508109785039 75239005015221762164677559)
          ·
            refine ⟨112858507522832643247016339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75239005015221762164677559 112858507522832643247016339)
            ·
              refine ⟨169287761284248964870524509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112858507522832643247016339 169287761284248964870524509)
              ·
                refine ⟨63482910481593361826446691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169287761284248964870524509 63482910481593361826446691)
                ·
                  refine ⟨95224365722390042739670037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63482910481593361826446691 95224365722390042739670037)
                  ·
                    refine ⟨4463642143237033253422033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 95224365722390042739670037 4463642143237033253422033)
                    ·
                      refine ⟨3347731607427774940066525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4463642143237033253422033 3347731607427774940066525)
                      ·
                        rfl

theorem cell23_6519684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_6519684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519684 prefixEnd_6519684 := by exact prefixLift 6519684
  have htrace : WordTrace (prefixWord ++ tailWord_6519684) baseStart_6519684 baseEnd_6519684 := by
    simpa [prefixWord, tailWord_6519684, baseEnd_6519684] using wordTrace_append hprefix tailTrace_6519684
  have hstable : (prefixWord ++ tailWord_6519684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519684).length < 2 ^ (prefixWord ++ tailWord_6519684).sum := by decide
  have hdescent : baseEnd_6519684 < baseStart_6519684 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519754 : List Nat := [3, 1, 2, 1, 2, 1, 1, 6, 1, 5]
def baseStart_6519754 : Nat := 118140960795 + 6519754 * 2 ^ 59
def prefixEnd_6519754 : Nat := 4983230072969 + 3 ^ 40 * 6519754 * 2
def baseEnd_6519754 : Nat := 1115922517024529888730401

theorem tailTrace_6519754 : CollatzResearch.WordTrace tailWord_6519754 prefixEnd_6519754 1115922517024529888730401 := by
  unfold tailWord_6519754
  simp only [CollatzResearch.WordTrace]
  refine ⟨59448741005513054544803579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158529976014701478786142877 59448741005513054544803579)
  ·
    refine ⟨89173111508269581817205369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59448741005513054544803579 89173111508269581817205369)
    ·
      refine ⟨66879833631202186362904027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89173111508269581817205369 66879833631202186362904027)
      ·
        refine ⟨100319750446803279544356041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66879833631202186362904027 100319750446803279544356041)
        ·
          refine ⟨75239812835102459658267031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100319750446803279544356041 75239812835102459658267031)
          ·
            refine ⟨112859719252653689487400547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75239812835102459658267031 112859719252653689487400547)
            ·
              refine ⟨169289578878980534231100821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112859719252653689487400547 169289578878980534231100821)
              ·
                refine ⟨7935449009952212542082851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 169289578878980534231100821 7935449009952212542082851)
                ·
                  refine ⟨11903173514928318813124277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7935449009952212542082851 11903173514928318813124277)
                  ·
                    refine ⟨1115922517024529888730401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11903173514928318813124277 1115922517024529888730401)
                    ·
                      rfl

theorem cell23_6519754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_6519754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519754 prefixEnd_6519754 := by exact prefixLift 6519754
  have htrace : WordTrace (prefixWord ++ tailWord_6519754) baseStart_6519754 baseEnd_6519754 := by
    simpa [prefixWord, tailWord_6519754, baseEnd_6519754] using wordTrace_append hprefix tailTrace_6519754
  have hstable : (prefixWord ++ tailWord_6519754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519754).length < 2 ^ (prefixWord ++ tailWord_6519754).sum := by decide
  have hdescent : baseEnd_6519754 < baseStart_6519754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519767 : List Nat := [1, 1, 3, 2, 1, 1, 2, 3, 3, 6]
def baseStart_6519767 : Nat := 118140960795 + 6519767 * 2 ^ 59
def prefixEnd_6519767 : Nat := 4983230072969 + 3 ^ 40 * 6519767 * 2
def baseEnd_6519767 : Nat := 1115924742107366038442881

theorem tailTrace_6519767 : CollatzResearch.WordTrace tailWord_6519767 prefixEnd_6519767 1115924742107366038442881 := by
  unfold tailWord_6519767
  simp only [CollatzResearch.WordTrace]
  refine ⟨237795438171005121399437555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158530292114003414266291703 237795438171005121399437555)
  ·
    refine ⟨356693157256507682099156333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237795438171005121399437555 356693157256507682099156333)
    ·
      refine ⟨133759933971190380787183625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356693157256507682099156333 133759933971190380787183625)
      ·
        refine ⟨100319950478392785590387719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133759933971190380787183625 100319950478392785590387719)
        ·
          refine ⟨150479925717589178385581579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100319950478392785590387719 150479925717589178385581579)
          ·
            refine ⟨225719888576383767578372369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150479925717589178385581579 225719888576383767578372369)
            ·
              refine ⟨169289916432287825683779277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 225719888576383767578372369 169289916432287825683779277)
              ·
                refine ⟨63483718662107934631417229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169289916432287825683779277 63483718662107934631417229)
                ·
                  refine ⟨23806394498290475486781461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63483718662107934631417229 23806394498290475486781461)
                  ·
                    refine ⟨1115924742107366038442881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23806394498290475486781461 1115924742107366038442881)
                    ·
                      rfl

theorem cell23_6519767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_6519767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519767 prefixEnd_6519767 := by exact prefixLift 6519767
  have htrace : WordTrace (prefixWord ++ tailWord_6519767) baseStart_6519767 baseEnd_6519767 := by
    simpa [prefixWord, tailWord_6519767, baseEnd_6519767] using wordTrace_append hprefix tailTrace_6519767
  have hstable : (prefixWord ++ tailWord_6519767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519767).length < 2 ^ (prefixWord ++ tailWord_6519767).sum := by decide
  have hdescent : baseEnd_6519767 < baseStart_6519767 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519768 : List Nat := [2, 1, 2, 2, 2, 3, 1, 5, 1, 1, 3]
def baseStart_6519768 : Nat := 118140960795 + 6519768 * 2 ^ 59
def prefixEnd_6519768 : Nat := 4983230072969 + 3 ^ 40 * 6519768 * 2
def baseEnd_6519768 : Nat := 3347774739802752611416139

theorem tailTrace_6519768 : CollatzResearch.WordTrace tailWord_6519768 prefixEnd_6519768 3347774739802752611416139 := by
  unfold tailWord_6519768
  simp only [CollatzResearch.WordTrace]
  refine ⟨118897737322000749285111979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158530316429334332380149305 118897737322000749285111979)
  ·
    refine ⟨178346605983001123927667969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118897737322000749285111979 178346605983001123927667969)
    ·
      refine ⟨133759954487250842945750977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178346605983001123927667969 133759954487250842945750977)
      ·
        refine ⟨100319965865438132209313233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133759954487250842945750977 100319965865438132209313233)
        ·
          refine ⟨75239974399078599156984925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100319965865438132209313233 75239974399078599156984925)
          ·
            refine ⟨28214990399654474683869347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75239974399078599156984925 28214990399654474683869347)
            ·
              refine ⟨42322485599481712025804021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28214990399654474683869347 42322485599481712025804021)
              ·
                refine ⟨3967733024951410502419127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42322485599481712025804021 3967733024951410502419127)
                ·
                  refine ⟨5951599537427115753628691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967733024951410502419127 5951599537427115753628691)
                  ·
                    refine ⟨8927399306140673630443037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5951599537427115753628691 8927399306140673630443037)
                    ·
                      refine ⟨3347774739802752611416139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8927399306140673630443037 3347774739802752611416139)
                      ·
                        rfl

theorem cell23_6519768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 1, 5, 1, 1, 3].length) (baseStart_6519768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519768 prefixEnd_6519768 := by exact prefixLift 6519768
  have htrace : WordTrace (prefixWord ++ tailWord_6519768) baseStart_6519768 baseEnd_6519768 := by
    simpa [prefixWord, tailWord_6519768, baseEnd_6519768] using wordTrace_append hprefix tailTrace_6519768
  have hstable : (prefixWord ++ tailWord_6519768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519768).length < 2 ^ (prefixWord ++ tailWord_6519768).sum := by decide
  have hdescent : baseEnd_6519768 < baseStart_6519768 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519787 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 4]
def baseStart_6519787 : Nat := 118140960795 + 6519787 * 2 ^ 59
def prefixEnd_6519787 : Nat := 4983230072969 + 3 ^ 40 * 6519787 * 2
def baseEnd_6519787 : Nat := 3347784495935188037078551

theorem tailTrace_6519787 : CollatzResearch.WordTrace tailWord_6519787 prefixEnd_6519787 3347784495935188037078551 := by
  unfold tailWord_6519787
  simp only [CollatzResearch.WordTrace]
  refine ⟨237796167630932664815165615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158530778420621776543443743 237796167630932664815165615)
  ·
    refine ⟨356694251446398997222748423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237796167630932664815165615 356694251446398997222748423)
    ·
      refine ⟨535041377169598495834122635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356694251446398997222748423 535041377169598495834122635)
      ·
        refine ⟨802562065754397743751183953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535041377169598495834122635 802562065754397743751183953)
        ·
          refine ⟨601921549315798307813387965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 802562065754397743751183953 601921549315798307813387965)
          ·
            refine ⟨225720580993424365430020487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 601921549315798307813387965 225720580993424365430020487)
            ·
              refine ⟨338580871490136548145030731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225720580993424365430020487 338580871490136548145030731)
              ·
                refine ⟨507871307235204822217546097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338580871490136548145030731 507871307235204822217546097)
                ·
                  refine ⟨380903480426403616663159573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507871307235204822217546097 380903480426403616663159573)
                  ·
                    refine ⟨17854850644987669531085605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 380903480426403616663159573 17854850644987669531085605)
                    ·
                      refine ⟨3347784495935188037078551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17854850644987669531085605 3347784495935188037078551)
                      ·
                        rfl

theorem cell23_6519787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 6, 4].length) (baseStart_6519787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519787 prefixEnd_6519787 := by exact prefixLift 6519787
  have htrace : WordTrace (prefixWord ++ tailWord_6519787) baseStart_6519787 baseEnd_6519787 := by
    simpa [prefixWord, tailWord_6519787, baseEnd_6519787] using wordTrace_append hprefix tailTrace_6519787
  have hstable : (prefixWord ++ tailWord_6519787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519787).length < 2 ^ (prefixWord ++ tailWord_6519787).sum := by decide
  have hdescent : baseEnd_6519787 < baseStart_6519787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519804 : List Nat := [2, 2, 2, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_6519804 : Nat := 118140960795 + 6519804 * 2 ^ 59
def prefixEnd_6519804 : Nat := 4983230072969 + 3 ^ 40 * 6519804 * 2
def baseEnd_6519804 : Nat := 3347793225106314470565973

theorem tailTrace_6519804 : CollatzResearch.WordTrace tailWord_6519804 prefixEnd_6519804 3347793225106314470565973 := by
  unfold tailWord_6519804
  simp only [CollatzResearch.WordTrace]
  refine ⟨118898393835935538359267233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158531191781247384479022977 118898393835935538359267233)
  ·
    refine ⟨89173795376951653769450425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118898393835935538359267233 89173795376951653769450425)
    ·
      refine ⟨66880346532713740327087819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89173795376951653769450425 66880346532713740327087819)
      ·
        refine ⟨100320519799070610490631729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66880346532713740327087819 100320519799070610490631729)
        ·
          refine ⟨75240389849302957867973797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100320519799070610490631729 75240389849302957867973797)
          ·
            refine ⟨14107573096744304600245087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75240389849302957867973797 14107573096744304600245087)
            ·
              refine ⟨21161359645116456900367631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14107573096744304600245087 21161359645116456900367631)
              ·
                refine ⟨31742039467674685350551447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21161359645116456900367631 31742039467674685350551447)
                ·
                  refine ⟨47613059201512028025827171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31742039467674685350551447 47613059201512028025827171)
                  ·
                    refine ⟨71419588802268042038740757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47613059201512028025827171 71419588802268042038740757)
                    ·
                      refine ⟨3347793225106314470565973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71419588802268042038740757 3347793225106314470565973)
                      ·
                        rfl

theorem cell23_6519804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_6519804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519804 prefixEnd_6519804 := by exact prefixLift 6519804
  have htrace : WordTrace (prefixWord ++ tailWord_6519804) baseStart_6519804 baseEnd_6519804 := by
    simpa [prefixWord, tailWord_6519804, baseEnd_6519804] using wordTrace_append hprefix tailTrace_6519804
  have hstable : (prefixWord ++ tailWord_6519804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519804).length < 2 ^ (prefixWord ++ tailWord_6519804).sum := by decide
  have hdescent : baseEnd_6519804 < baseStart_6519804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519817 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 6]
def baseStart_6519817 : Nat := 118140960795 + 6519817 * 2 ^ 59
def prefixEnd_6519817 : Nat := 4983230072969 + 3 ^ 40 * 6519817 * 2
def baseEnd_6519817 : Nat := 3347799900354822919703413

theorem tailTrace_6519817 : CollatzResearch.WordTrace tailWord_6519817 prefixEnd_6519817 3347799900354822919703413 := by
  unfold tailWord_6519817
  simp only [CollatzResearch.WordTrace]
  refine ⟨237797261820823979938757705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158531507880549319959171803 237797261820823979938757705)
  ·
    refine ⟨178347946365617984954068279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237797261820823979938757705 178347946365617984954068279)
    ·
      refine ⟨267521919548426977431102419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178347946365617984954068279 267521919548426977431102419)
      ·
        refine ⟨401282879322640466146653629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267521919548426977431102419 401282879322640466146653629)
        ·
          refine ⟨150481079745990174804995111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 401282879322640466146653629 150481079745990174804995111)
          ·
            refine ⟨225721619618985262207492667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150481079745990174804995111 225721619618985262207492667)
            ·
              refine ⟨338582429428477893311239001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 225721619618985262207492667 338582429428477893311239001)
              ·
                refine ⟨253936822071358419983429251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338582429428477893311239001 253936822071358419983429251)
                ·
                  refine ⟨380905233107037629975143877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253936822071358419983429251 380905233107037629975143877)
                  ·
                    refine ⟨71419731207569555620339477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 380905233107037629975143877 71419731207569555620339477)
                    ·
                      refine ⟨3347799900354822919703413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71419731207569555620339477 3347799900354822919703413)
                      ·
                        rfl

theorem cell23_6519817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 4, 6].length) (baseStart_6519817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519817 prefixEnd_6519817 := by exact prefixLift 6519817
  have htrace : WordTrace (prefixWord ++ tailWord_6519817) baseStart_6519817 baseEnd_6519817 := by
    simpa [prefixWord, tailWord_6519817, baseEnd_6519817] using wordTrace_append hprefix tailTrace_6519817
  have hstable : (prefixWord ++ tailWord_6519817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519817).length < 2 ^ (prefixWord ++ tailWord_6519817).sum := by decide
  have hdescent : baseEnd_6519817 < baseStart_6519817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519827 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 1, 9]
def baseStart_6519827 : Nat := 118140960795 + 6519827 * 2 ^ 59
def prefixEnd_6519827 : Nat := 4983230072969 + 3 ^ 40 * 6519827 * 2
def baseEnd_6519827 : Nat := 1115935011720455960192789

theorem tailTrace_6519827 : CollatzResearch.WordTrace tailWord_6519827 prefixEnd_6519827 1115935011720455960192789 := by
  unfold tailWord_6519827
  simp only [CollatzResearch.WordTrace]
  refine ⟨237797626550787751646621735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158531751033858501097747823 237797626550787751646621735)
  ·
    refine ⟨356696439826181627469932603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237797626550787751646621735 356696439826181627469932603)
    ·
      refine ⟨535044659739272441204898905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356696439826181627469932603 535044659739272441204898905)
      ·
        refine ⟨401283494804454330903674179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 535044659739272441204898905 401283494804454330903674179)
        ·
          refine ⟨601925242206681496355511269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401283494804454330903674179 601925242206681496355511269)
          ·
            refine ⟨112860982913752780566658363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 601925242206681496355511269 112860982913752780566658363)
            ·
              refine ⟨169291474370629170849987545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 112860982913752780566658363 169291474370629170849987545)
              ·
                refine ⟨126968605777971878137490659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169291474370629170849987545 126968605777971878137490659)
                ·
                  refine ⟨190452908666957817206235989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 126968605777971878137490659 190452908666957817206235989)
                  ·
                    refine ⟨1115935011720455960192789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 190452908666957817206235989 1115935011720455960192789)
                    ·
                      rfl

theorem cell23_6519827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 9].length) (baseStart_6519827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519827 prefixEnd_6519827 := by exact prefixLift 6519827
  have htrace : WordTrace (prefixWord ++ tailWord_6519827) baseStart_6519827 baseEnd_6519827 := by
    simpa [prefixWord, tailWord_6519827, baseEnd_6519827] using wordTrace_append hprefix tailTrace_6519827
  have hstable : (prefixWord ++ tailWord_6519827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519827).length < 2 ^ (prefixWord ++ tailWord_6519827).sum := by decide
  have hdescent : baseEnd_6519827 < baseStart_6519827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519851 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 3, 3, 2]
def baseStart_6519851 : Nat := 118140960795 + 6519851 * 2 ^ 59
def prefixEnd_6519851 : Nat := 4983230072969 + 3 ^ 40 * 6519851 * 2
def baseEnd_6519851 : Nat := 3347817358697075786678257

theorem tailTrace_6519851 : CollatzResearch.WordTrace tailWord_6519851 prefixEnd_6519851 3347817358697075786678257 := by
  unfold tailWord_6519851
  simp only [CollatzResearch.WordTrace]
  refine ⟨237798501902700803745495407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158532334601800535830330271 237798501902700803745495407)
  ·
    refine ⟨356697752854051205618243111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237798501902700803745495407 356697752854051205618243111)
    ·
      refine ⟨535046629281076808427364667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 356697752854051205618243111 535046629281076808427364667)
      ·
        refine ⟨802569943921615212641047001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 535046629281076808427364667 802569943921615212641047001)
        ·
          refine ⟨601927457941211409480785251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 802569943921615212641047001 601927457941211409480785251)
          ·
            refine ⟨902891186911817114221177877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 601927457941211409480785251 902891186911817114221177877)
            ·
              refine ⟨42323024386491427229117713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 902891186911817114221177877 42323024386491427229117713)
              ·
                refine ⟨31742268289868570421838285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42323024386491427229117713 31742268289868570421838285)
                ·
                  refine ⟨11903350608700713908189357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31742268289868570421838285 11903350608700713908189357)
                  ·
                    refine ⟨4463756478262767715571009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11903350608700713908189357 4463756478262767715571009)
                    ·
                      refine ⟨3347817358697075786678257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4463756478262767715571009 3347817358697075786678257)
                      ·
                        rfl

theorem cell23_6519851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 3, 3, 2].length) (baseStart_6519851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519851 prefixEnd_6519851 := by exact prefixLift 6519851
  have htrace : WordTrace (prefixWord ++ tailWord_6519851) baseStart_6519851 baseEnd_6519851 := by
    simpa [prefixWord, tailWord_6519851, baseEnd_6519851] using wordTrace_append hprefix tailTrace_6519851
  have hstable : (prefixWord ++ tailWord_6519851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519851).length < 2 ^ (prefixWord ++ tailWord_6519851).sum := by decide
  have hdescent : baseEnd_6519851 < baseStart_6519851 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519858 : List Nat := [3, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3]
def baseStart_6519858 : Nat := 118140960795 + 6519858 * 2 ^ 59
def prefixEnd_6519858 : Nat := 4983230072969 + 3 ^ 40 * 6519858 * 2
def baseEnd_6519858 : Nat := 3347820953061657259290725

theorem tailTrace_6519858 : CollatzResearch.WordTrace tailWord_6519858 prefixEnd_6519858 3347820953061657259290725 := by
  unfold tailWord_6519858
  simp only [CollatzResearch.WordTrace]
  refine ⟨59449689303418860985250057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158532504809116962627333485 59449689303418860985250057)
  ·
    refine ⟨44587266977564145738937543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59449689303418860985250057 44587266977564145738937543)
    ·
      refine ⟨66880900466346218608406315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44587266977564145738937543 66880900466346218608406315)
      ·
        refine ⟨100321350699519327912609473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66880900466346218608406315 100321350699519327912609473)
        ·
          refine ⟨75241013024639495934457105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100321350699519327912609473 75241013024639495934457105)
          ·
            refine ⟨56430759768479621950842829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75241013024639495934457105 56430759768479621950842829)
            ·
              refine ⟨21161534913179858231566061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56430759768479621950842829 21161534913179858231566061)
              ·
                refine ⟨7935575592442446836837273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21161534913179858231566061 7935575592442446836837273)
                ·
                  refine ⟨5951681694331835127627955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7935575592442446836837273 5951681694331835127627955)
                  ·
                    refine ⟨8927522541497752691441933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5951681694331835127627955 8927522541497752691441933)
                    ·
                      refine ⟨3347820953061657259290725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8927522541497752691441933 3347820953061657259290725)
                      ·
                        rfl

theorem cell23_6519858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_6519858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519858 prefixEnd_6519858 := by exact prefixLift 6519858
  have htrace : WordTrace (prefixWord ++ tailWord_6519858) baseStart_6519858 baseEnd_6519858 := by
    simpa [prefixWord, tailWord_6519858, baseEnd_6519858] using wordTrace_append hprefix tailTrace_6519858
  have hstable : (prefixWord ++ tailWord_6519858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519858).length < 2 ^ (prefixWord ++ tailWord_6519858).sum := by decide
  have hdescent : baseEnd_6519858 < baseStart_6519858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519868 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 3, 3, 2]
def baseStart_6519868 : Nat := 118140960795 + 6519868 * 2 ^ 59
def prefixEnd_6519868 : Nat := 4983230072969 + 3 ^ 40 * 6519868 * 2
def baseEnd_6519868 : Nat := 3347826087868202220165679

theorem tailTrace_6519868 : CollatzResearch.WordTrace tailWord_6519868 prefixEnd_6519868 3347826087868202220165679 := by
  unfold tailWord_6519868
  simp only [CollatzResearch.WordTrace]
  refine ⟨118899560971819607824432129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158532747962426143765909505 118899560971819607824432129)
  ·
    refine ⟨89174670728864705868324097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 118899560971819607824432129 89174670728864705868324097)
    ·
      refine ⟨66881003046648529401243073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89174670728864705868324097 66881003046648529401243073)
      ·
        refine ⟨50160752284986397050932305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66881003046648529401243073 50160752284986397050932305)
        ·
          refine ⟨37620564213739797788199229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50160752284986397050932305 37620564213739797788199229)
          ·
            refine ⟨14107711580152424170574711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37620564213739797788199229 14107711580152424170574711)
            ·
              refine ⟨21161567370228636255862067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14107711580152424170574711 21161567370228636255862067)
              ·
                refine ⟨31742351055342954383793101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21161567370228636255862067 31742351055342954383793101)
                ·
                  refine ⟨11903381645753607893922413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31742351055342954383793101 11903381645753607893922413)
                  ·
                    refine ⟨4463768117157602960220905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11903381645753607893922413 4463768117157602960220905)
                    ·
                      refine ⟨3347826087868202220165679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4463768117157602960220905 3347826087868202220165679)
                      ·
                        rfl

theorem cell23_6519868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_6519868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519868 prefixEnd_6519868 := by exact prefixLift 6519868
  have htrace : WordTrace (prefixWord ++ tailWord_6519868) baseStart_6519868 baseEnd_6519868 := by
    simpa [prefixWord, tailWord_6519868, baseEnd_6519868] using wordTrace_append hprefix tailTrace_6519868
  have hstable : (prefixWord ++ tailWord_6519868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519868).length < 2 ^ (prefixWord ++ tailWord_6519868).sum := by decide
  have hdescent : baseEnd_6519868 < baseStart_6519868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519902 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 3, 3, 2]
def baseStart_6519902 : Nat := 118140960795 + 6519902 * 2 ^ 59
def prefixEnd_6519902 : Nat := 4983230072969 + 3 ^ 40 * 6519902 * 2
def baseEnd_6519902 : Nat := 3347843546210455087140523

theorem tailTrace_6519902 : CollatzResearch.WordTrace tailWord_6519902 prefixEnd_6519902 3347843546210455087140523 := by
  unfold tailWord_6519902
  simp only [CollatzResearch.WordTrace]
  refine ⟨29725045253189504931950245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158533574683677359637067973 29725045253189504931950245)
  ·
    refine ⟨5573445984973032174740671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29725045253189504931950245 5573445984973032174740671)
    ·
      refine ⟨8360168977459548262111007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5573445984973032174740671 8360168977459548262111007)
      ·
        refine ⟨12540253466189322393166511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8360168977459548262111007 12540253466189322393166511)
        ·
          refine ⟨18810380199283983589749767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12540253466189322393166511 18810380199283983589749767)
          ·
            refine ⟨28215570298925975384624651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18810380199283983589749767 28215570298925975384624651)
            ·
              refine ⟨42323355448388963076936977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28215570298925975384624651 42323355448388963076936977)
              ·
                refine ⟨31742516586291722307702733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42323355448388963076936977 31742516586291722307702733)
                ·
                  refine ⟨11903443719859395865388525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31742516586291722307702733 11903443719859395865388525)
                  ·
                    refine ⟨4463791394947273449520697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11903443719859395865388525 4463791394947273449520697)
                    ·
                      refine ⟨3347843546210455087140523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4463791394947273449520697 3347843546210455087140523)
                      ·
                        rfl

theorem cell23_6519902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_6519902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519902 prefixEnd_6519902 := by exact prefixLift 6519902
  have htrace : WordTrace (prefixWord ++ tailWord_6519902) baseStart_6519902 baseEnd_6519902 := by
    simpa [prefixWord, tailWord_6519902, baseEnd_6519902] using wordTrace_append hprefix tailTrace_6519902
  have hstable : (prefixWord ++ tailWord_6519902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519902).length < 2 ^ (prefixWord ++ tailWord_6519902).sum := by decide
  have hdescent : baseEnd_6519902 < baseStart_6519902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519904 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 7]
def baseStart_6519904 : Nat := 118140960795 + 6519904 * 2 ^ 59
def prefixEnd_6519904 : Nat := 4983230072969 + 3 ^ 40 * 6519904 * 2
def baseEnd_6519904 : Nat := 371982730352418231035057

theorem tailTrace_6519904 : CollatzResearch.WordTrace tailWord_6519904 prefixEnd_6519904 371982730352418231035057 := by
  unfold tailWord_6519904
  simp only [CollatzResearch.WordTrace]
  refine ⟨118900217485754396898587383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158533623314339195864783177 118900217485754396898587383)
  ·
    refine ⟨178350326228631595347881075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118900217485754396898587383 178350326228631595347881075)
    ·
      refine ⟨267525489342947393021821613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178350326228631595347881075 267525489342947393021821613)
      ·
        refine ⟨100322058503605272383183105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267525489342947393021821613 100322058503605272383183105)
        ·
          refine ⟨75241543877703954287387329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100322058503605272383183105 75241543877703954287387329)
          ·
            refine ⟨56431157908277965715540497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75241543877703954287387329 56431157908277965715540497)
            ·
              refine ⟨42323368431208474286655373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56431157908277965715540497 42323368431208474286655373)
              ·
                refine ⟨15871263161703177857495765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42323368431208474286655373 15871263161703177857495765)
                ·
                  refine ⟨371982730352418231035057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15871263161703177857495765 371982730352418231035057)
                  ·
                    rfl

theorem cell23_6519904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 7].length) (baseStart_6519904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519904 prefixEnd_6519904 := by exact prefixLift 6519904
  have htrace : WordTrace (prefixWord ++ tailWord_6519904) baseStart_6519904 baseEnd_6519904 := by
    simpa [prefixWord, tailWord_6519904, baseEnd_6519904] using wordTrace_append hprefix tailTrace_6519904
  have hstable : (prefixWord ++ tailWord_6519904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519904).length < 2 ^ (prefixWord ++ tailWord_6519904).sum := by decide
  have hdescent : baseEnd_6519904 < baseStart_6519904 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519911 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_6519911 : Nat := 118140960795 + 6519911 * 2 ^ 59
def prefixEnd_6519911 : Nat := 4983230072969 + 3 ^ 40 * 6519911 * 2
def baseEnd_6519911 : Nat := 3347848167536345551927981

theorem tailTrace_6519911 : CollatzResearch.WordTrace tailWord_6519911 prefixEnd_6519911 3347848167536345551927981 := by
  unfold tailWord_6519911
  simp only [CollatzResearch.WordTrace]
  refine ⟨237800690282483433992679587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158533793521655622661786391 237800690282483433992679587)
  ·
    refine ⟨356701035423725150989019381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237800690282483433992679587 356701035423725150989019381)
    ·
      refine ⟨33440722070974232905220567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 356701035423725150989019381 33440722070974232905220567)
      ·
        refine ⟨50161083106461349357830851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33440722070974232905220567 50161083106461349357830851)
        ·
          refine ⟨75241624659692024036746277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50161083106461349357830851 75241624659692024036746277)
          ·
            refine ⟨14107804623692254506889927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75241624659692024036746277 14107804623692254506889927)
            ·
              refine ⟨21161706935538381760334891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14107804623692254506889927 21161706935538381760334891)
              ·
                refine ⟨31742560403307572640502337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21161706935538381760334891 31742560403307572640502337)
                ·
                  refine ⟨23806920302480679480376753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31742560403307572640502337 23806920302480679480376753)
                  ·
                    refine ⟨17855190226860509610282565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23806920302480679480376753 17855190226860509610282565)
                    ·
                      refine ⟨3347848167536345551927981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17855190226860509610282565 3347848167536345551927981)
                      ·
                        rfl

theorem cell23_6519911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_6519911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519911 prefixEnd_6519911 := by exact prefixLift 6519911
  have htrace : WordTrace (prefixWord ++ tailWord_6519911) baseStart_6519911 baseEnd_6519911 := by
    simpa [prefixWord, tailWord_6519911, baseEnd_6519911] using wordTrace_append hprefix tailTrace_6519911
  have hstable : (prefixWord ++ tailWord_6519911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519911).length < 2 ^ (prefixWord ++ tailWord_6519911).sum := by decide
  have hdescent : baseEnd_6519911 < baseStart_6519911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519984 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 6]
def baseStart_6519984 : Nat := 118140960795 + 6519984 * 2 ^ 59
def prefixEnd_6519984 : Nat := 4983230072969 + 3 ^ 40 * 6519984 * 2
def baseEnd_6519984 : Nat := 3347885651624123766315145

theorem tailTrace_6519984 : CollatzResearch.WordTrace tailWord_6519984 prefixEnd_6519984 3347885651624123766315145 := by
  unfold tailWord_6519984
  simp only [CollatzResearch.WordTrace]
  refine ⟨118901676405609483730043503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 158535568540812644973391337 118901676405609483730043503)
  ·
    refine ⟨178352514608414225595065255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 118901676405609483730043503 178352514608414225595065255)
    ·
      refine ⟨267528771912621338392597883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178352514608414225595065255 267528771912621338392597883)
      ·
        refine ⟨401293157868932007588896825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267528771912621338392597883 401293157868932007588896825)
        ·
          refine ⟨300969868401699005691672619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 401293157868932007588896825 300969868401699005691672619)
          ·
            refine ⟨451454802602548508537508929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300969868401699005691672619 451454802602548508537508929)
            ·
              refine ⟨338591101951911381403131697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451454802602548508537508929 338591101951911381403131697)
              ·
                refine ⟨253943326463933536052348773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338591101951911381403131697 253943326463933536052348773)
                ·
                  refine ⟨47614373711987538009815395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 253943326463933536052348773 47614373711987538009815395)
                  ·
                    refine ⟨71421560567981307014723093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 47614373711987538009815395 71421560567981307014723093)
                    ·
                      refine ⟨3347885651624123766315145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 71421560567981307014723093 3347885651624123766315145)
                      ·
                        rfl

theorem cell23_6519984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_6519984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519984 prefixEnd_6519984 := by exact prefixLift 6519984
  have htrace : WordTrace (prefixWord ++ tailWord_6519984) baseStart_6519984 baseEnd_6519984 := by
    simpa [prefixWord, tailWord_6519984, baseEnd_6519984] using wordTrace_append hprefix tailTrace_6519984
  have hstable : (prefixWord ++ tailWord_6519984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519984).length < 2 ^ (prefixWord ++ tailWord_6519984).sum := by decide
  have hdescent : baseEnd_6519984 < baseStart_6519984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6519991 : List Nat := [1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 3]
def baseStart_6519991 : Nat := 118140960795 + 6519991 * 2 ^ 59
def prefixEnd_6519991 : Nat := 4983230072969 + 3 ^ 40 * 6519991 * 2
def baseEnd_6519991 : Nat := 3347889245988705238927613

theorem tailTrace_6519991 : CollatzResearch.WordTrace tailWord_6519991 prefixEnd_6519991 3347889245988705238927613 := by
  unfold tailWord_6519991
  simp only [CollatzResearch.WordTrace]
  refine ⟨237803608122193607655591827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158535738748129071770394551 237803608122193607655591827)
  ·
    refine ⟨356705412183290411483387741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 237803608122193607655591827 356705412183290411483387741)
    ·
      refine ⟨133764529568733904306270403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 356705412183290411483387741 133764529568733904306270403)
      ·
        refine ⟨200646794353100856459405605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133764529568733904306270403 200646794353100856459405605)
        ·
          refine ⟨37621273941206410586138551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 200646794353100856459405605 37621273941206410586138551)
          ·
            refine ⟨56431910911809615879207827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37621273941206410586138551 56431910911809615879207827)
            ·
              refine ⟨84647866367714423818811741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56431910911809615879207827 84647866367714423818811741)
              ·
                refine ⟨31742949887892908932054403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84647866367714423818811741 31742949887892908932054403)
                ·
                  refine ⟨47614424831839363398081605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31742949887892908932054403 47614424831839363398081605)
                  ·
                    refine ⟨8927704655969880637140301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 47614424831839363398081605 8927704655969880637140301)
                    ·
                      refine ⟨3347889245988705238927613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8927704655969880637140301 3347889245988705238927613)
                      ·
                        rfl

theorem cell23_6519991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_6519991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6519991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6519991 prefixEnd_6519991 := by exact prefixLift 6519991
  have htrace : WordTrace (prefixWord ++ tailWord_6519991) baseStart_6519991 baseEnd_6519991 := by
    simpa [prefixWord, tailWord_6519991, baseEnd_6519991] using wordTrace_append hprefix tailTrace_6519991
  have hstable : (prefixWord ++ tailWord_6519991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6519991).length < 2 ^ (prefixWord ++ tailWord_6519991).sum := by decide
  have hdescent : baseEnd_6519991 < baseStart_6519991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6519991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520002 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_6520002 : Nat := 118140960795 + 6520002 * 2 ^ 59
def prefixEnd_6520002 : Nat := 4983230072969 + 3 ^ 40 * 6520002 * 2
def baseEnd_6520002 : Nat := 1115964964758634898630021

theorem tailTrace_6520002 : CollatzResearch.WordTrace tailWord_6520002 prefixEnd_6520002 1115964964758634898630021 := by
  unfold tailWord_6520002
  simp only [CollatzResearch.WordTrace]
  refine ⟨59451002331288439133560565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158536006216769171022828173 59451002331288439133560565)
  ·
    refine ⟨5573531468558291168771303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59451002331288439133560565 5573531468558291168771303)
    ·
      refine ⟨8360297202837436753156955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5573531468558291168771303 8360297202837436753156955)
      ·
        refine ⟨12540445804256155129735433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8360297202837436753156955 12540445804256155129735433)
        ·
          refine ⟨9405334353192116347301575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12540445804256155129735433 9405334353192116347301575)
          ·
            refine ⟨14108001529788174520952363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9405334353192116347301575 14108001529788174520952363)
            ·
              refine ⟨21162002294682261781428545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14108001529788174520952363 21162002294682261781428545)
              ·
                refine ⟨15871501721011696336071409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21162002294682261781428545 15871501721011696336071409)
                ·
                  refine ⟨11903626290758772252053557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15871501721011696336071409 11903626290758772252053557)
                  ·
                    refine ⟨1115964964758634898630021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11903626290758772252053557 1115964964758634898630021)
                    ·
                      rfl

theorem cell23_6520002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_6520002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520002 prefixEnd_6520002 := by exact prefixLift 6520002
  have htrace : WordTrace (prefixWord ++ tailWord_6520002) baseStart_6520002 baseEnd_6520002 := by
    simpa [prefixWord, tailWord_6520002, baseEnd_6520002] using wordTrace_append hprefix tailTrace_6520002
  have hstable : (prefixWord ++ tailWord_6520002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520002).length < 2 ^ (prefixWord ++ tailWord_6520002).sum := by decide
  have hdescent : baseEnd_6520002 < baseStart_6520002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520006 : List Nat := [6, 1, 2, 2, 1, 1, 3, 2, 5]
def baseStart_6520006 : Nat := 118140960795 + 6520006 * 2 ^ 59
def prefixEnd_6520006 : Nat := 4983230072969 + 3 ^ 40 * 6520006 * 2
def baseEnd_6520006 : Nat := 371988549799835853360005

theorem tailTrace_6520006 : CollatzResearch.WordTrace tailWord_6520006 prefixEnd_6520006 371988549799835853360005 := by
  unfold tailWord_6520006
  simp only [CollatzResearch.WordTrace]
  refine ⟨7431379850535602038043371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 158536103478092843478258581 7431379850535602038043371)
  ·
    refine ⟨11147069775803403057065057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7431379850535602038043371 11147069775803403057065057)
    ·
      refine ⟨8360302331852552292798793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11147069775803403057065057 8360302331852552292798793)
      ·
        refine ⟨6270226748889414219599095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8360302331852552292798793 6270226748889414219599095)
        ·
          refine ⟨9405340123334121329398643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6270226748889414219599095 9405340123334121329398643)
          ·
            refine ⟨14108010185001181994097965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9405340123334121329398643 14108010185001181994097965)
            ·
              refine ⟨5290503819375443247786737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14108010185001181994097965 5290503819375443247786737)
              ·
                refine ⟨3967877864531582435840053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5290503819375443247786737 3967877864531582435840053)
                ·
                  refine ⟨371988549799835853360005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3967877864531582435840053 371988549799835853360005)
                  ·
                    rfl

theorem cell23_6520006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 5].length) (baseStart_6520006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520006 prefixEnd_6520006 := by exact prefixLift 6520006
  have htrace : WordTrace (prefixWord ++ tailWord_6520006) baseStart_6520006 baseEnd_6520006 := by
    simpa [prefixWord, tailWord_6520006, baseEnd_6520006] using wordTrace_append hprefix tailTrace_6520006
  have hstable : (prefixWord ++ tailWord_6520006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520006).length < 2 ^ (prefixWord ++ tailWord_6520006).sum := by decide
  have hdescent : baseEnd_6520006 < baseStart_6520006 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520065 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 2, 3, 2]
def baseStart_6520065 : Nat := 118140960795 + 6520065 * 2 ^ 59
def prefixEnd_6520065 : Nat := 4983230072969 + 3 ^ 40 * 6520065 * 2
def baseEnd_6520065 : Nat := 3347927243557137949402273

theorem tailTrace_6520065 : CollatzResearch.WordTrace tailWord_6520065 prefixEnd_6520065 3347927243557137949402273 := by
  unfold tailWord_6520065
  simp only [CollatzResearch.WordTrace]
  refine ⟨237806307123925518293785649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 158537538082617012195857099 237806307123925518293785649)
  ·
    refine ⟨178354730342944138720339237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 237806307123925518293785649 178354730342944138720339237)
    ·
      refine ⟨33441511939302026010063607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178354730342944138720339237 33441511939302026010063607)
      ·
        refine ⟨50162267908953039015095411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33441511939302026010063607 50162267908953039015095411)
        ·
          refine ⟨75243401863429558522643117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50162267908953039015095411 75243401863429558522643117)
          ·
            refine ⟨28216275698786084445991169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75243401863429558522643117 28216275698786084445991169)
            ·
              refine ⟨21162206774089563334493377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28216275698786084445991169 21162206774089563334493377)
              ·
                refine ⟨15871655080567172500870033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21162206774089563334493377 15871655080567172500870033)
                ·
                  refine ⟨11903741310425379375652525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15871655080567172500870033 11903741310425379375652525)
                  ·
                    refine ⟨4463902991409517265869697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11903741310425379375652525 4463902991409517265869697)
                    ·
                      refine ⟨3347927243557137949402273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4463902991409517265869697 3347927243557137949402273)
                      ·
                        rfl

theorem cell23_6520065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 2, 3, 2].length) (baseStart_6520065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520065 prefixEnd_6520065 := by exact prefixLift 6520065
  have htrace : WordTrace (prefixWord ++ tailWord_6520065) baseStart_6520065 baseEnd_6520065 := by
    simpa [prefixWord, tailWord_6520065, baseEnd_6520065] using wordTrace_append hprefix tailTrace_6520065
  have hstable : (prefixWord ++ tailWord_6520065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520065).length < 2 ^ (prefixWord ++ tailWord_6520065).sum := by decide
  have hdescent : baseEnd_6520065 < baseStart_6520065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520066 : List Nat := [3, 4, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_6520066 : Nat := 118140960795 + 6520066 * 2 ^ 59
def prefixEnd_6520066 : Nat := 4983230072969 + 3 ^ 40 * 6520066 * 2
def baseEnd_6520066 : Nat := 1115975919012597481829923

theorem tailTrace_6520066 : CollatzResearch.WordTrace tailWord_6520066 prefixEnd_6520066 1115975919012597481829923 := by
  unfold tailWord_6520066
  simp only [CollatzResearch.WordTrace]
  refine ⟨59451585899230473866143013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 158537562397947930309714701 59451585899230473866143013)
  ·
    refine ⟨11147172356105713849901815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59451585899230473866143013 11147172356105713849901815)
    ·
      refine ⟨16720758534158570774852723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11147172356105713849901815 16720758534158570774852723)
      ·
        refine ⟨25081137801237856162279085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16720758534158570774852723 25081137801237856162279085)
        ·
          refine ⟨9405426675464196060854657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25081137801237856162279085 9405426675464196060854657)
          ·
            refine ⟨7054070006598147045640993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9405426675464196060854657 7054070006598147045640993)
            ·
              refine ⟨5290552504948610284230745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7054070006598147045640993 5290552504948610284230745)
              ·
                refine ⟨3967914378711457713173059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5290552504948610284230745 3967914378711457713173059)
                ·
                  refine ⟨5951871568067186569759589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3967914378711457713173059 5951871568067186569759589)
                  ·
                    refine ⟨1115975919012597481829923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5951871568067186569759589 1115975919012597481829923)
                    ·
                      rfl

theorem cell23_6520066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_6520066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520066 prefixEnd_6520066 := by exact prefixLift 6520066
  have htrace : WordTrace (prefixWord ++ tailWord_6520066) baseStart_6520066 baseEnd_6520066 := by
    simpa [prefixWord, tailWord_6520066, baseEnd_6520066] using wordTrace_append hprefix tailTrace_6520066
  have hstable : (prefixWord ++ tailWord_6520066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520066).length < 2 ^ (prefixWord ++ tailWord_6520066).sum := by decide
  have hdescent : baseEnd_6520066 < baseStart_6520066 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6520078 : List Nat := [4, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4]
def baseStart_6520078 : Nat := 118140960795 + 6520078 * 2 ^ 59
def prefixEnd_6520078 : Nat := 4983230072969 + 3 ^ 40 * 6520078 * 2
def baseEnd_6520078 : Nat := 3347933918805646398539713

theorem tailTrace_6520078 : CollatzResearch.WordTrace tailWord_6520078 prefixEnd_6520078 3347933918805646398539713 := by
  unfold tailWord_6520078
  simp only [CollatzResearch.WordTrace]
  refine ⟨29725847659109802689251111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 158537854181918947676005925 29725847659109802689251111)
  ·
    refine ⟨44588771488664704033876667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29725847659109802689251111 44588771488664704033876667)
    ·
      refine ⟨66883157232997056050815001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44588771488664704033876667 66883157232997056050815001)
      ·
        refine ⟨50162367924747792038111251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66883157232997056050815001 50162367924747792038111251)
        ·
          refine ⟨75243551887121688057166877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50162367924747792038111251 75243551887121688057166877)
          ·
            refine ⟨28216331957670633021437579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75243551887121688057166877 28216331957670633021437579)
            ·
              refine ⟨42324497936505949532156369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28216331957670633021437579 42324497936505949532156369)
              ·
                refine ⟨31743373452379462149117277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42324497936505949532156369 31743373452379462149117277)
                ·
                  refine ⟨11903765044642298305918979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31743373452379462149117277 11903765044642298305918979)
                  ·
                    refine ⟨17855647566963447458878469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11903765044642298305918979 17855647566963447458878469)
                    ·
                      refine ⟨3347933918805646398539713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17855647566963447458878469 3347933918805646398539713)
                      ·
                        rfl

theorem cell23_6520078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_6520078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6520078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6520078 prefixEnd_6520078 := by exact prefixLift 6520078
  have htrace : WordTrace (prefixWord ++ tailWord_6520078) baseStart_6520078 baseEnd_6520078 := by
    simpa [prefixWord, tailWord_6520078, baseEnd_6520078] using wordTrace_append hprefix tailTrace_6520078
  have hstable : (prefixWord ++ tailWord_6520078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6520078).length < 2 ^ (prefixWord ++ tailWord_6520078).sum := by decide
  have hdescent : baseEnd_6520078 < baseStart_6520078 := by decide
  rcases family_descends (prefixWord ++ tailWord_6520078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
