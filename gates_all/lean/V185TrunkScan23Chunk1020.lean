import V185TrunkScan23Chunk1019

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6038933 : List Nat := [1, 3, 2, 1, 1, 2, 2, 6, 1, 2, 2]
def baseStart_6038933 : Nat := 118140960795 + 6038933 * 2 ^ 59
def prefixEnd_6038933 : Nat := 4983230072969 + 3 ^ 40 * 6038933 * 2
def baseEnd_6038933 : Nat := 3100875269298126380564959

theorem tailTrace_6038933 : CollatzResearch.WordTrace tailWord_6038933 prefixEnd_6038933 3100875269298126380564959 := by
  unfold tailWord_6038933
  simp only [CollatzResearch.WordTrace]
  refine ⟨220257981430984583490137453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146838654287323055660091635 220257981430984583490137453)
  ·
    refine ⟨82596743036619218808801545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220257981430984583490137453 82596743036619218808801545)
    ·
      refine ⟨61947557277464414106601159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82596743036619218808801545 61947557277464414106601159)
      ·
        refine ⟨92921335916196621159901739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61947557277464414106601159 92921335916196621159901739)
        ·
          refine ⟨139382003874294931739852609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92921335916196621159901739 139382003874294931739852609)
          ·
            refine ⟨104536502905721198804889457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139382003874294931739852609 104536502905721198804889457)
            ·
              refine ⟨78402377179290899103667093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104536502905721198804889457 78402377179290899103667093)
              ·
                refine ⟨3675111430279260895484395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78402377179290899103667093 3675111430279260895484395)
                ·
                  refine ⟨5512667145418891343226593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675111430279260895484395 5512667145418891343226593)
                  ·
                    refine ⟨4134500359064168507419945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5512667145418891343226593 4134500359064168507419945)
                    ·
                      refine ⟨3100875269298126380564959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134500359064168507419945 3100875269298126380564959)
                      ·
                        rfl

theorem cell23_6038933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 6, 1, 2, 2].length) (baseStart_6038933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038933 prefixEnd_6038933 := by exact prefixLift 6038933
  have htrace : WordTrace (prefixWord ++ tailWord_6038933) baseStart_6038933 baseEnd_6038933 := by
    simpa [prefixWord, tailWord_6038933, baseEnd_6038933] using wordTrace_append hprefix tailTrace_6038933
  have hstable : (prefixWord ++ tailWord_6038933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038933).length < 2 ^ (prefixWord ++ tailWord_6038933).sum := by decide
  have hdescent : baseEnd_6038933 < baseStart_6038933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038943 : List Nat := [1, 1, 2, 5, 1, 4, 2, 1, 2, 4]
def baseStart_6038943 : Nat := 118140960795 + 6038943 * 2 ^ 59
def prefixEnd_6038943 : Nat := 4983230072969 + 3 ^ 40 * 6038943 * 2
def baseEnd_6038943 : Nat := 1033626801368223780479971

theorem tailTrace_6038943 : CollatzResearch.WordTrace tailWord_6038943 prefixEnd_6038943 1033626801368223780479971 := by
  unfold tailWord_6038943
  simp only [CollatzResearch.WordTrace]
  refine ⟨220258346160948355198001483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146838897440632236798667655 220258346160948355198001483)
  ·
    refine ⟨330387519241422532797002225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220258346160948355198001483 330387519241422532797002225)
    ·
      refine ⟨247790639431066899597751669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330387519241422532797002225 247790639431066899597751669)
      ·
        refine ⟨23230372446662521837289219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 247790639431066899597751669 23230372446662521837289219)
        ·
          refine ⟨34845558669993782755933829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23230372446662521837289219 34845558669993782755933829)
          ·
            refine ⟨6533542250623834266737593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34845558669993782755933829 6533542250623834266737593)
            ·
              refine ⟨4900156687967875700053195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6533542250623834266737593 4900156687967875700053195)
              ·
                refine ⟨7350235031951813550079793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4900156687967875700053195 7350235031951813550079793)
                ·
                  refine ⟨5512676273963860162559845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7350235031951813550079793 5512676273963860162559845)
                  ·
                    refine ⟨1033626801368223780479971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5512676273963860162559845 1033626801368223780479971)
                    ·
                      rfl

theorem cell23_6038943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 2, 4].length) (baseStart_6038943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038943 prefixEnd_6038943 := by exact prefixLift 6038943
  have htrace : WordTrace (prefixWord ++ tailWord_6038943) baseStart_6038943 baseEnd_6038943 := by
    simpa [prefixWord, tailWord_6038943, baseEnd_6038943] using wordTrace_append hprefix tailTrace_6038943
  have hstable : (prefixWord ++ tailWord_6038943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038943).length < 2 ^ (prefixWord ++ tailWord_6038943).sum := by decide
  have hdescent : baseEnd_6038943 < baseStart_6038943 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038949 : List Nat := [1, 3, 1, 2, 1, 1, 2, 2, 6, 1, 3]
def baseStart_6038949 : Nat := 118140960795 + 6038949 * 2 ^ 59
def prefixEnd_6038949 : Nat := 4983230072969 + 3 ^ 40 * 6038949 * 2
def baseEnd_6038949 : Nat := 3100883484988598317964885

theorem tailTrace_6038949 : CollatzResearch.WordTrace tailWord_6038949 prefixEnd_6038949 3100883484988598317964885 := by
  unfold tailWord_6038949
  simp only [CollatzResearch.WordTrace]
  refine ⟨220258564998926618222719901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146839043332617745481813267 220258564998926618222719901)
  ·
    refine ⟨82596961874597481833519963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220258564998926618222719901 82596961874597481833519963)
    ·
      refine ⟨123895442811896222750279945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82596961874597481833519963 123895442811896222750279945)
      ·
        refine ⟨92921582108922167062709959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123895442811896222750279945 92921582108922167062709959)
        ·
          refine ⟨139382373163383250594064939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92921582108922167062709959 139382373163383250594064939)
          ·
            refine ⟨209073559745074875891097409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139382373163383250594064939 209073559745074875891097409)
            ·
              refine ⟨156805169808806156918323057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209073559745074875891097409 156805169808806156918323057)
              ·
                refine ⟨117603877356604617688742293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156805169808806156918323057 117603877356604617688742293)
                ·
                  refine ⟨5512681751090841454159795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117603877356604617688742293 5512681751090841454159795)
                  ·
                    refine ⟨8269022626636262181239693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5512681751090841454159795 8269022626636262181239693)
                    ·
                      refine ⟨3100883484988598317964885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8269022626636262181239693 3100883484988598317964885)
                      ·
                        rfl

theorem cell23_6038949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_6038949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038949 prefixEnd_6038949 := by exact prefixLift 6038949
  have htrace : WordTrace (prefixWord ++ tailWord_6038949) baseStart_6038949 baseEnd_6038949 := by
    simpa [prefixWord, tailWord_6038949, baseEnd_6038949] using wordTrace_append hprefix tailTrace_6038949
  have hstable : (prefixWord ++ tailWord_6038949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038949).length < 2 ^ (prefixWord ++ tailWord_6038949).sum := by decide
  have hdescent : baseEnd_6038949 < baseStart_6038949 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038962 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5]
def baseStart_6038962 : Nat := 118140960795 + 6038962 * 2 ^ 59
def prefixEnd_6038962 : Nat := 4983230072969 + 3 ^ 40 * 6038962 * 2
def baseEnd_6038962 : Nat := 3100890160237106767102325

theorem tailTrace_6038962 : CollatzResearch.WordTrace tailWord_6038962 prefixEnd_6038962 3100890160237106767102325 := by
  unfold tailWord_6038962
  simp only [CollatzResearch.WordTrace]
  refine ⟨55064759786969880360735785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146839359431919680961962093 55064759786969880360735785)
  ·
    refine ⟨41298569840227410270551839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55064759786969880360735785 41298569840227410270551839)
    ·
      refine ⟨61947854760341115405827759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41298569840227410270551839 61947854760341115405827759)
      ·
        refine ⟨92921782140511673108741639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61947854760341115405827759 92921782140511673108741639)
        ·
          refine ⟨139382673210767509663112459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92921782140511673108741639 139382673210767509663112459)
          ·
            refine ⟨209074009816151264494668689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139382673210767509663112459 209074009816151264494668689)
            ·
              refine ⟨156805507362113448371001517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209074009816151264494668689 156805507362113448371001517)
              ·
                refine ⟨58802065260792543139125569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156805507362113448371001517 58802065260792543139125569)
                ·
                  refine ⟨44101548945594407354344177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58802065260792543139125569 44101548945594407354344177)
                  ·
                    refine ⟨33076161709195805515758133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44101548945594407354344177 33076161709195805515758133)
                    ·
                      refine ⟨3100890160237106767102325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33076161709195805515758133 3100890160237106767102325)
                      ·
                        rfl

theorem cell23_6038962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_6038962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038962 prefixEnd_6038962 := by exact prefixLift 6038962
  have htrace : WordTrace (prefixWord ++ tailWord_6038962) baseStart_6038962 baseEnd_6038962 := by
    simpa [prefixWord, tailWord_6038962, baseEnd_6038962] using wordTrace_append hprefix tailTrace_6038962
  have hstable : (prefixWord ++ tailWord_6038962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038962).length < 2 ^ (prefixWord ++ tailWord_6038962).sum := by decide
  have hdescent : baseEnd_6038962 < baseStart_6038962 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038976 : List Nat := [2, 1, 1, 2, 3, 1, 2, 5, 1, 3, 2]
def baseStart_6038976 : Nat := 118140960795 + 6038976 * 2 ^ 59
def prefixEnd_6038976 : Nat := 4983230072969 + 3 ^ 40 * 6038976 * 2
def baseEnd_6038976 : Nat := 3100897348966269712327261

theorem tailTrace_6038976 : CollatzResearch.WordTrace tailWord_6038976 prefixEnd_6038976 3100897348966269712327261 := by
  unfold tailWord_6038976
  simp only [CollatzResearch.WordTrace]
  refine ⟨110129774884914400916976391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146839699846552534555968521 110129774884914400916976391)
  ·
    refine ⟨165194662327371601375464587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110129774884914400916976391 165194662327371601375464587)
    ·
      refine ⟨247791993491057402063196881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165194662327371601375464587 247791993491057402063196881)
      ·
        refine ⟨185843995118293051547397661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247791993491057402063196881 185843995118293051547397661)
        ·
          refine ⟨69691498169359894330274123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185843995118293051547397661 69691498169359894330274123)
          ·
            refine ⟨104537247254039841495411185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69691498169359894330274123 104537247254039841495411185)
            ·
              refine ⟨78402935440529881121558389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104537247254039841495411185 78402935440529881121558389)
              ·
                refine ⟨7350275197549676355146099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78402935440529881121558389 7350275197549676355146099)
                ·
                  refine ⟨11025412796324514532719149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7350275197549676355146099 11025412796324514532719149)
                  ·
                    refine ⟨4134529798621692949769681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11025412796324514532719149 4134529798621692949769681)
                    ·
                      refine ⟨3100897348966269712327261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134529798621692949769681 3100897348966269712327261)
                      ·
                        rfl

theorem cell23_6038976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 1, 3, 2].length) (baseStart_6038976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038976 prefixEnd_6038976 := by exact prefixLift 6038976
  have htrace : WordTrace (prefixWord ++ tailWord_6038976) baseStart_6038976 baseEnd_6038976 := by
    simpa [prefixWord, tailWord_6038976, baseEnd_6038976] using wordTrace_append hprefix tailTrace_6038976
  have hstable : (prefixWord ++ tailWord_6038976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038976).length < 2 ^ (prefixWord ++ tailWord_6038976).sum := by decide
  have hdescent : baseEnd_6038976 < baseStart_6038976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6038978 : List Nat := [3, 5, 2, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_6038978 : Nat := 118140960795 + 6038978 * 2 ^ 59
def prefixEnd_6038978 : Nat := 4983230072969 + 3 ^ 40 * 6038978 * 2
def baseEnd_6038978 : Nat := 3100898375927578704502253

theorem tailTrace_6038978 : CollatzResearch.WordTrace tailWord_6038978 prefixEnd_6038978 3100898375927578704502253 := by
  unfold tailWord_6038978
  simp only [CollatzResearch.WordTrace]
  refine ⟨55064905678955389043881397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146839748477214370783683725 55064905678955389043881397)
  ·
    refine ⟨5162334907402067722863881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55064905678955389043881397 5162334907402067722863881)
    ·
      refine ⟨3871751180551550792147911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5162334907402067722863881 3871751180551550792147911)
      ·
        refine ⟨5807626770827326188221867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3871751180551550792147911 5807626770827326188221867)
        ·
          refine ⟨8711440156240989282332801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5807626770827326188221867 8711440156240989282332801)
          ·
            refine ⟨6533580117180741961749601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8711440156240989282332801 6533580117180741961749601)
            ·
              refine ⟨4900185087885556471312201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6533580117180741961749601 4900185087885556471312201)
              ·
                refine ⟨3675138815914167353484151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4900185087885556471312201 3675138815914167353484151)
                ·
                  refine ⟨5512708223871251030226227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675138815914167353484151 5512708223871251030226227)
                  ·
                    refine ⟨8269062335806876545339341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5512708223871251030226227 8269062335806876545339341)
                    ·
                      refine ⟨3100898375927578704502253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8269062335806876545339341 3100898375927578704502253)
                      ·
                        rfl

theorem cell23_6038978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_6038978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6038978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6038978 prefixEnd_6038978 := by exact prefixLift 6038978
  have htrace : WordTrace (prefixWord ++ tailWord_6038978) baseStart_6038978 baseEnd_6038978 := by
    simpa [prefixWord, tailWord_6038978, baseEnd_6038978] using wordTrace_append hprefix tailTrace_6038978
  have hstable : (prefixWord ++ tailWord_6038978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6038978).length < 2 ^ (prefixWord ++ tailWord_6038978).sum := by decide
  have hdescent : baseEnd_6038978 < baseStart_6038978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6038978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039080 : List Nat := [2, 1, 5, 2, 2, 2, 1, 3, 5]
def baseStart_6039080 : Nat := 118140960795 + 6039080 * 2 ^ 59
def prefixEnd_6039080 : Nat := 4983230072969 + 3 ^ 40 * 6039080 * 2
def baseEnd_6039080 : Nat := 344550083439370811714087

theorem tailTrace_6039080 : CollatzResearch.WordTrace tailWord_6039080 prefixEnd_6039080 344550083439370811714087 := by
  unfold tailWord_6039080
  simp only [CollatzResearch.WordTrace]
  refine ⟨110131671480726013797869347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146842228640968018397159129 110131671480726013797869347)
  ·
    refine ⟨165197507221089020696804021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110131671480726013797869347 165197507221089020696804021)
    ·
      refine ⟨15487266301977095690325377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165197507221089020696804021 15487266301977095690325377)
      ·
        refine ⟨11615449726482821767744033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15487266301977095690325377 11615449726482821767744033)
        ·
          refine ⟨8711587294862116325808025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11615449726482821767744033 8711587294862116325808025)
          ·
            refine ⟨6533690471146587244356019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8711587294862116325808025 6533690471146587244356019)
            ·
              refine ⟨9800535706719880866534029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6533690471146587244356019 9800535706719880866534029)
              ·
                refine ⟨3675200890019955324950261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9800535706719880866534029 3675200890019955324950261)
                ·
                  refine ⟨344550083439370811714087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3675200890019955324950261 344550083439370811714087)
                  ·
                    rfl

theorem cell23_6039080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 5].length) (baseStart_6039080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039080 prefixEnd_6039080 := by exact prefixLift 6039080
  have htrace : WordTrace (prefixWord ++ tailWord_6039080) baseStart_6039080 baseEnd_6039080 := by
    simpa [prefixWord, tailWord_6039080, baseEnd_6039080] using wordTrace_append hprefix tailTrace_6039080
  have hstable : (prefixWord ++ tailWord_6039080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039080).length < 2 ^ (prefixWord ++ tailWord_6039080).sum := by decide
  have hdescent : baseEnd_6039080 < baseStart_6039080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039096 : List Nat := [2, 1, 2, 1, 4, 3, 1, 2, 2, 1, 4]
def baseStart_6039096 : Nat := 118140960795 + 6039096 * 2 ^ 59
def prefixEnd_6039096 : Nat := 4983230072969 + 3 ^ 40 * 6039096 * 2
def baseEnd_6039096 : Nat := 3100958966644809242826709

theorem tailTrace_6039096 : CollatzResearch.WordTrace tailWord_6039096 prefixEnd_6039096 3100958966644809242826709 := by
  unfold tailWord_6039096
  simp only [CollatzResearch.WordTrace]
  refine ⟨110131963264697031164160571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146842617686262708218880761 110131963264697031164160571)
  ·
    refine ⟨165197944897045546746240857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110131963264697031164160571 165197944897045546746240857)
    ·
      refine ⟨123898458672784160059680643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165197944897045546746240857 123898458672784160059680643)
      ·
        refine ⟨185847688009176240089520965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123898458672784160059680643 185847688009176240089520965)
        ·
          refine ⟨34846441501720545016785181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185847688009176240089520965 34846441501720545016785181)
          ·
            refine ⟨13067415563145204381294443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34846441501720545016785181 13067415563145204381294443)
            ·
              refine ⟨19601123344717806571941665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13067415563145204381294443 19601123344717806571941665)
              ·
                refine ⟨14700842508538354928956249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19601123344717806571941665 14700842508538354928956249)
                ·
                  refine ⟨11025631881403766196717187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14700842508538354928956249 11025631881403766196717187)
                  ·
                    refine ⟨16538447822105649295075781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11025631881403766196717187 16538447822105649295075781)
                    ·
                      refine ⟨3100958966644809242826709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16538447822105649295075781 3100958966644809242826709)
                      ·
                        rfl

theorem cell23_6039096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 2, 2, 1, 4].length) (baseStart_6039096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039096 prefixEnd_6039096 := by exact prefixLift 6039096
  have htrace : WordTrace (prefixWord ++ tailWord_6039096) baseStart_6039096 baseEnd_6039096 := by
    simpa [prefixWord, tailWord_6039096, baseEnd_6039096] using wordTrace_append hprefix tailTrace_6039096
  have hstable : (prefixWord ++ tailWord_6039096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039096).length < 2 ^ (prefixWord ++ tailWord_6039096).sum := by decide
  have hdescent : baseEnd_6039096 < baseStart_6039096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039129 : List Nat := [1, 2, 1, 2, 2, 1, 1, 3, 2, 5, 3]
def baseStart_6039129 : Nat := 118140960795 + 6039129 * 2 ^ 59
def prefixEnd_6039129 : Nat := 4983230072969 + 3 ^ 40 * 6039129 * 2
def baseEnd_6039129 : Nat := 3100975911506407613714057

theorem tailTrace_6039129 : CollatzResearch.WordTrace tailWord_6039129 prefixEnd_6039129 3100975911506407613714057 := by
  unfold tailWord_6039129
  simp only [CollatzResearch.WordTrace]
  refine ⟨220265130138274508964272441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146843420092183005976181627 220265130138274508964272441)
  ·
    refine ⟨165198847603705881723204331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220265130138274508964272441 165198847603705881723204331)
    ·
      refine ⟨247798271405558822584806497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165198847603705881723204331 247798271405558822584806497)
      ·
        refine ⟨185848703554169116938604873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247798271405558822584806497 185848703554169116938604873)
        ·
          refine ⟨139386527665626837703953655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185848703554169116938604873 139386527665626837703953655)
          ·
            refine ⟨209079791498440256555930483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139386527665626837703953655 209079791498440256555930483)
            ·
              refine ⟨313619687247660384833895725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209079791498440256555930483 313619687247660384833895725)
              ·
                refine ⟨117607382717872644312710897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313619687247660384833895725 117607382717872644312710897)
                ·
                  refine ⟨88205537038404483234533173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117607382717872644312710897 88205537038404483234533173)
                  ·
                    refine ⟨8269269097350420303237485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88205537038404483234533173 8269269097350420303237485)
                    ·
                      refine ⟨3100975911506407613714057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8269269097350420303237485 3100975911506407613714057)
                      ·
                        rfl

theorem cell23_6039129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_6039129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039129 prefixEnd_6039129 := by exact prefixLift 6039129
  have htrace : WordTrace (prefixWord ++ tailWord_6039129) baseStart_6039129 baseEnd_6039129 := by
    simpa [prefixWord, tailWord_6039129, baseEnd_6039129] using wordTrace_append hprefix tailTrace_6039129
  have hstable : (prefixWord ++ tailWord_6039129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039129).length < 2 ^ (prefixWord ++ tailWord_6039129).sum := by decide
  have hdescent : baseEnd_6039129 < baseStart_6039129 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039157 : List Nat := [1, 3, 4, 2, 1, 1, 4, 2, 1, 4]
def baseStart_6039157 : Nat := 118140960795 + 6039157 * 2 ^ 59
def prefixEnd_6039157 : Nat := 4983230072969 + 3 ^ 40 * 6039157 * 2
def baseEnd_6039157 : Nat := 1033663429654911168054643

theorem tailTrace_6039157 : CollatzResearch.WordTrace tailWord_6039157 prefixEnd_6039157 1033663429654911168054643 := by
  unfold tailWord_6039157
  simp only [CollatzResearch.WordTrace]
  refine ⟨220266151382173069746291725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146844100921448713164194483 220266151382173069746291725)
  ·
    refine ⟨82599806768314901154859397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220266151382173069746291725 82599806768314901154859397)
    ·
      refine ⟨15487463769059043966536137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82599806768314901154859397 15487463769059043966536137)
      ·
        refine ⟨11615597826794282974902103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15487463769059043966536137 11615597826794282974902103)
        ·
          refine ⟨17423396740191424462353155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11615597826794282974902103 17423396740191424462353155)
          ·
            refine ⟨26135095110287136693529733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17423396740191424462353155 26135095110287136693529733)
            ·
              refine ⟨4900330333178838130036825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26135095110287136693529733 4900330333178838130036825)
              ·
                refine ⟨3675247749884128597527619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4900330333178838130036825 3675247749884128597527619)
                ·
                  refine ⟨5512871624826192896291429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675247749884128597527619 5512871624826192896291429)
                  ·
                    refine ⟨1033663429654911168054643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5512871624826192896291429 1033663429654911168054643)
                    ·
                      rfl

theorem cell23_6039157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_6039157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039157 prefixEnd_6039157 := by exact prefixLift 6039157
  have htrace : WordTrace (prefixWord ++ tailWord_6039157) baseStart_6039157 baseEnd_6039157 := by
    simpa [prefixWord, tailWord_6039157, baseEnd_6039157] using wordTrace_append hprefix tailTrace_6039157
  have hstable : (prefixWord ++ tailWord_6039157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039157).length < 2 ^ (prefixWord ++ tailWord_6039157).sum := by decide
  have hdescent : baseEnd_6039157 < baseStart_6039157 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039200 : List Nat := [2, 1, 1, 4, 3, 3, 2, 1, 1, 5]
def baseStart_6039200 : Nat := 118140960795 + 6039200 * 2 ^ 59
def prefixEnd_6039200 : Nat := 4983230072969 + 3 ^ 40 * 6039200 * 2
def baseEnd_6039200 : Nat := 1033670789544292278642077

theorem tailTrace_6039200 : CollatzResearch.WordTrace tailWord_6039200 prefixEnd_6039200 1033670789544292278642077 := by
  unfold tailWord_6039200
  simp only [CollatzResearch.WordTrace]
  refine ⟨110133859860508644045053527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146845146480678192060071369 110133859860508644045053527)
  ·
    refine ⟨165200789790762966067580291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110133859860508644045053527 165200789790762966067580291)
    ·
      refine ⟨247801184686144449101370437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165200789790762966067580291 247801184686144449101370437)
      ·
        refine ⟨46462722128652084206506957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247801184686144449101370437 46462722128652084206506957)
        ·
          refine ⟨17423520798244531577440109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46462722128652084206506957 17423520798244531577440109)
          ·
            refine ⟨6533820299341699341540041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17423520798244531577440109 6533820299341699341540041)
            ·
              refine ⟨4900365224506274506155031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6533820299341699341540041 4900365224506274506155031)
              ·
                refine ⟨7350547836759411759232547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4900365224506274506155031 7350547836759411759232547)
                ·
                  refine ⟨11025821755139117638848821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7350547836759411759232547 11025821755139117638848821)
                  ·
                    refine ⟨1033670789544292278642077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11025821755139117638848821 1033670789544292278642077)
                    ·
                      rfl

theorem cell23_6039200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 2, 1, 1, 5].length) (baseStart_6039200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039200 prefixEnd_6039200 := by exact prefixLift 6039200
  have htrace : WordTrace (prefixWord ++ tailWord_6039200) baseStart_6039200 baseEnd_6039200 := by
    simpa [prefixWord, tailWord_6039200, baseEnd_6039200] using wordTrace_append hprefix tailTrace_6039200
  have hstable : (prefixWord ++ tailWord_6039200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039200).length < 2 ^ (prefixWord ++ tailWord_6039200).sum := by decide
  have hdescent : baseEnd_6039200 < baseStart_6039200 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039203 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 5, 2, 2]
def baseStart_6039203 : Nat := 118140960795 + 6039203 * 2 ^ 59
def prefixEnd_6039203 : Nat := 4983230072969 + 3 ^ 40 * 6039203 * 2
def baseEnd_6039203 : Nat := 3101013909074840324188717

theorem tailTrace_6039203 : CollatzResearch.WordTrace tailWord_6039203 prefixEnd_6039203 3101013909074840324188717 := by
  unfold tailWord_6039203
  simp only [CollatzResearch.WordTrace]
  refine ⟨220267829140006419602466263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146845219426670946401644175 220267829140006419602466263)
  ·
    refine ⟨330401743710009629403699395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220267829140006419602466263 330401743710009629403699395)
    ·
      refine ⟨495602615565014444105549093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330401743710009629403699395 495602615565014444105549093)
      ·
        refine ⟨92925490418440208269790455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 495602615565014444105549093 92925490418440208269790455)
        ·
          refine ⟨139388235627660312404685683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92925490418440208269790455 139388235627660312404685683)
          ·
            refine ⟨209082353441490468607028525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139388235627660312404685683 209082353441490468607028525)
            ·
              refine ⟨78405882540558925727635697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209082353441490468607028525 78405882540558925727635697)
              ·
                refine ⟨58804411905419194295726773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78405882540558925727635697 58804411905419194295726773)
                ·
                  refine ⟨5512913616133049465224385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58804411905419194295726773 5512913616133049465224385)
                  ·
                    refine ⟨4134685212099787098918289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5512913616133049465224385 4134685212099787098918289)
                    ·
                      refine ⟨3101013909074840324188717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134685212099787098918289 3101013909074840324188717)
                      ·
                        rfl

theorem cell23_6039203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_6039203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039203 prefixEnd_6039203 := by exact prefixLift 6039203
  have htrace : WordTrace (prefixWord ++ tailWord_6039203) baseStart_6039203 baseEnd_6039203 := by
    simpa [prefixWord, tailWord_6039203, baseEnd_6039203] using wordTrace_append hprefix tailTrace_6039203
  have hstable : (prefixWord ++ tailWord_6039203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039203).length < 2 ^ (prefixWord ++ tailWord_6039203).sum := by decide
  have hdescent : baseEnd_6039203 < baseStart_6039203 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039213 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 4, 4]
def baseStart_6039213 : Nat := 118140960795 + 6039213 * 2 ^ 59
def prefixEnd_6039213 : Nat := 4983230072969 + 3 ^ 40 * 6039213 * 2
def baseEnd_6039213 : Nat := 1033673014627128428354557

theorem tailTrace_6039213 : CollatzResearch.WordTrace tailWord_6039213 prefixEnd_6039213 1033673014627128428354557 := by
  unfold tailWord_6039213
  simp only [CollatzResearch.WordTrace]
  refine ⟨220268193869970191310330293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146845462579980127540220195 220268193869970191310330293)
  ·
    refine ⟨20650143175309705435343465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220268193869970191310330293 20650143175309705435343465)
    ·
      refine ⟨15487607381482279076507599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20650143175309705435343465 15487607381482279076507599)
      ·
        refine ⟨23231411072223418614761399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15487607381482279076507599 23231411072223418614761399)
        ·
          refine ⟨34847116608335127922142099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23231411072223418614761399 34847116608335127922142099)
          ·
            refine ⟨52270674912502691883213149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34847116608335127922142099 52270674912502691883213149)
            ·
              refine ⟨19601503092188509456204931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52270674912502691883213149 19601503092188509456204931)
              ·
                refine ⟨29402254638282764184307397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19601503092188509456204931 29402254638282764184307397)
                ·
                  refine ⟨5512922744678018284557637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29402254638282764184307397 5512922744678018284557637)
                  ·
                    refine ⟨1033673014627128428354557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5512922744678018284557637 1033673014627128428354557)
                    ·
                      rfl

theorem cell23_6039213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_6039213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039213 prefixEnd_6039213 := by exact prefixLift 6039213
  have htrace : WordTrace (prefixWord ++ tailWord_6039213) baseStart_6039213 baseEnd_6039213 := by
    simpa [prefixWord, tailWord_6039213, baseEnd_6039213] using wordTrace_append hprefix tailTrace_6039213
  have hstable : (prefixWord ++ tailWord_6039213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039213).length < 2 ^ (prefixWord ++ tailWord_6039213).sum := by decide
  have hdescent : baseEnd_6039213 < baseStart_6039213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039234 : List Nat := [3, 5, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_6039234 : Nat := 118140960795 + 6039234 * 2 ^ 59
def prefixEnd_6039234 : Nat := 4983230072969 + 3 ^ 40 * 6039234 * 2
def baseEnd_6039234 : Nat := 1033676608991709900967025

theorem tailTrace_6039234 : CollatzResearch.WordTrace tailWord_6039234 prefixEnd_6039234 1033676608991709900967025 := by
  unfold tailWord_6039234
  simp only [CollatzResearch.WordTrace]
  refine ⟨55067239950723527974211189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146845973201929407931229837 55067239950723527974211189)
  ·
    refine ⟨5162553745380330747582299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55067239950723527974211189 5162553745380330747582299)
    ·
      refine ⟨7743830618070496121373449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5162553745380330747582299 7743830618070496121373449)
      ·
        refine ⟨5807872963552872091030087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7743830618070496121373449 5807872963552872091030087)
        ·
          refine ⟨8711809445329308136545131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5807872963552872091030087 8711809445329308136545131)
          ·
            refine ⟨13067714167993962204817697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8711809445329308136545131 13067714167993962204817697)
            ·
              refine ⟨9800785625995471653613273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13067714167993962204817697 9800785625995471653613273)
              ·
                refine ⟨7350589219496603740209955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9800785625995471653613273 7350589219496603740209955)
                ·
                  refine ⟨11025883829244905610314933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7350589219496603740209955 11025883829244905610314933)
                  ·
                    refine ⟨1033676608991709900967025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11025883829244905610314933 1033676608991709900967025)
                    ·
                      rfl

theorem cell23_6039234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_6039234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039234 prefixEnd_6039234 := by exact prefixLift 6039234
  have htrace : WordTrace (prefixWord ++ tailWord_6039234) baseStart_6039234 baseEnd_6039234 := by
    simpa [prefixWord, tailWord_6039234, baseEnd_6039234] using wordTrace_append hprefix tailTrace_6039234
  have hstable : (prefixWord ++ tailWord_6039234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039234).length < 2 ^ (prefixWord ++ tailWord_6039234).sum := by decide
  have hdescent : baseEnd_6039234 < baseStart_6039234 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039260 : List Nat := [2, 2, 5, 1, 3, 1, 9]
def baseStart_6039260 : Nat := 118140960795 + 6039260 * 2 ^ 59
def prefixEnd_6039260 : Nat := 4983230072969 + 3 ^ 40 * 6039260 * 2
def baseEnd_6039260 : Nat := 38284483672495637051555

theorem tailTrace_6039260 : CollatzResearch.WordTrace tailWord_6039260 prefixEnd_6039260 38284483672495637051555 := by
  unfold tailWord_6039260
  simp only [CollatzResearch.WordTrace]
  refine ⟨110134954050399959168645617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146846605400533278891527489 110134954050399959168645617)
  ·
    refine ⟨82601215537799969376484213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110134954050399959168645617 82601215537799969376484213)
    ·
      refine ⟨7743863956668747129045395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82601215537799969376484213 7743863956668747129045395)
      ·
        refine ⟨11615795935003120693568093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7743863956668747129045395 11615795935003120693568093)
        ·
          refine ⟨4355923475626170260088035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11615795935003120693568093 4355923475626170260088035)
          ·
            refine ⟨6533885213439255390132053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4355923475626170260088035 6533885213439255390132053)
            ·
              refine ⟨38284483672495637051555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6533885213439255390132053 38284483672495637051555)
              ·
                rfl

theorem cell23_6039260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 9].length) (baseStart_6039260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039260 prefixEnd_6039260 := by exact prefixLift 6039260
  have htrace : WordTrace (prefixWord ++ tailWord_6039260) baseStart_6039260 baseEnd_6039260 := by
    simpa [prefixWord, tailWord_6039260, baseEnd_6039260] using wordTrace_append hprefix tailTrace_6039260
  have hstable : (prefixWord ++ tailWord_6039260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039260).length < 2 ^ (prefixWord ++ tailWord_6039260).sum := by decide
  have hdescent : baseEnd_6039260 < baseStart_6039260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039271 : List Nat := [1, 1, 5, 4, 2, 1, 1, 1, 3, 2, 2]
def baseStart_6039271 : Nat := 118140960795 + 6039271 * 2 ^ 59
def prefixEnd_6039271 : Nat := 4983230072969 + 3 ^ 40 * 6039271 * 2
def baseEnd_6039271 : Nat := 3101048825759346058138405

theorem tailTrace_6039271 : CollatzResearch.WordTrace tailWord_6039271 prefixEnd_6039271 3101048825759346058138405 := by
  unfold tailWord_6039271
  simp only [CollatzResearch.WordTrace]
  refine ⟨220270309303760067215941667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146846872869173378143961111 220270309303760067215941667)
  ·
    refine ⟨330405463955640100823912501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220270309303760067215941667 330405463955640100823912501)
    ·
      refine ⟨30975512245841259452241797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 330405463955640100823912501 30975512245841259452241797)
      ·
        refine ⟨5807908546095236147295337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30975512245841259452241797 5807908546095236147295337)
        ·
          refine ⟨4355931409571427110471503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5807908546095236147295337 4355931409571427110471503)
          ·
            refine ⟨6533897114357140665707255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4355931409571427110471503 6533897114357140665707255)
            ·
              refine ⟨9800845671535710998560883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6533897114357140665707255 9800845671535710998560883)
              ·
                refine ⟨14701268507303566497841325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9800845671535710998560883 14701268507303566497841325)
                ·
                  refine ⟨5512975690238837436690497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14701268507303566497841325 5512975690238837436690497)
                  ·
                    refine ⟨4134731767679128077517873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5512975690238837436690497 4134731767679128077517873)
                    ·
                      refine ⟨3101048825759346058138405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134731767679128077517873 3101048825759346058138405)
                      ·
                        rfl

theorem cell23_6039271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_6039271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039271 prefixEnd_6039271 := by exact prefixLift 6039271
  have htrace : WordTrace (prefixWord ++ tailWord_6039271) baseStart_6039271 baseEnd_6039271 := by
    simpa [prefixWord, tailWord_6039271, baseEnd_6039271] using wordTrace_append hprefix tailTrace_6039271
  have hstable : (prefixWord ++ tailWord_6039271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039271).length < 2 ^ (prefixWord ++ tailWord_6039271).sum := by decide
  have hdescent : baseEnd_6039271 < baseStart_6039271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039296 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 3]
def baseStart_6039296 : Nat := 118140960795 + 6039296 * 2 ^ 59
def prefixEnd_6039296 : Nat := 4983230072969 + 3 ^ 40 * 6039296 * 2
def baseEnd_6039296 : Nat := 3101061662775708460325789

theorem tailTrace_6039296 : CollatzResearch.WordTrace tailWord_6039296 prefixEnd_6039296 3101061662775708460325789 := by
  unfold tailWord_6039296
  simp only [CollatzResearch.WordTrace]
  refine ⟨110135610564334748242800871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146847480752446330990401161 110135610564334748242800871)
  ·
    refine ⟨165203415846502122364201307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110135610564334748242800871 165203415846502122364201307)
    ·
      refine ⟨247805123769753183546301961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165203415846502122364201307 247805123769753183546301961)
      ·
        refine ⟨185853842827314887659726471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247805123769753183546301961 185853842827314887659726471)
        ·
          refine ⟨278780764240972331489589707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185853842827314887659726471 278780764240972331489589707)
          ·
            refine ⟨418171146361458497234384561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278780764240972331489589707 418171146361458497234384561)
            ·
              refine ⟨313628359771093872925788421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418171146361458497234384561 313628359771093872925788421)
              ·
                refine ⟨58805317457080101173585329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313628359771093872925788421 58805317457080101173585329)
                ·
                  refine ⟨44103988092810075880188997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58805317457080101173585329 44103988092810075880188997)
                  ·
                    refine ⟨8269497767401889227535437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44103988092810075880188997 8269497767401889227535437)
                    ·
                      refine ⟨3101061662775708460325789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8269497767401889227535437 3101061662775708460325789)
                      ·
                        rfl

theorem cell23_6039296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 2, 4, 3].length) (baseStart_6039296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039296 prefixEnd_6039296 := by exact prefixLift 6039296
  have htrace : WordTrace (prefixWord ++ tailWord_6039296) baseStart_6039296 baseEnd_6039296 := by
    simpa [prefixWord, tailWord_6039296, baseEnd_6039296] using wordTrace_append hprefix tailTrace_6039296
  have hstable : (prefixWord ++ tailWord_6039296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039296).length < 2 ^ (prefixWord ++ tailWord_6039296).sum := by decide
  have hdescent : baseEnd_6039296 < baseStart_6039296 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039310 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2]
def baseStart_6039310 : Nat := 118140960795 + 6039310 * 2 ^ 59
def prefixEnd_6039310 : Nat := 4983230072969 + 3 ^ 40 * 6039310 * 2
def baseEnd_6039310 : Nat := 3101068851504871405550725

theorem tailTrace_6039310 : CollatzResearch.WordTrace tailWord_6039310 prefixEnd_6039310 3101068851504871405550725 := by
  unfold tailWord_6039310
  simp only [CollatzResearch.WordTrace]
  refine ⟨27533966468827347109576423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146847821167079184584407589 27533966468827347109576423)
  ·
    refine ⟨41300949703241020664364635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27533966468827347109576423 41300949703241020664364635)
    ·
      refine ⟨61951424554861530996546953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41300949703241020664364635 61951424554861530996546953)
      ·
        refine ⟨46463568416146148247410215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61951424554861530996546953 46463568416146148247410215)
        ·
          refine ⟨69695352624219222371115323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46463568416146148247410215 69695352624219222371115323)
          ·
            refine ⟨104543028936328833556672985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69695352624219222371115323 104543028936328833556672985)
            ·
              refine ⟨78407271702246625167504739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104543028936328833556672985 78407271702246625167504739)
              ·
                refine ⟨117610907553369937751257109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78407271702246625167504739 117610907553369937751257109)
                ·
                  refine ⟨5513011291564215832090177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117610907553369937751257109 5513011291564215832090177)
                  ·
                    refine ⟨4134758468673161874067633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5513011291564215832090177 4134758468673161874067633)
                    ·
                      refine ⟨3101068851504871405550725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134758468673161874067633 3101068851504871405550725)
                      ·
                        rfl

theorem cell23_6039310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 6, 2, 2].length) (baseStart_6039310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039310 prefixEnd_6039310 := by exact prefixLift 6039310
  have htrace : WordTrace (prefixWord ++ tailWord_6039310) baseStart_6039310 baseEnd_6039310 := by
    simpa [prefixWord, tailWord_6039310, baseEnd_6039310] using wordTrace_append hprefix tailTrace_6039310
  have hstable : (prefixWord ++ tailWord_6039310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039310).length < 2 ^ (prefixWord ++ tailWord_6039310).sum := by decide
  have hdescent : baseEnd_6039310 < baseStart_6039310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039327 : List Nat := [1, 1, 2, 4, 2, 1, 4, 2, 2, 2, 2]
def baseStart_6039327 : Nat := 118140960795 + 6039327 * 2 ^ 59
def prefixEnd_6039327 : Nat := 4983230072969 + 3 ^ 40 * 6039327 * 2
def baseEnd_6039327 : Nat := 3101077580675997839038147

theorem tailTrace_6039327 : CollatzResearch.WordTrace tailWord_6039327 prefixEnd_6039327 3101077580675997839038147 := by
  unfold tailWord_6039327
  simp only [CollatzResearch.WordTrace]
  refine ⟨220272351791557188779980235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146848234527704792519986823 220272351791557188779980235)
  ·
    refine ⟨330408527687335783169970353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220272351791557188779980235 330408527687335783169970353)
    ·
      refine ⟨247806395765501837377477765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330408527687335783169970353 247806395765501837377477765)
      ·
        refine ⟨46463699206031594508277081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247806395765501837377477765 46463699206031594508277081)
        ·
          refine ⟨34847774404523695881207811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46463699206031594508277081 34847774404523695881207811)
          ·
            refine ⟨52271661606785543821811717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34847774404523695881207811 52271661606785543821811717)
            ·
              refine ⟨9800936551272289466589697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52271661606785543821811717 9800936551272289466589697)
              ·
                refine ⟨7350702413454217099942273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9800936551272289466589697 7350702413454217099942273)
                ·
                  refine ⟨5513026810090662824956705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7350702413454217099942273 5513026810090662824956705)
                  ·
                    refine ⟨4134770107567997118717529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5513026810090662824956705 4134770107567997118717529)
                    ·
                      refine ⟨3101077580675997839038147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134770107567997118717529 3101077580675997839038147)
                      ·
                        rfl

theorem cell23_6039327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_6039327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039327 prefixEnd_6039327 := by exact prefixLift 6039327
  have htrace : WordTrace (prefixWord ++ tailWord_6039327) baseStart_6039327 baseEnd_6039327 := by
    simpa [prefixWord, tailWord_6039327, baseEnd_6039327] using wordTrace_append hprefix tailTrace_6039327
  have hstable : (prefixWord ++ tailWord_6039327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039327).length < 2 ^ (prefixWord ++ tailWord_6039327).sum := by decide
  have hdescent : baseEnd_6039327 < baseStart_6039327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039350 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 7]
def baseStart_6039350 : Nat := 118140960795 + 6039350 * 2 ^ 59
def prefixEnd_6039350 : Nat := 4983230072969 + 3 ^ 40 * 6039350 * 2
def baseEnd_6039350 : Nat := 344565487859005694338949

theorem tailTrace_6039350 : CollatzResearch.WordTrace tailWord_6039350 prefixEnd_6039350 344565487859005694338949 := by
  unfold tailWord_6039350
  simp only [CollatzResearch.WordTrace]
  refine ⟨13767074416904616481754219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146848793780315909138711669 13767074416904616481754219)
  ·
    refine ⟨20650611625356924722631329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13767074416904616481754219 20650611625356924722631329)
    ·
      refine ⟨15487958719017693541973497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20650611625356924722631329 15487958719017693541973497)
      ·
        refine ⟨11615969039263270156480123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15487958719017693541973497 11615969039263270156480123)
        ·
          refine ⟨17423953558894905234720185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11615969039263270156480123 17423953558894905234720185)
          ·
            refine ⟨13067965169171178926040139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17423953558894905234720185 13067965169171178926040139)
            ·
              refine ⟨19601947753756768389060209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13067965169171178926040139 19601947753756768389060209)
              ·
                refine ⟨14701460815317576291795157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19601947753756768389060209 14701460815317576291795157)
                ·
                  refine ⟨344565487859005694338949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14701460815317576291795157 344565487859005694338949)
                  ·
                    rfl

theorem cell23_6039350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 7].length) (baseStart_6039350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039350 prefixEnd_6039350 := by exact prefixLift 6039350
  have htrace : WordTrace (prefixWord ++ tailWord_6039350) baseStart_6039350 baseEnd_6039350 := by
    simpa [prefixWord, tailWord_6039350, baseEnd_6039350] using wordTrace_append hprefix tailTrace_6039350
  have hstable : (prefixWord ++ tailWord_6039350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039350).length < 2 ^ (prefixWord ++ tailWord_6039350).sum := by decide
  have hdescent : baseEnd_6039350 < baseStart_6039350 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039356 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 1, 1, 7]
def baseStart_6039356 : Nat := 118140960795 + 6039356 * 2 ^ 59
def prefixEnd_6039356 : Nat := 4983230072969 + 3 ^ 40 * 6039356 * 2
def baseEnd_6039356 : Nat := 3101092471614978225575513

theorem tailTrace_6039356 : CollatzResearch.WordTrace tailWord_6039356 prefixEnd_6039356 3101092471614978225575513 := by
  unfold tailWord_6039356
  simp only [CollatzResearch.WordTrace]
  refine ⟨110136704754226063366392961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146848939672301417821857281 110136704754226063366392961)
  ·
    refine ⟨82602528565669547524794721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110136704754226063366392961 82602528565669547524794721)
    ·
      refine ⟨61951896424252160643596041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82602528565669547524794721 61951896424252160643596041)
      ·
        refine ⟨46463922318189120482697031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61951896424252160643596041 46463922318189120482697031)
        ·
          refine ⟨69695883477283680724045547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46463922318189120482697031 69695883477283680724045547)
          ·
            refine ⟨104543825215925521086068321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69695883477283680724045547 104543825215925521086068321)
            ·
              refine ⟨78407868911944140814551241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104543825215925521086068321 78407868911944140814551241)
              ·
                refine ⟨58805901683958105610913431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78407868911944140814551241 58805901683958105610913431)
                ·
                  refine ⟨88208852525937158416370147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58805901683958105610913431 88208852525937158416370147)
                  ·
                    refine ⟨132313278788905737624555221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88208852525937158416370147 132313278788905737624555221)
                    ·
                      refine ⟨3101092471614978225575513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132313278788905737624555221 3101092471614978225575513)
                      ·
                        rfl

theorem cell23_6039356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_6039356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039356 prefixEnd_6039356 := by exact prefixLift 6039356
  have htrace : WordTrace (prefixWord ++ tailWord_6039356) baseStart_6039356 baseEnd_6039356 := by
    simpa [prefixWord, tailWord_6039356, baseEnd_6039356] using wordTrace_append hprefix tailTrace_6039356
  have hstable : (prefixWord ++ tailWord_6039356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039356).length < 2 ^ (prefixWord ++ tailWord_6039356).sum := by decide
  have hdescent : baseEnd_6039356 < baseStart_6039356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039363 : List Nat := [1, 1, 1, 3, 1, 5, 3, 1, 2, 5]
def baseStart_6039363 : Nat := 118140960795 + 6039363 * 2 ^ 59
def prefixEnd_6039363 : Nat := 4983230072969 + 3 ^ 40 * 6039363 * 2
def baseEnd_6039363 : Nat := 1033698688659853232729327

theorem tailTrace_6039363 : CollatzResearch.WordTrace tailWord_6039363 prefixEnd_6039363 1033698688659853232729327 := by
  unfold tailWord_6039363
  simp only [CollatzResearch.WordTrace]
  refine ⟨220273664819426766928290743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146849109879617844618860495 220273664819426766928290743)
  ·
    refine ⟨330410497229140150392436115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220273664819426766928290743 330410497229140150392436115)
    ·
      refine ⟨495615745843710225588654173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330410497229140150392436115 495615745843710225588654173)
      ·
        refine ⟨185855904691391334595745315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 495615745843710225588654173 185855904691391334595745315)
        ·
          refine ⟨278783857037087001893617973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185855904691391334595745315 278783857037087001893617973)
          ·
            refine ⟨26135986597226906427526685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 278783857037087001893617973 26135986597226906427526685)
            ·
              refine ⟨9800994973960089910322507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26135986597226906427526685 9800994973960089910322507)
              ·
                refine ⟨14701492460940134865483761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9800994973960089910322507 14701492460940134865483761)
                ·
                  refine ⟨11026119345705101149112821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14701492460940134865483761 11026119345705101149112821)
                  ·
                    refine ⟨1033698688659853232729327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11026119345705101149112821 1033698688659853232729327)
                    ·
                      rfl

theorem cell23_6039363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 5].length) (baseStart_6039363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039363 prefixEnd_6039363 := by exact prefixLift 6039363
  have htrace : WordTrace (prefixWord ++ tailWord_6039363) baseStart_6039363 baseEnd_6039363 := by
    simpa [prefixWord, tailWord_6039363, baseEnd_6039363] using wordTrace_append hprefix tailTrace_6039363
  have hstable : (prefixWord ++ tailWord_6039363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039363).length < 2 ^ (prefixWord ++ tailWord_6039363).sum := by decide
  have hdescent : baseEnd_6039363 < baseStart_6039363 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039400 : List Nat := [2, 1, 4, 2, 1, 1, 1, 3, 2, 4, 2]
def baseStart_6039400 : Nat := 118140960795 + 6039400 * 2 ^ 59
def prefixEnd_6039400 : Nat := 4983230072969 + 3 ^ 40 * 6039400 * 2
def baseEnd_6039400 : Nat := 3101115064763776053425311

theorem tailTrace_6039400 : CollatzResearch.WordTrace tailWord_6039400 prefixEnd_6039400 3101115064763776053425311 := by
  unfold tailWord_6039400
  simp only [CollatzResearch.WordTrace]
  refine ⟨110137507160146361123693827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146850009546861814831591769 110137507160146361123693827)
  ·
    refine ⟨165206260740219541685540741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110137507160146361123693827 165206260740219541685540741)
    ·
      refine ⟨30976173888791164066038889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165206260740219541685540741 30976173888791164066038889)
      ·
        refine ⟨23232130416593373049529167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30976173888791164066038889 23232130416593373049529167)
        ·
          refine ⟨34848195624890059574293751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23232130416593373049529167 34848195624890059574293751)
          ·
            refine ⟨52272293437335089361440627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34848195624890059574293751 52272293437335089361440627)
            ·
              refine ⟨78408440156002634042160941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52272293437335089361440627 78408440156002634042160941)
              ·
                refine ⟨29403165058500987765810353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78408440156002634042160941 29403165058500987765810353)
                ·
                  refine ⟨22052373793875740824357765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29403165058500987765810353 22052373793875740824357765)
                  ·
                    refine ⟨4134820086351701404567081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22052373793875740824357765 4134820086351701404567081)
                    ·
                      refine ⟨3101115064763776053425311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134820086351701404567081 3101115064763776053425311)
                      ·
                        rfl

theorem cell23_6039400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_6039400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039400 prefixEnd_6039400 := by exact prefixLift 6039400
  have htrace : WordTrace (prefixWord ++ tailWord_6039400) baseStart_6039400 baseEnd_6039400 := by
    simpa [prefixWord, tailWord_6039400, baseEnd_6039400] using wordTrace_append hprefix tailTrace_6039400
  have hstable : (prefixWord ++ tailWord_6039400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039400).length < 2 ^ (prefixWord ++ tailWord_6039400).sum := by decide
  have hdescent : baseEnd_6039400 < baseStart_6039400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039413 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 2, 4, 4]
def baseStart_6039413 : Nat := 118140960795 + 6039413 * 2 ^ 59
def prefixEnd_6039413 : Nat := 4983230072969 + 3 ^ 40 * 6039413 * 2
def baseEnd_6039413 : Nat := 3101121740012284502562751

theorem tailTrace_6039413 : CollatzResearch.WordTrace tailWord_6039413 prefixEnd_6039413 3101121740012284502562751 := by
  unfold tailWord_6039413
  simp only [CollatzResearch.WordTrace]
  refine ⟨220275488469245625467610893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146850325646163750311740595 220275488469245625467610893)
  ·
    refine ⟨82603308175967109550354085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220275488469245625467610893 82603308175967109550354085)
    ·
      refine ⟨15488120282993833040691391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82603308175967109550354085 15488120282993833040691391)
      ·
        refine ⟨23232180424490749561037087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15488120282993833040691391 23232180424490749561037087)
        ·
          refine ⟨34848270636736124341555631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23232180424490749561037087 34848270636736124341555631)
          ·
            refine ⟨52272405955104186512333447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34848270636736124341555631 52272405955104186512333447)
            ·
              refine ⟨78408608932656279768500171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52272405955104186512333447 78408608932656279768500171)
              ·
                refine ⟨117612913398984419652750257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78408608932656279768500171 117612913398984419652750257)
                ·
                  refine ⟨88209685049238314739562693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117612913398984419652750257 88209685049238314739562693)
                  ·
                    refine ⟨16539315946732184013668005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88209685049238314739562693 16539315946732184013668005)
                    ·
                      refine ⟨3101121740012284502562751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16539315946732184013668005 3101121740012284502562751)
                      ·
                        rfl

theorem cell23_6039413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_6039413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039413 prefixEnd_6039413 := by exact prefixLift 6039413
  have htrace : WordTrace (prefixWord ++ tailWord_6039413) baseStart_6039413 baseEnd_6039413 := by
    simpa [prefixWord, tailWord_6039413, baseEnd_6039413] using wordTrace_append hprefix tailTrace_6039413
  have hstable : (prefixWord ++ tailWord_6039413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039413).length < 2 ^ (prefixWord ++ tailWord_6039413).sum := by decide
  have hdescent : baseEnd_6039413 < baseStart_6039413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039427 : List Nat := [1, 1, 1, 3, 4, 2, 3, 3, 1, 4]
def baseStart_6039427 : Nat := 118140960795 + 6039427 * 2 ^ 59
def prefixEnd_6039427 : Nat := 4983230072969 + 3 ^ 40 * 6039427 * 2
def baseEnd_6039427 : Nat := 1033709642913815815929229

theorem tailTrace_6039427 : CollatzResearch.WordTrace tailWord_6039427 prefixEnd_6039427 1033709642913815815929229 := by
  unfold tailWord_6039427
  simp only [CollatzResearch.WordTrace]
  refine ⟨220275999091194905858620535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146850666060796603905747023 220275999091194905858620535)
  ·
    refine ⟨330413998636792358787930803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220275999091194905858620535 330413998636792358787930803)
    ·
      refine ⟨495620997955188538181896205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330413998636792358787930803 495620997955188538181896205)
      ·
        refine ⟨185857874233195701818211077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 495620997955188538181896205 185857874233195701818211077)
        ·
          refine ⟨34848351418724194090914577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185857874233195701818211077 34848351418724194090914577)
          ·
            refine ⟨26136263564043145568185933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34848351418724194090914577 26136263564043145568185933)
            ·
              refine ⟨9801098836516179588069725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26136263564043145568185933 9801098836516179588069725)
              ·
                refine ⟨3675412063693567345526147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9801098836516179588069725 3675412063693567345526147)
                ·
                  refine ⟨5513118095540351018289221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675412063693567345526147 5513118095540351018289221)
                  ·
                    refine ⟨1033709642913815815929229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5513118095540351018289221 1033709642913815815929229)
                    ·
                      rfl

theorem cell23_6039427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 3, 1, 4].length) (baseStart_6039427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039427 prefixEnd_6039427 := by exact prefixLift 6039427
  have htrace : WordTrace (prefixWord ++ tailWord_6039427) baseStart_6039427 baseEnd_6039427 := by
    simpa [prefixWord, tailWord_6039427, baseEnd_6039427] using wordTrace_append hprefix tailTrace_6039427
  have hstable : (prefixWord ++ tailWord_6039427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039427).length < 2 ^ (prefixWord ++ tailWord_6039427).sum := by decide
  have hdescent : baseEnd_6039427 < baseStart_6039427 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039477 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 2, 3, 2]
def baseStart_6039477 : Nat := 118140960795 + 6039477 * 2 ^ 59
def prefixEnd_6039477 : Nat := 4983230072969 + 3 ^ 40 * 6039477 * 2
def baseEnd_6039477 : Nat := 3101154602774172252162457

theorem tailTrace_6039477 : CollatzResearch.WordTrace tailWord_6039477 prefixEnd_6039477 3101154602774172252162457 := by
  unfold tailWord_6039477
  simp only [CollatzResearch.WordTrace]
  refine ⟨220277822741013764397940685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146851881827342509598627123 220277822741013764397940685)
  ·
    refine ⟨82604183527880161649227757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220277822741013764397940685 82604183527880161649227757)
    ·
      refine ⟨30976568822955060618460409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82604183527880161649227757 30976568822955060618460409)
      ·
        refine ⟨23232426617216295463845307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30976568822955060618460409 23232426617216295463845307)
        ·
          refine ⟨34848639925824443195767961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23232426617216295463845307 34848639925824443195767961)
          ·
            refine ⟨26136479944368332396825971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34848639925824443195767961 26136479944368332396825971)
            ·
              refine ⟨39204719916552498595238957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26136479944368332396825971 39204719916552498595238957)
              ·
                refine ⟨14701769968707186973214609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39204719916552498595238957 14701769968707186973214609)
                ·
                  refine ⟨11026327476530390229910957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14701769968707186973214609 11026327476530390229910957)
                  ·
                    refine ⟨4134872803698896336216609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11026327476530390229910957 4134872803698896336216609)
                    ·
                      refine ⟨3101154602774172252162457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134872803698896336216609 3101154602774172252162457)
                      ·
                        rfl

theorem cell23_6039477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_6039477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039477 prefixEnd_6039477 := by exact prefixLift 6039477
  have htrace : WordTrace (prefixWord ++ tailWord_6039477) baseStart_6039477 baseEnd_6039477 := by
    simpa [prefixWord, tailWord_6039477, baseEnd_6039477] using wordTrace_append hprefix tailTrace_6039477
  have hstable : (prefixWord ++ tailWord_6039477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039477).length < 2 ^ (prefixWord ++ tailWord_6039477).sum := by decide
  have hdescent : baseEnd_6039477 < baseStart_6039477 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039493 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 5]
def baseStart_6039493 : Nat := 118140960795 + 6039493 * 2 ^ 59
def prefixEnd_6039493 : Nat := 4983230072969 + 3 ^ 40 * 6039493 * 2
def baseEnd_6039493 : Nat := 3101162818464644189562383

theorem tailTrace_6039493 : CollatzResearch.WordTrace tailWord_6039493 prefixEnd_6039493 3101162818464644189562383 := by
  unfold tailWord_6039493
  simp only [CollatzResearch.WordTrace]
  refine ⟨220278406308955799130523133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146852270872637199420348755 220278406308955799130523133)
  ·
    refine ⟨82604402365858424673946175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220278406308955799130523133 82604402365858424673946175)
    ·
      refine ⟨123906603548787637010919263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82604402365858424673946175 123906603548787637010919263)
      ·
        refine ⟨185859905323181455516378895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123906603548787637010919263 185859905323181455516378895)
        ·
          refine ⟨278789857984772183274568343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185859905323181455516378895 278789857984772183274568343)
          ·
            refine ⟨418184786977158274911852515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278789857984772183274568343 418184786977158274911852515)
            ·
              refine ⟨627277180465737412367778773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418184786977158274911852515 627277180465737412367778773)
              ·
                refine ⟨14701808917165720602369815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 627277180465737412367778773 14701808917165720602369815)
                ·
                  refine ⟨22052713375748580903554723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14701808917165720602369815 22052713375748580903554723)
                  ·
                    refine ⟨33079070063622871355332085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22052713375748580903554723 33079070063622871355332085)
                    ·
                      refine ⟨3101162818464644189562383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33079070063622871355332085 3101162818464644189562383)
                      ·
                        rfl

theorem cell23_6039493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 1, 5].length) (baseStart_6039493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039493 prefixEnd_6039493 := by exact prefixLift 6039493
  have htrace : WordTrace (prefixWord ++ tailWord_6039493) baseStart_6039493 baseEnd_6039493 := by
    simpa [prefixWord, tailWord_6039493, baseEnd_6039493] using wordTrace_append hprefix tailTrace_6039493
  have hstable : (prefixWord ++ tailWord_6039493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039493).length < 2 ^ (prefixWord ++ tailWord_6039493).sum := by decide
  have hdescent : baseEnd_6039493 < baseStart_6039493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039503 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 4]
def baseStart_6039503 : Nat := 118140960795 + 6039503 * 2 ^ 59
def prefixEnd_6039503 : Nat := 4983230072969 + 3 ^ 40 * 6039503 * 2
def baseEnd_6039503 : Nat := 3101167953271189150437337

theorem tailTrace_6039503 : CollatzResearch.WordTrace tailWord_6039503 prefixEnd_6039503 3101167953271189150437337 := by
  unfold tailWord_6039503
  simp only [CollatzResearch.WordTrace]
  refine ⟨220278771038919570838387163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146852514025946380558924775 220278771038919570838387163)
  ·
    refine ⟨330418156558379356257580745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220278771038919570838387163 330418156558379356257580745)
    ·
      refine ⟨247813617418784517193185559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330418156558379356257580745 247813617418784517193185559)
      ·
        refine ⟨371720426128176775789778339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247813617418784517193185559 371720426128176775789778339)
        ·
          refine ⟨557580639192265163684667509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371720426128176775789778339 557580639192265163684667509)
          ·
            refine ⟨52273184924274859095437579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 557580639192265163684667509 52273184924274859095437579)
            ·
              refine ⟨78409777386412288643156369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52273184924274859095437579 78409777386412288643156369)
              ·
                refine ⟨58807333039809216482367277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78409777386412288643156369 58807333039809216482367277)
                ·
                  refine ⟨22052749889928456180887729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58807333039809216482367277 22052749889928456180887729)
                  ·
                    refine ⟨16539562417446342135665797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22052749889928456180887729 16539562417446342135665797)
                    ·
                      refine ⟨3101167953271189150437337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16539562417446342135665797 3101167953271189150437337)
                      ·
                        rfl

theorem cell23_6039503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 2, 4].length) (baseStart_6039503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039503 prefixEnd_6039503 := by exact prefixLift 6039503
  have htrace : WordTrace (prefixWord ++ tailWord_6039503) baseStart_6039503 baseEnd_6039503 := by
    simpa [prefixWord, tailWord_6039503, baseEnd_6039503] using wordTrace_append hprefix tailTrace_6039503
  have hstable : (prefixWord ++ tailWord_6039503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039503).length < 2 ^ (prefixWord ++ tailWord_6039503).sum := by decide
  have hdescent : baseEnd_6039503 < baseStart_6039503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039517 : List Nat := [1, 4, 3, 1, 3, 1, 2, 1, 1, 6]
def baseStart_6039517 : Nat := 118140960795 + 6039517 * 2 ^ 59
def prefixEnd_6039517 : Nat := 4983230072969 + 3 ^ 40 * 6039517 * 2
def baseEnd_6039517 : Nat := 1033725047333450698554091

theorem tailTrace_6039517 : CollatzResearch.WordTrace tailWord_6039517 prefixEnd_6039517 1033725047333450698554091 := by
  unfold tailWord_6039517
  simp only [CollatzResearch.WordTrace]
  refine ⟨220279281660868851229396805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146852854440579234152931203 220279281660868851229396805)
  ·
    refine ⟨41302365311412909605511901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220279281660868851229396805 41302365311412909605511901)
    ·
      refine ⟨15488386991779841102066963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41302365311412909605511901 15488386991779841102066963)
      ·
        refine ⟨23232580487669761653100445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15488386991779841102066963 23232580487669761653100445)
        ·
          refine ⟨8712217682876160619912667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23232580487669761653100445 8712217682876160619912667)
          ·
            refine ⟨13068326524314240929869001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8712217682876160619912667 13068326524314240929869001)
            ·
              refine ⟨9801244893235680697401751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13068326524314240929869001 9801244893235680697401751)
              ·
                refine ⟨14701867339853521046102627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9801244893235680697401751 14701867339853521046102627)
                ·
                  refine ⟨22052801009780281569153941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14701867339853521046102627 22052801009780281569153941)
                  ·
                    refine ⟨1033725047333450698554091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22052801009780281569153941 1033725047333450698554091)
                    ·
                      rfl

theorem cell23_6039517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_6039517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039517 prefixEnd_6039517 := by exact prefixLift 6039517
  have htrace : WordTrace (prefixWord ++ tailWord_6039517) baseStart_6039517 baseEnd_6039517 := by
    simpa [prefixWord, tailWord_6039517, baseEnd_6039517] using wordTrace_append hprefix tailTrace_6039517
  have hstable : (prefixWord ++ tailWord_6039517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039517).length < 2 ^ (prefixWord ++ tailWord_6039517).sum := by decide
  have hdescent : baseEnd_6039517 < baseStart_6039517 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039530 : List Nat := [3, 1, 3, 1, 2, 1, 5, 7]
def baseStart_6039530 : Nat := 118140960795 + 6039530 * 2 ^ 59
def prefixEnd_6039530 : Nat := 4983230072969 + 3 ^ 40 * 6039530 * 2
def baseEnd_6039530 : Nat := 114858585824031872029619

theorem tailTrace_6039530 : CollatzResearch.WordTrace tailWord_6039530 prefixEnd_6039530 114858585824031872029619 := by
  unfold tailWord_6039530
  simp only [CollatzResearch.WordTrace]
  refine ⟨55069938952455438612405011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146853170539881169633080029 55069938952455438612405011)
  ·
    refine ⟨82604908428683157918607517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55069938952455438612405011 82604908428683157918607517)
    ·
      refine ⟨30976840660756184219477819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82604908428683157918607517 30976840660756184219477819)
      ·
        refine ⟨46465260991134276329216729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30976840660756184219477819 46465260991134276329216729)
        ·
          refine ⟨34848945743350707246912547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46465260991134276329216729 34848945743350707246912547)
          ·
            refine ⟨52273418615026060870368821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34848945743350707246912547 52273418615026060870368821)
            ·
              refine ⟨4900632995158693206597077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52273418615026060870368821 4900632995158693206597077)
              ·
                refine ⟨114858585824031872029619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4900632995158693206597077 114858585824031872029619)
                ·
                  rfl

theorem cell23_6039530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 5, 7].length) (baseStart_6039530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039530 prefixEnd_6039530 := by exact prefixLift 6039530
  have htrace : WordTrace (prefixWord ++ tailWord_6039530) baseStart_6039530 baseEnd_6039530 := by
    simpa [prefixWord, tailWord_6039530, baseEnd_6039530] using wordTrace_append hprefix tailTrace_6039530
  have hstable : (prefixWord ++ tailWord_6039530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039530).length < 2 ^ (prefixWord ++ tailWord_6039530).sum := by decide
  have hdescent : baseEnd_6039530 < baseStart_6039530 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039557 : List Nat := [1, 3, 1, 1, 2, 5, 1, 1, 4, 1, 3]
def baseStart_6039557 : Nat := 118140960795 + 6039557 * 2 ^ 59
def prefixEnd_6039557 : Nat := 4983230072969 + 3 ^ 40 * 6039557 * 2
def baseEnd_6039557 : Nat := 3101195681226531939162089

theorem tailTrace_6039557 : CollatzResearch.WordTrace tailWord_6039557 prefixEnd_6039557 3101195681226531939162089 := by
  unfold tailWord_6039557
  simp only [CollatzResearch.WordTrace]
  refine ⟨220280740580723938060852925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146853827053815958707235283 220280740580723938060852925)
  ·
    refine ⟨82605277717771476772819847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220280740580723938060852925 82605277717771476772819847)
    ·
      refine ⟨123907916576657215159229771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82605277717771476772819847 123907916576657215159229771)
      ·
        refine ⟨185861874864985822738844657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123907916576657215159229771 185861874864985822738844657)
        ·
          refine ⟨139396406148739367054133493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185861874864985822738844657 139396406148739367054133493)
          ·
            refine ⟨13068413076444315661325015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139396406148739367054133493 13068413076444315661325015)
            ·
              refine ⟨19602619614666473491987523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13068413076444315661325015 19602619614666473491987523)
              ·
                refine ⟨29403929421999710237981285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19602619614666473491987523 29403929421999710237981285)
                ·
                  refine ⟨5513236766624945669621491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29403929421999710237981285 5513236766624945669621491)
                  ·
                    refine ⟨8269855149937418504432237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5513236766624945669621491 8269855149937418504432237)
                    ·
                      refine ⟨3101195681226531939162089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8269855149937418504432237 3101195681226531939162089)
                      ·
                        rfl

theorem cell23_6039557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 1, 4, 1, 3].length) (baseStart_6039557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039557 prefixEnd_6039557 := by exact prefixLift 6039557
  have htrace : WordTrace (prefixWord ++ tailWord_6039557) baseStart_6039557 baseEnd_6039557 := by
    simpa [prefixWord, tailWord_6039557, baseEnd_6039557] using wordTrace_append hprefix tailTrace_6039557
  have hstable : (prefixWord ++ tailWord_6039557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039557).length < 2 ^ (prefixWord ++ tailWord_6039557).sum := by decide
  have hdescent : baseEnd_6039557 < baseStart_6039557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039592 : List Nat := [2, 1, 5, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_6039592 : Nat := 118140960795 + 6039592 * 2 ^ 59
def prefixEnd_6039592 : Nat := 4983230072969 + 3 ^ 40 * 6039592 * 2
def baseEnd_6039592 : Nat := 3101213653049439302224429

theorem tailTrace_6039592 : CollatzResearch.WordTrace tailWord_6039592 prefixEnd_6039592 3101213653049439302224429 := by
  unfold tailWord_6039592
  simp only [CollatzResearch.WordTrace]
  refine ⟨110141008567798569519188515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146854678090398092692251353 110141008567798569519188515)
  ·
    refine ⟨165211512851697854278782773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110141008567798569519188515 165211512851697854278782773)
    ·
      refine ⟨15488579329846673838635885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165211512851697854278782773 15488579329846673838635885)
      ·
        refine ⟨5808217248692502689488457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15488579329846673838635885 5808217248692502689488457)
        ·
          refine ⟨4356162936519377017116343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5808217248692502689488457 4356162936519377017116343)
          ·
            refine ⟨6534244404779065525674515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4356162936519377017116343 6534244404779065525674515)
            ·
              refine ⟨9801366607168598288511773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6534244404779065525674515 9801366607168598288511773)
              ·
                refine ⟨3675512477688224358191915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9801366607168598288511773 3675512477688224358191915)
                ·
                  refine ⟨5513268716532336537287873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675512477688224358191915 5513268716532336537287873)
                  ·
                    refine ⟨4134951537399252402965905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5513268716532336537287873 4134951537399252402965905)
                    ·
                      refine ⟨3101213653049439302224429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4134951537399252402965905 3101213653049439302224429)
                      ·
                        rfl

theorem cell23_6039592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_6039592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039592 prefixEnd_6039592 := by exact prefixLift 6039592
  have htrace : WordTrace (prefixWord ++ tailWord_6039592) baseStart_6039592 baseEnd_6039592 := by
    simpa [prefixWord, tailWord_6039592, baseEnd_6039592] using wordTrace_append hprefix tailTrace_6039592
  have hstable : (prefixWord ++ tailWord_6039592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039592).length < 2 ^ (prefixWord ++ tailWord_6039592).sum := by decide
  have hdescent : baseEnd_6039592 < baseStart_6039592 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039600 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 5]
def baseStart_6039600 : Nat := 118140960795 + 6039600 * 2 ^ 59
def prefixEnd_6039600 : Nat := 4983230072969 + 3 ^ 40 * 6039600 * 2
def baseEnd_6039600 : Nat := 3101217760894675270924391

theorem tailTrace_6039600 : CollatzResearch.WordTrace tailWord_6039600 prefixEnd_6039600 3101217760894675270924391 := by
  unfold tailWord_6039600
  simp only [CollatzResearch.WordTrace]
  refine ⟨110141154459784078202334127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146854872613045437603112169 110141154459784078202334127)
  ·
    refine ⟨165211731689676117303501191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110141154459784078202334127 165211731689676117303501191)
    ·
      refine ⟨247817597534514175955251787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165211731689676117303501191 247817597534514175955251787)
      ·
        refine ⟨371726396301771263932877681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247817597534514175955251787 371726396301771263932877681)
        ·
          refine ⟨278794797226328447949658261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371726396301771263932877681 278794797226328447949658261)
          ·
            refine ⟨13068506119984145997640231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 278794797226328447949658261 13068506119984145997640231)
            ·
              refine ⟨19602759179976218996460347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13068506119984145997640231 19602759179976218996460347)
              ·
                refine ⟨29404138769964328494690521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19602759179976218996460347 29404138769964328494690521)
                ·
                  refine ⟨22053104077473246371017891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29404138769964328494690521 22053104077473246371017891)
                  ·
                    refine ⟨33079656116209869556526837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22053104077473246371017891 33079656116209869556526837)
                    ·
                      refine ⟨3101217760894675270924391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33079656116209869556526837 3101217760894675270924391)
                      ·
                        rfl

theorem cell23_6039600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 5].length) (baseStart_6039600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039600 prefixEnd_6039600 := by exact prefixLift 6039600
  have htrace : WordTrace (prefixWord ++ tailWord_6039600) baseStart_6039600 baseEnd_6039600 := by
    simpa [prefixWord, tailWord_6039600, baseEnd_6039600] using wordTrace_append hprefix tailTrace_6039600
  have hstable : (prefixWord ++ tailWord_6039600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039600).length < 2 ^ (prefixWord ++ tailWord_6039600).sum := by decide
  have hdescent : baseEnd_6039600 < baseStart_6039600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039603 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 9]
def baseStart_6039603 : Nat := 118140960795 + 6039603 * 2 ^ 59
def prefixEnd_6039603 : Nat := 4983230072969 + 3 ^ 40 * 6039603 * 2
def baseEnd_6039603 : Nat := 344579922370737639909653

theorem tailTrace_6039603 : CollatzResearch.WordTrace tailWord_6039603 prefixEnd_6039603 344579922370737639909653 := by
  unfold tailWord_6039603
  simp only [CollatzResearch.WordTrace]
  refine ⟨220282418338557287917027463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146854945559038191944684975 220282418338557287917027463)
  ·
    refine ⟨330423627507835931875541195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220282418338557287917027463 330423627507835931875541195)
    ·
      refine ⟨495635441261753897813311793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330423627507835931875541195 495635441261753897813311793)
      ·
        refine ⟨371726580946315423359983845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495635441261753897813311793 371726580946315423359983845)
        ·
          refine ⟨69698733927434141879996971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 371726580946315423359983845 69698733927434141879996971)
          ·
            refine ⟨104548100891151212819995457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69698733927434141879996971 104548100891151212819995457)
            ·
              refine ⟨78411075668363409614996593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104548100891151212819995457 78411075668363409614996593)
              ·
                refine ⟨58808306751272557211247445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78411075668363409614996593 58808306751272557211247445)
                ·
                  refine ⟨344579922370737639909653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 58808306751272557211247445 344579922370737639909653)
                  ·
                    rfl

theorem cell23_6039603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 9].length) (baseStart_6039603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039603 prefixEnd_6039603 := by exact prefixLift 6039603
  have htrace : WordTrace (prefixWord ++ tailWord_6039603) baseStart_6039603 baseEnd_6039603 := by
    simpa [prefixWord, tailWord_6039603, baseEnd_6039603] using wordTrace_append hprefix tailTrace_6039603
  have hstable : (prefixWord ++ tailWord_6039603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039603).length < 2 ^ (prefixWord ++ tailWord_6039603).sum := by decide
  have hdescent : baseEnd_6039603 < baseStart_6039603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039660 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 5]
def baseStart_6039660 : Nat := 118140960795 + 6039660 * 2 ^ 59
def prefixEnd_6039660 : Nat := 4983230072969 + 3 ^ 40 * 6039660 * 2
def baseEnd_6039660 : Nat := 3101248569733945036174115

theorem tailTrace_6039660 : CollatzResearch.WordTrace tailWord_6039660 prefixEnd_6039660 3101248569733945036174115 := by
  unfold tailWord_6039660
  simp only [CollatzResearch.WordTrace]
  refine ⟨110142248649675393325926217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146856331532900524434568289 110142248649675393325926217)
  ·
    refine ⟨82606686487256544994444663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110142248649675393325926217 82606686487256544994444663)
    ·
      refine ⟨123910029730884817491666995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82606686487256544994444663 123910029730884817491666995)
      ·
        refine ⟨185865044596327226237500493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123910029730884817491666995 185865044596327226237500493)
        ·
          refine ⟨69699391723622709839062685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185865044596327226237500493 69699391723622709839062685)
          ·
            refine ⟨26137271896358516189648507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69699391723622709839062685 26137271896358516189648507)
            ·
              refine ⟨39205907844537774284472761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26137271896358516189648507 39205907844537774284472761)
              ·
                refine ⟨29404430883403330713354571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39205907844537774284472761 29404430883403330713354571)
                ·
                  refine ⟨44106646325104996070031857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29404430883403330713354571 44106646325104996070031857)
                  ·
                    refine ⟨33079984743828747052523893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44106646325104996070031857 33079984743828747052523893)
                    ·
                      refine ⟨3101248569733945036174115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33079984743828747052523893 3101248569733945036174115)
                      ·
                        rfl

theorem cell23_6039660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 5].length) (baseStart_6039660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039660 prefixEnd_6039660 := by exact prefixLift 6039660
  have htrace : WordTrace (prefixWord ++ tailWord_6039660) baseStart_6039660 baseEnd_6039660 := by
    simpa [prefixWord, tailWord_6039660, baseEnd_6039660] using wordTrace_append hprefix tailTrace_6039660
  have hstable : (prefixWord ++ tailWord_6039660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039660).length < 2 ^ (prefixWord ++ tailWord_6039660).sum := by decide
  have hdescent : baseEnd_6039660 < baseStart_6039660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039687 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 1, 6, 2]
def baseStart_6039687 : Nat := 118140960795 + 6039687 * 2 ^ 59
def prefixEnd_6039687 : Nat := 4983230072969 + 3 ^ 40 * 6039687 * 2
def baseEnd_6039687 : Nat := 3101262433711616430536491

theorem tailTrace_6039687 : CollatzResearch.WordTrace tailWord_6039687 prefixEnd_6039687 3101262433711616430536491 := by
  unfold tailWord_6039687
  simp only [CollatzResearch.WordTrace]
  refine ⟨220285482070252970263085315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146856988046835313508723543 220285482070252970263085315)
  ·
    refine ⟨330428223105379455394627973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220285482070252970263085315 330428223105379455394627973)
    ·
      refine ⟨61955291832258647886492745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 330428223105379455394627973 61955291832258647886492745)
      ·
        refine ⟨46466468874193985914869559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61955291832258647886492745 46466468874193985914869559)
        ·
          refine ⟨69699703311290978872304339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46466468874193985914869559 69699703311290978872304339)
          ·
            refine ⟨104549554966936468308456509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69699703311290978872304339 104549554966936468308456509)
            ·
              refine ⟨39206083112601175615671191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104549554966936468308456509 39206083112601175615671191)
              ·
                refine ⟨58809124668901763423506787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39206083112601175615671191 58809124668901763423506787)
                ·
                  refine ⟨88213687003352645135260181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58809124668901763423506787 88213687003352645135260181)
                  ·
                    refine ⟨4135016578282155240715321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88213687003352645135260181 4135016578282155240715321)
                    ·
                      refine ⟨3101262433711616430536491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135016578282155240715321 3101262433711616430536491)
                      ·
                        rfl

theorem cell23_6039687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_6039687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039687 prefixEnd_6039687 := by exact prefixLift 6039687
  have htrace : WordTrace (prefixWord ++ tailWord_6039687) baseStart_6039687 baseEnd_6039687 := by
    simpa [prefixWord, tailWord_6039687, baseEnd_6039687] using wordTrace_append hprefix tailTrace_6039687
  have hstable : (prefixWord ++ tailWord_6039687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039687).length < 2 ^ (prefixWord ++ tailWord_6039687).sum := by decide
  have hdescent : baseEnd_6039687 < baseStart_6039687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039730 : List Nat := [3, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8]
def baseStart_6039730 : Nat := 118140960795 + 6039730 * 2 ^ 59
def prefixEnd_6039730 : Nat := 4983230072969 + 3 ^ 40 * 6039730 * 2
def baseEnd_6039730 : Nat := 3101284513379759762298793

theorem tailTrace_6039730 : CollatzResearch.WordTrace tailWord_6039730 prefixEnd_6039730 3101284513379759762298793 := by
  unfold tailWord_6039730
  simp only [CollatzResearch.WordTrace]
  refine ⟨55071762602274297151725161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146858033606064792404600429 55071762602274297151725161)
  ·
    refine ⟨41303821951705722863793871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55071762602274297151725161 41303821951705722863793871)
    ·
      refine ⟨61955732927558584295690807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41303821951705722863793871 61955732927558584295690807)
      ·
        refine ⟨92933599391337876443536211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61955732927558584295690807 92933599391337876443536211)
        ·
          refine ⟨139400399087006814665304317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92933599391337876443536211 139400399087006814665304317)
          ·
            refine ⟨52275149657627555499489119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139400399087006814665304317 52275149657627555499489119)
            ·
              refine ⟨78412724486441333249233679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52275149657627555499489119 78412724486441333249233679)
              ·
                refine ⟨117619086729661999873850519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78412724486441333249233679 117619086729661999873850519)
                ·
                  refine ⟨176428630094492999810775779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117619086729661999873850519 176428630094492999810775779)
                  ·
                    refine ⟨264642945141739499716163669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 176428630094492999810775779 264642945141739499716163669)
                    ·
                      refine ⟨3101284513379759762298793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 264642945141739499716163669 3101284513379759762298793)
                      ·
                        rfl

theorem cell23_6039730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_6039730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039730 prefixEnd_6039730 := by exact prefixLift 6039730
  have htrace : WordTrace (prefixWord ++ tailWord_6039730) baseStart_6039730 baseEnd_6039730 := by
    simpa [prefixWord, tailWord_6039730, baseEnd_6039730] using wordTrace_append hprefix tailTrace_6039730
  have hstable : (prefixWord ++ tailWord_6039730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039730).length < 2 ^ (prefixWord ++ tailWord_6039730).sum := by decide
  have hdescent : baseEnd_6039730 < baseStart_6039730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039744 : List Nat := [2, 1, 1, 2, 5, 2, 3, 1, 6]
def baseStart_6039744 : Nat := 118140960795 + 6039744 * 2 ^ 59
def prefixEnd_6039744 : Nat := 4983230072969 + 3 ^ 40 * 6039744 * 2
def baseEnd_6039744 : Nat := 344587966900991411947081

theorem tailTrace_6039744 : CollatzResearch.WordTrace tailWord_6039744 prefixEnd_6039744 344587966900991411947081 := by
  unfold tailWord_6039744
  simp only [CollatzResearch.WordTrace]
  refine ⟨110143780515523234498955143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146858374020697645998606857 110143780515523234498955143)
  ·
    refine ⟨165215670773284851748432715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110143780515523234498955143 165215670773284851748432715)
    ·
      refine ⟨247823506159927277622649073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165215670773284851748432715 247823506159927277622649073)
      ·
        refine ⟨185867629619945458216986805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247823506159927277622649073 185867629619945458216986805)
        ·
          refine ⟨17425090276869886707842513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 185867629619945458216986805 17425090276869886707842513)
          ·
            refine ⟨13068817707652415030881885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17425090276869886707842513 13068817707652415030881885)
            ·
              refine ⟨4900806640369655636580707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13068817707652415030881885 4900806640369655636580707)
              ·
                refine ⟨7351209960554483454871061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4900806640369655636580707 7351209960554483454871061)
                ·
                  refine ⟨344587966900991411947081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7351209960554483454871061 344587966900991411947081)
                  ·
                    rfl

theorem cell23_6039744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 6].length) (baseStart_6039744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039744 prefixEnd_6039744 := by exact prefixLift 6039744
  have htrace : WordTrace (prefixWord ++ tailWord_6039744) baseStart_6039744 baseEnd_6039744 := by
    simpa [prefixWord, tailWord_6039744, baseEnd_6039744] using wordTrace_append hprefix tailTrace_6039744
  have hstable : (prefixWord ++ tailWord_6039744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039744).length < 2 ^ (prefixWord ++ tailWord_6039744).sum := by decide
  have hdescent : baseEnd_6039744 < baseStart_6039744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039754 : List Nat := [3, 1, 2, 1, 3, 1, 1, 4, 3, 1, 3]
def baseStart_6039754 : Nat := 118140960795 + 6039754 * 2 ^ 59
def prefixEnd_6039754 : Nat := 4983230072969 + 3 ^ 40 * 6039754 * 2
def baseEnd_6039754 : Nat := 3101296836915467668398683

theorem tailTrace_6039754 : CollatzResearch.WordTrace tailWord_6039754 prefixEnd_6039754 3101296836915467668398683 := by
  unfold tailWord_6039754
  simp only [CollatzResearch.WordTrace]
  refine ⟨55071981440252560176443579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146858617174006827137182877 55071981440252560176443579)
  ·
    refine ⟨82607972160378840264665369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55071981440252560176443579 82607972160378840264665369)
    ·
      refine ⟨61955979120284130198499027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82607972160378840264665369 61955979120284130198499027)
      ·
        refine ⟨92933968680426195297748541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61955979120284130198499027 92933968680426195297748541)
        ·
          refine ⟨34850238255159823236655703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92933968680426195297748541 34850238255159823236655703)
          ·
            refine ⟨52275357382739734854983555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34850238255159823236655703 52275357382739734854983555)
            ·
              refine ⟨78413036074109602282475333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52275357382739734854983555 78413036074109602282475333)
              ·
                refine ⟨14702444263895550427964125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78413036074109602282475333 14702444263895550427964125)
                ·
                  refine ⟨5513416598960831410486547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14702444263895550427964125 5513416598960831410486547)
                  ·
                    refine ⟨8270124898441247115729821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5513416598960831410486547 8270124898441247115729821)
                    ·
                      refine ⟨3101296836915467668398683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8270124898441247115729821 3101296836915467668398683)
                      ·
                        rfl

theorem cell23_6039754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 4, 3, 1, 3].length) (baseStart_6039754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039754 prefixEnd_6039754 := by exact prefixLift 6039754
  have htrace : WordTrace (prefixWord ++ tailWord_6039754) baseStart_6039754 baseEnd_6039754 := by
    simpa [prefixWord, tailWord_6039754, baseEnd_6039754] using wordTrace_append hprefix tailTrace_6039754
  have hstable : (prefixWord ++ tailWord_6039754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039754).length < 2 ^ (prefixWord ++ tailWord_6039754).sum := by decide
  have hdescent : baseEnd_6039754 < baseStart_6039754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039760 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 4]
def baseStart_6039760 : Nat := 118140960795 + 6039760 * 2 ^ 59
def prefixEnd_6039760 : Nat := 4983230072969 + 3 ^ 40 * 6039760 * 2
def baseEnd_6039760 : Nat := 3101299917799394644923655

theorem tailTrace_6039760 : CollatzResearch.WordTrace tailWord_6039760 prefixEnd_6039760 3101299917799394644923655 := by
  unfold tailWord_6039760
  simp only [CollatzResearch.WordTrace]
  refine ⟨110144072299494251865246367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146858763065992335820328489 110144072299494251865246367)
  ·
    refine ⟨165216108449241377797869551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110144072299494251865246367 165216108449241377797869551)
    ·
      refine ⟨247824162673862066696804327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165216108449241377797869551 247824162673862066696804327)
      ·
        refine ⟨371736244010793100045206491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247824162673862066696804327 371736244010793100045206491)
        ·
          refine ⟨557604366016189650067809737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371736244010793100045206491 557604366016189650067809737)
          ·
            refine ⟨418203274512142237550857303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557604366016189650067809737 418203274512142237550857303)
            ·
              refine ⟨627304911768213356326285955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418203274512142237550857303 627304911768213356326285955)
              ·
                refine ⟨940957367652320034489428933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627304911768213356326285955 940957367652320034489428933)
                ·
                  refine ⟨176429506434810006466767925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 940957367652320034489428933 176429506434810006466767925)
                  ·
                    refine ⟨16540266228263438106259493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 176429506434810006466767925 16540266228263438106259493)
                    ·
                      refine ⟨3101299917799394644923655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16540266228263438106259493 3101299917799394644923655)
                      ·
                        rfl

theorem cell23_6039760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 4].length) (baseStart_6039760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039760 prefixEnd_6039760 := by exact prefixLift 6039760
  have htrace : WordTrace (prefixWord ++ tailWord_6039760) baseStart_6039760 baseEnd_6039760 := by
    simpa [prefixWord, tailWord_6039760, baseEnd_6039760] using wordTrace_append hprefix tailTrace_6039760
  have hstable : (prefixWord ++ tailWord_6039760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039760).length < 2 ^ (prefixWord ++ tailWord_6039760).sum := by decide
  have hdescent : baseEnd_6039760 < baseStart_6039760 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039765 : List Nat := [1, 3, 2, 4, 3, 1, 1, 3, 1, 4]
def baseStart_6039765 : Nat := 118140960795 + 6039765 * 2 ^ 59
def prefixEnd_6039765 : Nat := 4983230072969 + 3 ^ 40 * 6039765 * 2
def baseEnd_6039765 : Nat := 1033767495067555708453711

theorem tailTrace_6039765 : CollatzResearch.WordTrace tailWord_6039765 prefixEnd_6039765 1033767495067555708453711 := by
  unfold tailWord_6039765
  simp only [CollatzResearch.WordTrace]
  refine ⟨220288326963970389584424749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146858884642646926389616499 220288326963970389584424749)
  ·
    refine ⟨82608122611488896094159281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220288326963970389584424749 82608122611488896094159281)
    ·
      refine ⟨61956091958616672070619461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82608122611488896094159281 61956091958616672070619461)
      ·
        refine ⟨11616767242240626013241149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61956091958616672070619461 11616767242240626013241149)
        ·
          refine ⟨4356287715840234754965431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11616767242240626013241149 4356287715840234754965431)
          ·
            refine ⟨6534431573760352132448147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4356287715840234754965431 6534431573760352132448147)
            ·
              refine ⟨9801647360640528198672221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6534431573760352132448147 9801647360640528198672221)
              ·
                refine ⟨3675617760240198074502083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9801647360640528198672221 3675617760240198074502083)
                ·
                  refine ⟨5513426640360297111753125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675617760240198074502083 5513426640360297111753125)
                  ·
                    refine ⟨1033767495067555708453711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5513426640360297111753125 1033767495067555708453711)
                    ·
                      rfl

theorem cell23_6039765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_6039765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039765 prefixEnd_6039765 := by exact prefixLift 6039765
  have htrace : WordTrace (prefixWord ++ tailWord_6039765) baseStart_6039765 baseEnd_6039765 := by
    simpa [prefixWord, tailWord_6039765, baseEnd_6039765] using wordTrace_append hprefix tailTrace_6039765
  have hstable : (prefixWord ++ tailWord_6039765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039765).length < 2 ^ (prefixWord ++ tailWord_6039765).sum := by decide
  have hdescent : baseEnd_6039765 < baseStart_6039765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039781 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 2, 3, 2]
def baseStart_6039781 : Nat := 118140960795 + 6039781 * 2 ^ 59
def prefixEnd_6039781 : Nat := 4983230072969 + 3 ^ 40 * 6039781 * 2
def baseEnd_6039781 : Nat := 3101310700893139062761059

theorem tailTrace_6039781 : CollatzResearch.WordTrace tailWord_6039781 prefixEnd_6039781 3101310700893139062761059 := by
  unfold tailWord_6039781
  simp only [CollatzResearch.WordTrace]
  refine ⟨220288910531912424317007197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146859273687941616211338131 220288910531912424317007197)
  ·
    refine ⟨82608341449467159118877699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220288910531912424317007197 82608341449467159118877699)
    ·
      refine ⟨123912512174200738678316549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82608341449467159118877699 123912512174200738678316549)
      ·
        refine ⟨23233596032662638502184353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123912512174200738678316549 23233596032662638502184353)
        ·
          refine ⟨17425197024496978876638265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23233596032662638502184353 17425197024496978876638265)
          ·
            refine ⟨13068897768372734157478699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17425197024496978876638265 13068897768372734157478699)
            ·
              refine ⟨19603346652559101236218049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13068897768372734157478699 19603346652559101236218049)
              ·
                refine ⟨14702509989419325927163537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19603346652559101236218049 14702509989419325927163537)
                ·
                  refine ⟨11026882492064494445372653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14702509989419325927163537 11026882492064494445372653)
                  ·
                    refine ⟨4135080934524185417014745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11026882492064494445372653 4135080934524185417014745)
                    ·
                      refine ⟨3101310700893139062761059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135080934524185417014745 3101310700893139062761059)
                      ·
                        rfl

theorem cell23_6039781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_6039781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039781 prefixEnd_6039781 := by exact prefixLift 6039781
  have htrace : WordTrace (prefixWord ++ tailWord_6039781) baseStart_6039781 baseEnd_6039781 := by
    simpa [prefixWord, tailWord_6039781, baseEnd_6039781] using wordTrace_append hprefix tailTrace_6039781
  have hstable : (prefixWord ++ tailWord_6039781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039781).length < 2 ^ (prefixWord ++ tailWord_6039781).sum := by decide
  have hdescent : baseEnd_6039781 < baseStart_6039781 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039787 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 4, 4]
def baseStart_6039787 : Nat := 118140960795 + 6039787 * 2 ^ 59
def prefixEnd_6039787 : Nat := 4983230072969 + 3 ^ 40 * 6039787 * 2
def baseEnd_6039787 : Nat := 1033771260592355346428677

theorem tailTrace_6039787 : CollatzResearch.WordTrace tailWord_6039787 prefixEnd_6039787 1033771260592355346428677 := by
  unfold tailWord_6039787
  simp only [CollatzResearch.WordTrace]
  refine ⟨220289129369890687341725615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146859419579927124894483743 220289129369890687341725615)
  ·
    refine ⟨330433694054836031012588423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220289129369890687341725615 330433694054836031012588423)
    ·
      refine ⟨495650541082254046518882635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330433694054836031012588423 495650541082254046518882635)
      ·
        refine ⟨743475811623381069778323953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495650541082254046518882635 743475811623381069778323953)
        ·
          refine ⟨557606858717535802333742965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 743475811623381069778323953 557606858717535802333742965)
          ·
            refine ⟨52275643004768981468788403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 557606858717535802333742965 52275643004768981468788403)
            ·
              refine ⟨78413464507153472203182605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52275643004768981468788403 78413464507153472203182605)
              ·
                refine ⟨29405049190182552076193477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78413464507153472203182605 29405049190182552076193477)
                ·
                  refine ⟨5513446723159228514286277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29405049190182552076193477 5513446723159228514286277)
                  ·
                    refine ⟨1033771260592355346428677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5513446723159228514286277 1033771260592355346428677)
                    ·
                      rfl

theorem cell23_6039787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 4, 4].length) (baseStart_6039787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039787 prefixEnd_6039787 := by exact prefixLift 6039787
  have htrace : WordTrace (prefixWord ++ tailWord_6039787) baseStart_6039787 baseEnd_6039787 := by
    simpa [prefixWord, tailWord_6039787, baseEnd_6039787] using wordTrace_append hprefix tailTrace_6039787
  have hstable : (prefixWord ++ tailWord_6039787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039787).length < 2 ^ (prefixWord ++ tailWord_6039787).sum := by decide
  have hdescent : baseEnd_6039787 < baseStart_6039787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039788 : List Nat := [2, 2, 1, 1, 2, 3, 5, 2, 1, 1, 3]
def baseStart_6039788 : Nat := 118140960795 + 6039788 * 2 ^ 59
def prefixEnd_6039788 : Nat := 4983230072969 + 3 ^ 40 * 6039788 * 2
def baseEnd_6039788 : Nat := 3101314295257720535373527

theorem tailTrace_6039788 : CollatzResearch.WordTrace tailWord_6039788 prefixEnd_6039788 3101314295257720535373527 := by
  unfold tailWord_6039788
  simp only [CollatzResearch.WordTrace]
  refine ⟨110144582921443532256256009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146859443895258043008341345 110144582921443532256256009)
  ·
    refine ⟨82608437191082649192192007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110144582921443532256256009 82608437191082649192192007)
    ·
      refine ⟨123912655786623973788288011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82608437191082649192192007 123912655786623973788288011)
      ·
        refine ⟨185868983679935960682432017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123912655786623973788288011 185868983679935960682432017)
        ·
          refine ⟨139401737759951970511824013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185868983679935960682432017 139401737759951970511824013)
          ·
            refine ⟨52275651659981988941934005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139401737759951970511824013 52275651659981988941934005)
            ·
              refine ⟨4900842343123311463306313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52275651659981988941934005 4900842343123311463306313)
              ·
                refine ⟨3675631757342483597479735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4900842343123311463306313 3675631757342483597479735)
                ·
                  refine ⟨5513447636013725396219603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675631757342483597479735 5513447636013725396219603)
                  ·
                    refine ⟨8270171454020588094329405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5513447636013725396219603 8270171454020588094329405)
                    ·
                      refine ⟨3101314295257720535373527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8270171454020588094329405 3101314295257720535373527)
                      ·
                        rfl

theorem cell23_6039788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 5, 2, 1, 1, 3].length) (baseStart_6039788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039788 prefixEnd_6039788 := by exact prefixLift 6039788
  have htrace : WordTrace (prefixWord ++ tailWord_6039788) baseStart_6039788 baseEnd_6039788 := by
    simpa [prefixWord, tailWord_6039788, baseEnd_6039788] using wordTrace_append hprefix tailTrace_6039788
  have hstable : (prefixWord ++ tailWord_6039788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039788).length < 2 ^ (prefixWord ++ tailWord_6039788).sum := by decide
  have hdescent : baseEnd_6039788 < baseStart_6039788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039807 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 4]
def baseStart_6039807 : Nat := 118140960795 + 6039807 * 2 ^ 59
def prefixEnd_6039807 : Nat := 4983230072969 + 3 ^ 40 * 6039807 * 2
def baseEnd_6039807 : Nat := 3101324051390155961035939

theorem tailTrace_6039807 : CollatzResearch.WordTrace tailWord_6039807 prefixEnd_6039807 3101324051390155961035939 := by
  unfold tailWord_6039807
  simp only [CollatzResearch.WordTrace]
  refine ⟨220289858829818230757453675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146859905886545487171635783 220289858829818230757453675)
  ·
    refine ⟨330434788244727346136180513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220289858829818230757453675 330434788244727346136180513)
    ·
      refine ⟨247826091183545509602135385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330434788244727346136180513 247826091183545509602135385)
      ·
        refine ⟨185869568387659132201601539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247826091183545509602135385 185869568387659132201601539)
        ·
          refine ⟨278804352581488698302402309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185869568387659132201601539 278804352581488698302402309)
          ·
            refine ⟨52275816109029130931700433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278804352581488698302402309 52275816109029130931700433)
            ·
              refine ⟨39206862081771848198775325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52275816109029130931700433 39206862081771848198775325)
              ·
                refine ⟨14702573280664443074540747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39206862081771848198775325 14702573280664443074540747)
                ·
                  refine ⟨22053859920996664611811121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14702573280664443074540747 22053859920996664611811121)
                  ·
                    refine ⟨16540394940747498458858341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22053859920996664611811121 16540394940747498458858341)
                    ·
                      refine ⟨3101324051390155961035939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16540394940747498458858341 3101324051390155961035939)
                      ·
                        rfl

theorem cell23_6039807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_6039807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039807 prefixEnd_6039807 := by exact prefixLift 6039807
  have htrace : WordTrace (prefixWord ++ tailWord_6039807) baseStart_6039807 baseEnd_6039807 := by
    simpa [prefixWord, tailWord_6039807, baseEnd_6039807] using wordTrace_append hprefix tailTrace_6039807
  have hstable : (prefixWord ++ tailWord_6039807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039807).length < 2 ^ (prefixWord ++ tailWord_6039807).sum := by decide
  have hdescent : baseEnd_6039807 < baseStart_6039807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039838 : List Nat := [4, 3, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_6039838 : Nat := 118140960795 + 6039838 * 2 ^ 59
def prefixEnd_6039838 : Nat := 4983230072969 + 3 ^ 40 * 6039838 * 2
def baseEnd_6039838 : Nat := 1033779989763481779916099

theorem tailTrace_6039838 : CollatzResearch.WordTrace tailWord_6039838 prefixEnd_6039838 1033779989763481779916099 := by
  unfold tailWord_6039838
  simp only [CollatzResearch.WordTrace]
  refine ⟨27536373686588240381479021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146860659661803948701221445 27536373686588240381479021)
  ·
    refine ⟨10326140132470590143054633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27536373686588240381479021 10326140132470590143054633)
    ·
      refine ⟨7744605099352942607290975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10326140132470590143054633 7744605099352942607290975)
      ·
        refine ⟨11616907649029413910936463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7744605099352942607290975 11616907649029413910936463)
        ·
          refine ⟨17425361473544120866404695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11616907649029413910936463 17425361473544120866404695)
          ·
            refine ⟨26138042210316181299607043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17425361473544120866404695 26138042210316181299607043)
            ·
              refine ⟨39207063315474271949410565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26138042210316181299607043 39207063315474271949410565)
              ·
                refine ⟨7351324371651425990514481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39207063315474271949410565 7351324371651425990514481)
                ·
                  refine ⟨5513493278738569492885861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7351324371651425990514481 5513493278738569492885861)
                  ·
                    refine ⟨1033779989763481779916099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5513493278738569492885861 1033779989763481779916099)
                    ·
                      rfl

theorem cell23_6039838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_6039838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039838 prefixEnd_6039838 := by exact prefixLift 6039838
  have htrace : WordTrace (prefixWord ++ tailWord_6039838) baseStart_6039838 baseEnd_6039838 := by
    simpa [prefixWord, tailWord_6039838, baseEnd_6039838] using wordTrace_append hprefix tailTrace_6039838
  have hstable : (prefixWord ++ tailWord_6039838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039838).length < 2 ^ (prefixWord ++ tailWord_6039838).sum := by decide
  have hdescent : baseEnd_6039838 < baseStart_6039838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039845 : List Nat := [1, 3, 1, 2, 5, 1, 1, 4, 1, 2, 2]
def baseStart_6039845 : Nat := 118140960795 + 6039845 * 2 ^ 59
def prefixEnd_6039845 : Nat := 4983230072969 + 3 ^ 40 * 6039845 * 2
def baseEnd_6039845 : Nat := 3101343563655026812360765

theorem tailTrace_6039845 : CollatzResearch.WordTrace tailWord_6039845 prefixEnd_6039845 3101343563655026812360765 := by
  unfold tailWord_6039845
  simp only [CollatzResearch.WordTrace]
  refine ⟨220291244803680563247336989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146860829869120375498224659 220291244803680563247336989)
  ·
    refine ⟨82609216801380211217751371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220291244803680563247336989 82609216801380211217751371)
    ·
      refine ⟨123913825202070316826627057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82609216801380211217751371 123913825202070316826627057)
      ·
        refine ⟨92935368901552737619970293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123913825202070316826627057 92935368901552737619970293)
        ·
          refine ⟨8712690834520569151872215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 92935368901552737619970293 8712690834520569151872215)
          ·
            refine ⟨13069036251780853727808323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8712690834520569151872215 13069036251780853727808323)
            ·
              refine ⟨19603554377671280591712485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13069036251780853727808323 19603554377671280591712485)
              ·
                refine ⟨3675666445813365110946091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19603554377671280591712485 3675666445813365110946091)
                ·
                  refine ⟨5513499668720047666419137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675666445813365110946091 5513499668720047666419137)
                  ·
                    refine ⟨4135124751540035749814353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5513499668720047666419137 4135124751540035749814353)
                    ·
                      refine ⟨3101343563655026812360765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135124751540035749814353 3101343563655026812360765)
                      ·
                        rfl

theorem cell23_6039845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_6039845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039845 prefixEnd_6039845 := by exact prefixLift 6039845
  have htrace : WordTrace (prefixWord ++ tailWord_6039845) baseStart_6039845 baseEnd_6039845 := by
    simpa [prefixWord, tailWord_6039845, baseEnd_6039845] using wordTrace_append hprefix tailTrace_6039845
  have hstable : (prefixWord ++ tailWord_6039845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039845).length < 2 ^ (prefixWord ++ tailWord_6039845).sum := by decide
  have hdescent : baseEnd_6039845 < baseStart_6039845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039861 : List Nat := [1, 3, 3, 1, 2, 1, 1, 5, 2, 1, 3]
def baseStart_6039861 : Nat := 118140960795 + 6039861 * 2 ^ 59
def prefixEnd_6039861 : Nat := 4983230072969 + 3 ^ 40 * 6039861 * 2
def baseEnd_6039861 : Nat := 3101351779345498749760691

theorem tailTrace_6039861 : CollatzResearch.WordTrace tailWord_6039861 prefixEnd_6039861 3101351779345498749760691 := by
  unfold tailWord_6039861
  simp only [CollatzResearch.WordTrace]
  refine ⟨220291828371622597979919437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146861218914415065319946291 220291828371622597979919437)
  ·
    refine ⟨82609435639358474242469789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220291828371622597979919437 82609435639358474242469789)
    ·
      refine ⟨30978538364759427840926171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82609435639358474242469789 30978538364759427840926171)
      ·
        refine ⟨46467807547139141761389257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30978538364759427840926171 46467807547139141761389257)
        ·
          refine ⟨34850855660354356321041943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46467807547139141761389257 34850855660354356321041943)
          ·
            refine ⟨52276283490531534481562915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34850855660354356321041943 52276283490531534481562915)
            ·
              refine ⟨78414425235797301722344373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52276283490531534481562915 78414425235797301722344373)
              ·
                refine ⟨7351352365855997036469785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78414425235797301722344373 7351352365855997036469785)
                ·
                  refine ⟨5513514274391997777352339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7351352365855997036469785 5513514274391997777352339)
                  ·
                    refine ⟨8270271411587996666028509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5513514274391997777352339 8270271411587996666028509)
                    ·
                      refine ⟨3101351779345498749760691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8270271411587996666028509 3101351779345498749760691)
                      ·
                        rfl

theorem cell23_6039861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_6039861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039861 prefixEnd_6039861 := by exact prefixLift 6039861
  have htrace : WordTrace (prefixWord ++ tailWord_6039861) baseStart_6039861 baseEnd_6039861 := by
    simpa [prefixWord, tailWord_6039861, baseEnd_6039861] using wordTrace_append hprefix tailTrace_6039861
  have hstable : (prefixWord ++ tailWord_6039861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039861).length < 2 ^ (prefixWord ++ tailWord_6039861).sum := by decide
  have hdescent : baseEnd_6039861 < baseStart_6039861 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039871 : List Nat := [1, 1, 2, 2, 4, 1, 2, 4, 1, 3, 2]
def baseStart_6039871 : Nat := 118140960795 + 6039871 * 2 ^ 59
def prefixEnd_6039871 : Nat := 4983230072969 + 3 ^ 40 * 6039871 * 2
def baseEnd_6039871 : Nat := 3101356914152043710635645

theorem tailTrace_6039871 : CollatzResearch.WordTrace tailWord_6039871 prefixEnd_6039871 3101356914152043710635645 := by
  unfold tailWord_6039871
  simp only [CollatzResearch.WordTrace]
  refine ⟨220292193101586369687783467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146861462067724246458522311 220292193101586369687783467)
  ·
    refine ⟨330438289652379554531675201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220292193101586369687783467 330438289652379554531675201)
    ·
      refine ⟨247828717239284665898756401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330438289652379554531675201 247828717239284665898756401)
      ·
        refine ⟨185871537929463499424067301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247828717239284665898756401 185871537929463499424067301)
        ·
          refine ⟨34850913361774406142012619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185871537929463499424067301 34850913361774406142012619)
          ·
            refine ⟨52276370042661609213018929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34850913361774406142012619 52276370042661609213018929)
            ·
              refine ⟨39207277531996206909764197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52276370042661609213018929 39207277531996206909764197)
              ·
                refine ⟨7351364537249288795580787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39207277531996206909764197 7351364537249288795580787)
                ·
                  refine ⟨11027046805873933193371181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7351364537249288795580787 11027046805873933193371181)
                  ·
                    refine ⟨4135142552202724947514193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11027046805873933193371181 4135142552202724947514193)
                    ·
                      refine ⟨3101356914152043710635645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135142552202724947514193 3101356914152043710635645)
                      ·
                        rfl

theorem cell23_6039871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 1, 3, 2].length) (baseStart_6039871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039871 prefixEnd_6039871 := by exact prefixLift 6039871
  have htrace : WordTrace (prefixWord ++ tailWord_6039871) baseStart_6039871 baseEnd_6039871 := by
    simpa [prefixWord, tailWord_6039871, baseEnd_6039871] using wordTrace_append hprefix tailTrace_6039871
  have hstable : (prefixWord ++ tailWord_6039871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039871).length < 2 ^ (prefixWord ++ tailWord_6039871).sum := by decide
  have hdescent : baseEnd_6039871 < baseStart_6039871 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039887 : List Nat := [1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 3]
def baseStart_6039887 : Nat := 118140960795 + 6039887 * 2 ^ 59
def prefixEnd_6039887 : Nat := 4983230072969 + 3 ^ 40 * 6039887 * 2
def baseEnd_6039887 : Nat := 3101365129842515648035571

theorem tailTrace_6039887 : CollatzResearch.WordTrace tailWord_6039887 prefixEnd_6039887 3101365129842515648035571 := by
  unfold tailWord_6039887
  simp only [CollatzResearch.WordTrace]
  refine ⟨220292776669528404420365915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146861851113018936280243943 220292776669528404420365915)
  ·
    refine ⟨330439165004292606630548873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220292776669528404420365915 330439165004292606630548873)
    ·
      refine ⟨247829373753219454972911655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330439165004292606630548873 247829373753219454972911655)
      ·
        refine ⟨371744060629829182459367483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247829373753219454972911655 371744060629829182459367483)
        ·
          refine ⟨557616090944743773689051225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371744060629829182459367483 557616090944743773689051225)
          ·
            refine ⟨418212068208557830266788419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557616090944743773689051225 418212068208557830266788419)
            ·
              refine ⟨627318102312836745400182629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418212068208557830266788419 627318102312836745400182629)
              ·
                refine ⟨117622144183656889762534243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 627318102312836745400182629 117622144183656889762534243)
                ·
                  refine ⟨176433216275485334643801365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117622144183656889762534243 176433216275485334643801365)
                  ·
                    refine ⟨8270307012913375061428189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 176433216275485334643801365 8270307012913375061428189)
                    ·
                      refine ⟨3101365129842515648035571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8270307012913375061428189 3101365129842515648035571)
                      ·
                        rfl

theorem cell23_6039887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 3].length) (baseStart_6039887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039887 prefixEnd_6039887 := by exact prefixLift 6039887
  have htrace : WordTrace (prefixWord ++ tailWord_6039887) baseStart_6039887 baseEnd_6039887 := by
    simpa [prefixWord, tailWord_6039887, baseEnd_6039887] using wordTrace_append hprefix tailTrace_6039887
  have hstable : (prefixWord ++ tailWord_6039887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039887).length < 2 ^ (prefixWord ++ tailWord_6039887).sum := by decide
  have hdescent : baseEnd_6039887 < baseStart_6039887 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039888 : List Nat := [2, 1, 1, 1, 1, 6, 4, 1, 1, 3, 2]
def baseStart_6039888 : Nat := 118140960795 + 6039888 * 2 ^ 59
def prefixEnd_6039888 : Nat := 4983230072969 + 3 ^ 40 * 6039888 * 2
def baseEnd_6039888 : Nat := 3101365643323170144123067

theorem tailTrace_6039888 : CollatzResearch.WordTrace tailWord_6039888 prefixEnd_6039888 3101365643323170144123067 := by
  unfold tailWord_6039888
  simp only [CollatzResearch.WordTrace]
  refine ⟨110146406571262390795576159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146861875428349854394101545 110146406571262390795576159)
  ·
    refine ⟨165219609856893586193364239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110146406571262390795576159 165219609856893586193364239)
    ·
      refine ⟨247829414785340379290046359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165219609856893586193364239 247829414785340379290046359)
      ·
        refine ⟨371744122178010568935069539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247829414785340379290046359 371744122178010568935069539)
        ·
          refine ⟨557616183267015853402604309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371744122178010568935069539 557616183267015853402604309)
          ·
            refine ⟨26138258590641368128247077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 557616183267015853402604309 26138258590641368128247077)
            ·
              refine ⟨4900923485745256524046327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26138258590641368128247077 4900923485745256524046327)
              ·
                refine ⟨7351385228617884786069491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4900923485745256524046327 7351385228617884786069491)
                ·
                  refine ⟨11027077842926827179104237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7351385228617884786069491 11027077842926827179104237)
                  ·
                    refine ⟨4135154191097560192164089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11027077842926827179104237 4135154191097560192164089)
                    ·
                      refine ⟨3101365643323170144123067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135154191097560192164089 3101365643323170144123067)
                      ·
                        rfl

theorem cell23_6039888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 1, 3, 2].length) (baseStart_6039888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039888 prefixEnd_6039888 := by exact prefixLift 6039888
  have htrace : WordTrace (prefixWord ++ tailWord_6039888) baseStart_6039888 baseEnd_6039888 := by
    simpa [prefixWord, tailWord_6039888, baseEnd_6039888] using wordTrace_append hprefix tailTrace_6039888
  have hstable : (prefixWord ++ tailWord_6039888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039888).length < 2 ^ (prefixWord ++ tailWord_6039888).sum := by decide
  have hdescent : baseEnd_6039888 < baseStart_6039888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039938 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_6039938 : Nat := 118140960795 + 6039938 * 2 ^ 59
def prefixEnd_6039938 : Nat := 4983230072969 + 3 ^ 40 * 6039938 * 2
def baseEnd_6039938 : Nat := 3101391317355894948497837

theorem tailTrace_6039938 : CollatzResearch.WordTrace tailWord_6039938 prefixEnd_6039938 3101391317355894948497837 := by
  unfold tailWord_6039938
  simp only [CollatzResearch.WordTrace]
  refine ⟨55073659198085910032618117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146863091194895760086981645 55073659198085910032618117)
  ·
    refine ⟨10326311099641108131115897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55073659198085910032618117 10326311099641108131115897)
    ·
      refine ⟨7744733324730831098336923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10326311099641108131115897 7744733324730831098336923)
      ·
        refine ⟨11617099987096246647505385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7744733324730831098336923 11617099987096246647505385)
        ·
          refine ⟨8712824990322184985629039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11617099987096246647505385 8712824990322184985629039)
          ·
            refine ⟨13069237485483277478443559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8712824990322184985629039 13069237485483277478443559)
            ·
              refine ⟨19603856228224916217665339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13069237485483277478443559 19603856228224916217665339)
              ·
                refine ⟨29405784342337374326498009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19603856228224916217665339 29405784342337374326498009)
                ·
                  refine ⟨22054338256753030744873507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29405784342337374326498009 22054338256753030744873507)
                  ·
                    refine ⟨33081507385129546117310261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22054338256753030744873507 33081507385129546117310261)
                    ·
                      refine ⟨3101391317355894948497837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33081507385129546117310261 3101391317355894948497837)
                      ·
                        rfl

theorem cell23_6039938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_6039938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039938 prefixEnd_6039938 := by exact prefixLift 6039938
  have htrace : WordTrace (prefixWord ++ tailWord_6039938) baseStart_6039938 baseEnd_6039938 := by
    simpa [prefixWord, tailWord_6039938, baseEnd_6039938] using wordTrace_append hprefix tailTrace_6039938
  have hstable : (prefixWord ++ tailWord_6039938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039938).length < 2 ^ (prefixWord ++ tailWord_6039938).sum := by decide
  have hdescent : baseEnd_6039938 < baseStart_6039938 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039969 : List Nat := [1, 2, 3, 5, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6039969 : Nat := 118140960795 + 6039969 * 2 ^ 59
def prefixEnd_6039969 : Nat := 4983230072969 + 3 ^ 40 * 6039969 * 2
def baseEnd_6039969 : Nat := 3101407235256184327210195

theorem tailTrace_6039969 : CollatzResearch.WordTrace tailWord_6039969 prefixEnd_6039969 3101407235256184327210195 := by
  unfold tailWord_6039969
  simp only [CollatzResearch.WordTrace]
  refine ⟨220295767455231332424850961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146863844970154221616567307 220295767455231332424850961)
  ·
    refine ⟨165221825591423499318638221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220295767455231332424850961 165221825591423499318638221)
    ·
      refine ⟨61958184596783812244489333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165221825591423499318638221 61958184596783812244489333)
      ·
        refine ⟨5808579805948482397920875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 61958184596783812244489333 5808579805948482397920875)
        ·
          refine ⟨8712869708922723596881313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5808579805948482397920875 8712869708922723596881313)
          ·
            refine ⟨6534652281692042697660985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8712869708922723596881313 6534652281692042697660985)
            ·
              refine ⟨4900989211269032023245739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6534652281692042697660985 4900989211269032023245739)
              ·
                refine ⟨7351483816903548034868609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4900989211269032023245739 7351483816903548034868609)
                ·
                  refine ⟨5513612862677661026151457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7351483816903548034868609 5513612862677661026151457)
                  ·
                    refine ⟨4135209647008245769613593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5513612862677661026151457 4135209647008245769613593)
                    ·
                      refine ⟨3101407235256184327210195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135209647008245769613593 3101407235256184327210195)
                      ·
                        rfl

theorem cell23_6039969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6039969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039969 prefixEnd_6039969 := by exact prefixLift 6039969
  have htrace : WordTrace (prefixWord ++ tailWord_6039969) baseStart_6039969 baseEnd_6039969 := by
    simpa [prefixWord, tailWord_6039969, baseEnd_6039969] using wordTrace_append hprefix tailTrace_6039969
  have hstable : (prefixWord ++ tailWord_6039969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039969).length < 2 ^ (prefixWord ++ tailWord_6039969).sum := by decide
  have hdescent : baseEnd_6039969 < baseStart_6039969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039977 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 1, 5, 5]
def baseStart_6039977 : Nat := 118140960795 + 6039977 * 2 ^ 59
def prefixEnd_6039977 : Nat := 4983230072969 + 3 ^ 40 * 6039977 * 2
def baseEnd_6039977 : Nat := 3101411343101420295910157

theorem tailTrace_6039977 : CollatzResearch.WordTrace tailWord_6039977 prefixEnd_6039977 3101411343101420295910157 := by
  unfold tailWord_6039977
  simp only [CollatzResearch.WordTrace]
  refine ⟨220296059239202349791142185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146864039492801566527428123 220296059239202349791142185)
  ·
    refine ⟨165222044429401762343356639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220296059239202349791142185 165222044429401762343356639)
    ·
      refine ⟨247833066644102643515034959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165222044429401762343356639 247833066644102643515034959)
      ·
        refine ⟨371749599966153965272552439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247833066644102643515034959 371749599966153965272552439)
        ·
          refine ⟨557624399949230947908828659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371749599966153965272552439 557624399949230947908828659)
          ·
            refine ⟨836436599923846421863242989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557624399949230947908828659 836436599923846421863242989)
            ·
              refine ⟨313663724971442408198716121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 836436599923846421863242989 313663724971442408198716121)
              ·
                refine ⟨235247793728581806149037091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 313663724971442408198716121 235247793728581806149037091)
                ·
                  refine ⟨352871690592872709223555637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 235247793728581806149037091 352871690592872709223555637)
                  ·
                    refine ⟨33081720993081816489708341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 352871690592872709223555637 33081720993081816489708341)
                    ·
                      refine ⟨3101411343101420295910157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33081720993081816489708341 3101411343101420295910157)
                      ·
                        rfl

theorem cell23_6039977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 5, 5].length) (baseStart_6039977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039977 prefixEnd_6039977 := by exact prefixLift 6039977
  have htrace : WordTrace (prefixWord ++ tailWord_6039977) baseStart_6039977 baseEnd_6039977 := by
    simpa [prefixWord, tailWord_6039977, baseEnd_6039977] using wordTrace_append hprefix tailTrace_6039977
  have hstable : (prefixWord ++ tailWord_6039977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039977).length < 2 ^ (prefixWord ++ tailWord_6039977).sum := by decide
  have hdescent : baseEnd_6039977 < baseStart_6039977 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039987 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 6]
def baseStart_6039987 : Nat := 118140960795 + 6039987 * 2 ^ 59
def prefixEnd_6039987 : Nat := 4983230072969 + 3 ^ 40 * 6039987 * 2
def baseEnd_6039987 : Nat := 3101416477907965256785111

theorem tailTrace_6039987 : CollatzResearch.WordTrace tailWord_6039987 prefixEnd_6039987 3101416477907965256785111 := by
  unfold tailWord_6039987
  simp only [CollatzResearch.WordTrace]
  refine ⟨220296423969166121499006215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146864282646110747666004143 220296423969166121499006215)
  ·
    refine ⟨330444635953749182248509323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220296423969166121499006215 330444635953749182248509323)
    ·
      refine ⟨495666953930623773372763985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330444635953749182248509323 495666953930623773372763985)
      ·
        refine ⟨371750215447967830029572989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495666953930623773372763985 371750215447967830029572989)
        ·
          refine ⟨139406330792987936261089871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371750215447967830029572989 139406330792987936261089871)
          ·
            refine ⟨209109496189481904391634807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139406330792987936261089871 209109496189481904391634807)
            ·
              refine ⟨313664244284222856587452211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209109496189481904391634807 313664244284222856587452211)
              ·
                refine ⟨470496366426334284881178317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313664244284222856587452211 470496366426334284881178317)
                ·
                  refine ⟨176436137409875356830441869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 470496366426334284881178317 176436137409875356830441869)
                  ·
                    refine ⟨66163551528703258811415701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 176436137409875356830441869 66163551528703258811415701)
                    ·
                      refine ⟨3101416477907965256785111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66163551528703258811415701 3101416477907965256785111)
                      ·
                        rfl

theorem cell23_6039987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_6039987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039987 prefixEnd_6039987 := by exact prefixLift 6039987
  have htrace : WordTrace (prefixWord ++ tailWord_6039987) baseStart_6039987 baseEnd_6039987 := by
    simpa [prefixWord, tailWord_6039987, baseEnd_6039987] using wordTrace_append hprefix tailTrace_6039987
  have hstable : (prefixWord ++ tailWord_6039987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039987).length < 2 ^ (prefixWord ++ tailWord_6039987).sum := by decide
  have hdescent : baseEnd_6039987 < baseStart_6039987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039991 : List Nat := [1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 4]
def baseStart_6039991 : Nat := 118140960795 + 6039991 * 2 ^ 59
def prefixEnd_6039991 : Nat := 4983230072969 + 3 ^ 40 * 6039991 * 2
def baseEnd_6039991 : Nat := 3101418531830583241135093

theorem tailTrace_6039991 : CollatzResearch.WordTrace tailWord_6039991 prefixEnd_6039991 3101418531830583241135093 := by
  unfold tailWord_6039991
  simp only [CollatzResearch.WordTrace]
  refine ⟨220296569861151630182151827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146864379907434420121434551 220296569861151630182151827)
  ·
    refine ⟨330444854791727445273227741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220296569861151630182151827 330444854791727445273227741)
    ·
      refine ⟨123916820546897791977460403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330444854791727445273227741 123916820546897791977460403)
      ·
        refine ⟨185875230820346687966190605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123916820546897791977460403 185875230820346687966190605)
        ·
          refine ⟨69703211557630007987321477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185875230820346687966190605 69703211557630007987321477)
          ·
            refine ⟨13069352167055626497622777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69703211557630007987321477 13069352167055626497622777)
            ·
              refine ⟨9802014125291719873217083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13069352167055626497622777 9802014125291719873217083)
              ·
                refine ⟨14703021187937579809825625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9802014125291719873217083 14703021187937579809825625)
                ·
                  refine ⟨11027265890953184857369219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14703021187937579809825625 11027265890953184857369219)
                  ·
                    refine ⟨16540898836429777286053829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11027265890953184857369219 16540898836429777286053829)
                    ·
                      refine ⟨3101418531830583241135093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16540898836429777286053829 3101418531830583241135093)
                      ·
                        rfl

theorem cell23_6039991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_6039991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039991 prefixEnd_6039991 := by exact prefixLift 6039991
  have htrace : WordTrace (prefixWord ++ tailWord_6039991) baseStart_6039991 baseEnd_6039991 := by
    simpa [prefixWord, tailWord_6039991, baseEnd_6039991] using wordTrace_append hprefix tailTrace_6039991
  have hstable : (prefixWord ++ tailWord_6039991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039991).length < 2 ^ (prefixWord ++ tailWord_6039991).sum := by decide
  have hdescent : baseEnd_6039991 < baseStart_6039991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6039994 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3]
def baseStart_6039994 : Nat := 118140960795 + 6039994 * 2 ^ 59
def prefixEnd_6039994 : Nat := 4983230072969 + 3 ^ 40 * 6039994 * 2
def baseEnd_6039994 : Nat := 3101420072272546729397579

theorem tailTrace_6039994 : CollatzResearch.WordTrace tailWord_6039994 prefixEnd_6039994 3101420072272546729397579 := by
  unfold tailWord_6039994
  simp only [CollatzResearch.WordTrace]
  refine ⟨55074169820035190423627759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146864452853427174463007357 55074169820035190423627759)
  ·
    refine ⟨82611254730052785635441639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55074169820035190423627759 82611254730052785635441639)
    ·
      refine ⟨123916882095079178453162459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82611254730052785635441639 123916882095079178453162459)
      ·
        refine ⟨185875323142618767679743689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123916882095079178453162459 185875323142618767679743689)
        ·
          refine ⟨139406492356964075759807767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185875323142618767679743689 139406492356964075759807767)
          ·
            refine ⟨209109738535446113639711651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139406492356964075759807767 209109738535446113639711651)
            ·
              refine ⟨313664607803169170459567477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209109738535446113639711651 313664607803169170459567477)
              ·
                refine ⟨29406056981547109730584451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 313664607803169170459567477 29406056981547109730584451)
                ·
                  refine ⟨44109085472320664595876677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29406056981547109730584451 44109085472320664595876677)
                  ·
                    refine ⟨8270453526060124611726877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44109085472320664595876677 8270453526060124611726877)
                    ·
                      refine ⟨3101420072272546729397579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8270453526060124611726877 3101420072272546729397579)
                      ·
                        rfl

theorem cell23_6039994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 1, 4, 3].length) (baseStart_6039994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6039994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6039994 prefixEnd_6039994 := by exact prefixLift 6039994
  have htrace : WordTrace (prefixWord ++ tailWord_6039994) baseStart_6039994 baseEnd_6039994 := by
    simpa [prefixWord, tailWord_6039994, baseEnd_6039994] using wordTrace_append hprefix tailTrace_6039994
  have hstable : (prefixWord ++ tailWord_6039994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6039994).length < 2 ^ (prefixWord ++ tailWord_6039994).sum := by decide
  have hdescent : baseEnd_6039994 < baseStart_6039994 := by decide
  rcases family_descends (prefixWord ++ tailWord_6039994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040024 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 2, 5, 3]
def baseStart_6040024 : Nat := 118140960795 + 6040024 * 2 ^ 59
def prefixEnd_6040024 : Nat := 4983230072969 + 3 ^ 40 * 6040024 * 2
def baseEnd_6040024 : Nat := 3101435476692181612022441

theorem tailTrace_6040024 : CollatzResearch.WordTrace tailWord_6040024 prefixEnd_6040024 3101435476692181612022441 := by
  unfold tailWord_6040024
  simp only [CollatzResearch.WordTrace]
  refine ⟨110148886735016038409051563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146865182313354717878735417 110148886735016038409051563)
  ·
    refine ⟨165223330102524057613577345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110148886735016038409051563 165223330102524057613577345)
    ·
      refine ⟨123917497576893043210183009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165223330102524057613577345 123917497576893043210183009)
      ·
        refine ⟨92938123182669782407637257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123917497576893043210183009 92938123182669782407637257)
        ·
          refine ⟨69703592387002336805727943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92938123182669782407637257 69703592387002336805727943)
          ·
            refine ⟨104555388580503505208591915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69703592387002336805727943 104555388580503505208591915)
            ·
              refine ⟨156833082870755257812887873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104555388580503505208591915 156833082870755257812887873)
              ·
                refine ⟨117624812153066443359665905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156833082870755257812887873 117624812153066443359665905)
                ·
                  refine ⟨88218609114799832519749429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117624812153066443359665905 88218609114799832519749429)
                  ·
                    refine ⟨8270494604512484298726509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88218609114799832519749429 8270494604512484298726509)
                    ·
                      refine ⟨3101435476692181612022441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8270494604512484298726509 3101435476692181612022441)
                      ·
                        rfl

theorem cell23_6040024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_6040024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040024 prefixEnd_6040024 := by exact prefixLift 6040024
  have htrace : WordTrace (prefixWord ++ tailWord_6040024) baseStart_6040024 baseEnd_6040024 := by
    simpa [prefixWord, tailWord_6040024, baseEnd_6040024] using wordTrace_append hprefix tailTrace_6040024
  have hstable : (prefixWord ++ tailWord_6040024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040024).length < 2 ^ (prefixWord ++ tailWord_6040024).sum := by decide
  have hdescent : baseEnd_6040024 < baseStart_6040024 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040044 : List Nat := [2, 2, 1, 1, 2, 1, 3, 3, 3, 5]
def baseStart_6040044 : Nat := 118140960795 + 6040044 * 2 ^ 59
def prefixEnd_6040044 : Nat := 4983230072969 + 3 ^ 40 * 6040044 * 2
def baseEnd_6040044 : Nat := 1033815248768423844590783

theorem tailTrace_6040044 : CollatzResearch.WordTrace tailWord_6040044 prefixEnd_6040044 1033815248768423844590783 := by
  unfold tailWord_6040044
  simp only [CollatzResearch.WordTrace]
  refine ⟨110149251464979810116915593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146865668619973080155887457 110149251464979810116915593)
  ·
    refine ⟨82611938598734857587686695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110149251464979810116915593 82611938598734857587686695)
    ·
      refine ⟨123917907898102286381530043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82611938598734857587686695 123917907898102286381530043)
      ·
        refine ⟨185876861847153429572295065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123917907898102286381530043 185876861847153429572295065)
        ·
          refine ⟨139407646385365072179221299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185876861847153429572295065 139407646385365072179221299)
          ·
            refine ⟨209111469578047608268831949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139407646385365072179221299 209111469578047608268831949)
            ·
              refine ⟨78416801091767853100811981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209111469578047608268831949 78416801091767853100811981)
              ·
                refine ⟨29406300409412944912804493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78416801091767853100811981 29406300409412944912804493)
                ·
                  refine ⟨11027362653529854342301685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29406300409412944912804493 11027362653529854342301685)
                  ·
                    refine ⟨1033815248768423844590783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11027362653529854342301685 1033815248768423844590783)
                    ·
                      rfl

theorem cell23_6040044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_6040044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040044 prefixEnd_6040044 := by exact prefixLift 6040044
  have htrace : WordTrace (prefixWord ++ tailWord_6040044) baseStart_6040044 baseEnd_6040044 := by
    simpa [prefixWord, tailWord_6040044, baseEnd_6040044] using wordTrace_append hprefix tailTrace_6040044
  have hstable : (prefixWord ++ tailWord_6040044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040044).length < 2 ^ (prefixWord ++ tailWord_6040044).sum := by decide
  have hdescent : baseEnd_6040044 < baseStart_6040044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040045 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 2, 2, 3]
def baseStart_6040045 : Nat := 118140960795 + 6040045 * 2 ^ 59
def prefixEnd_6040045 : Nat := 4983230072969 + 3 ^ 40 * 6040045 * 2
def baseEnd_6040045 : Nat := 3101446259785926029859845

theorem tailTrace_6040045 : CollatzResearch.WordTrace tailWord_6040045 prefixEnd_6040045 3101446259785926029859845 := by
  unfold tailWord_6040045
  simp only [CollatzResearch.WordTrace]
  refine ⟨220298539402955997404617589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146865692935303998269745059 220298539402955997404617589)
  ·
    refine ⟨20652988069027124756682899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220298539402955997404617589 20652988069027124756682899)
    ·
      refine ⟨30979482103540687135024349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20652988069027124756682899 30979482103540687135024349)
      ·
        refine ⟨11617305788827757675634131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30979482103540687135024349 11617305788827757675634131)
        ·
          refine ⟨17425958683241636513451197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11617305788827757675634131 17425958683241636513451197)
          ·
            refine ⟨6534734506215613692544199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17425958683241636513451197 6534734506215613692544199)
            ·
              refine ⟨9802101759323420538816299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6534734506215613692544199 9802101759323420538816299)
              ·
                refine ⟨14703152638985130808224449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9802101759323420538816299 14703152638985130808224449)
                ·
                  refine ⟨11027364479238848106168337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14703152638985130808224449 11027364479238848106168337)
                  ·
                    refine ⟨8270523359429136079626253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11027364479238848106168337 8270523359429136079626253)
                    ·
                      refine ⟨3101446259785926029859845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8270523359429136079626253 3101446259785926029859845)
                      ·
                        rfl

theorem cell23_6040045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_6040045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040045 prefixEnd_6040045 := by exact prefixLift 6040045
  have htrace : WordTrace (prefixWord ++ tailWord_6040045) baseStart_6040045 baseEnd_6040045 := by
    simpa [prefixWord, tailWord_6040045, baseEnd_6040045] using wordTrace_append hprefix tailTrace_6040045
  have hstable : (prefixWord ++ tailWord_6040045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040045).length < 2 ^ (prefixWord ++ tailWord_6040045).sum := by decide
  have hdescent : baseEnd_6040045 < baseStart_6040045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040051 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 1, 5, 2]
def baseStart_6040051 : Nat := 118140960795 + 6040051 * 2 ^ 59
def prefixEnd_6040051 : Nat := 4983230072969 + 3 ^ 40 * 6040051 * 2
def baseEnd_6040051 : Nat := 3101449340669853006384817

theorem tailTrace_6040051 : CollatzResearch.WordTrace tailWord_6040051 prefixEnd_6040051 3101449340669853006384817 := by
  unfold tailWord_6040051
  simp only [CollatzResearch.WordTrace]
  refine ⟨220298758240934260429336007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146865838827289506952890671 220298758240934260429336007)
  ·
    refine ⟨330448137361401390644004011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220298758240934260429336007 330448137361401390644004011)
    ·
      refine ⟨495672206042102085966006017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330448137361401390644004011 495672206042102085966006017)
      ·
        refine ⟨371754154531576564474504513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495672206042102085966006017 371754154531576564474504513)
        ·
          refine ⟨278815615898682423355878385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371754154531576564474504513 278815615898682423355878385)
          ·
            refine ⟨209111711924011817516908789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278815615898682423355878385 209111711924011817516908789)
            ·
              refine ⟨19604222992876107892210199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 209111711924011817516908789 19604222992876107892210199)
              ·
                refine ⟨29406334489314161838315299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19604222992876107892210199 29406334489314161838315299)
                ·
                  refine ⟨44109501733971242757472949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29406334489314161838315299 44109501733971242757472949)
                  ·
                    refine ⟨4135265787559804008513089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44109501733971242757472949 4135265787559804008513089)
                    ·
                      refine ⟨3101449340669853006384817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135265787559804008513089 3101449340669853006384817)
                      ·
                        rfl

theorem cell23_6040051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 5, 2].length) (baseStart_6040051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040051 prefixEnd_6040051 := by exact prefixLift 6040051
  have htrace : WordTrace (prefixWord ++ tailWord_6040051) baseStart_6040051 baseEnd_6040051 := by
    simpa [prefixWord, tailWord_6040051, baseEnd_6040051] using wordTrace_append hprefix tailTrace_6040051
  have hstable : (prefixWord ++ tailWord_6040051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040051).length < 2 ^ (prefixWord ++ tailWord_6040051).sum := by decide
  have hdescent : baseEnd_6040051 < baseStart_6040051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040061 : List Nat := [1, 4, 1, 1, 1, 3, 3, 3, 1, 5]
def baseStart_6040061 : Nat := 118140960795 + 6040061 * 2 ^ 59
def prefixEnd_6040061 : Nat := 4983230072969 + 3 ^ 40 * 6040061 * 2
def baseEnd_6040061 : Nat := 1033818158492132655753257

theorem tailTrace_6040061 : CollatzResearch.WordTrace tailWord_6040061 prefixEnd_6040061 1033818158492132655753257 := by
  unfold tailWord_6040061
  simp only [CollatzResearch.WordTrace]
  refine ⟨220299122970898032137200037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146866081980598688091466691 220299122970898032137200037)
  ·
    refine ⟨41306085557043381025725007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220299122970898032137200037 41306085557043381025725007)
    ·
      refine ⟨61959128335565071538587511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41306085557043381025725007 61959128335565071538587511)
      ·
        refine ⟨92938692503347607307881267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61959128335565071538587511 92938692503347607307881267)
        ·
          refine ⟨139408038755021410961821901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92938692503347607307881267 139408038755021410961821901)
          ·
            refine ⟨52278014533133029110683213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139408038755021410961821901 52278014533133029110683213)
            ·
              refine ⟨19604255449924885916506205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52278014533133029110683213 19604255449924885916506205)
              ·
                refine ⟨7351595793721832218689827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19604255449924885916506205 7351595793721832218689827)
                ·
                  refine ⟨11027393690582748328034741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7351595793721832218689827 11027393690582748328034741)
                  ·
                    refine ⟨1033818158492132655753257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11027393690582748328034741 1033818158492132655753257)
                    ·
                      rfl

theorem cell23_6040061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_6040061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040061 prefixEnd_6040061 := by exact prefixLift 6040061
  have htrace : WordTrace (prefixWord ++ tailWord_6040061) baseStart_6040061 baseEnd_6040061 := by
    simpa [prefixWord, tailWord_6040061, baseEnd_6040061] using wordTrace_append hprefix tailTrace_6040061
  have hstable : (prefixWord ++ tailWord_6040061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040061).length < 2 ^ (prefixWord ++ tailWord_6040061).sum := by decide
  have hdescent : baseEnd_6040061 < baseStart_6040061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040075 : List Nat := [1, 1, 1, 1, 7, 1, 2, 4, 1, 1, 3]
def baseStart_6040075 : Nat := 118140960795 + 6040075 * 2 ^ 59
def prefixEnd_6040075 : Nat := 4983230072969 + 3 ^ 40 * 6040075 * 2
def baseEnd_6040075 : Nat := 3101461664205560912484707

theorem tailTrace_6040075 : CollatzResearch.WordTrace tailWord_6040075 prefixEnd_6040075 3101461664205560912484707 := by
  unfold tailWord_6040075
  simp only [CollatzResearch.WordTrace]
  refine ⟨220299633592847312528209679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146866422395231541685473119 220299633592847312528209679)
  ·
    refine ⟨330449450389270968792314519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220299633592847312528209679 330449450389270968792314519)
    ·
      refine ⟨495674175583906453188471779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330449450389270968792314519 495674175583906453188471779)
      ·
        refine ⟨743511263375859679782707669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495674175583906453188471779 743511263375859679782707669)
        ·
          refine ⟨17426045235371711244907211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 743511263375859679782707669 17426045235371711244907211)
          ·
            refine ⟨26139067853057566867360817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17426045235371711244907211 26139067853057566867360817)
            ·
              refine ⟨19604300889793175150520613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26139067853057566867360817 19604300889793175150520613)
              ·
                refine ⟨3675806416836220340722615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19604300889793175150520613 3675806416836220340722615)
                ·
                  refine ⟨5513709625254330511083923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675806416836220340722615 5513709625254330511083923)
                  ·
                    refine ⟨8270564437881495766625885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5513709625254330511083923 8270564437881495766625885)
                    ·
                      refine ⟨3101461664205560912484707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8270564437881495766625885 3101461664205560912484707)
                      ·
                        rfl

theorem cell23_6040075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 4, 1, 1, 3].length) (baseStart_6040075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040075 prefixEnd_6040075 := by exact prefixLift 6040075
  have htrace : WordTrace (prefixWord ++ tailWord_6040075) baseStart_6040075 baseEnd_6040075 := by
    simpa [prefixWord, tailWord_6040075, baseEnd_6040075] using wordTrace_append hprefix tailTrace_6040075
  have hstable : (prefixWord ++ tailWord_6040075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040075).length < 2 ^ (prefixWord ++ tailWord_6040075).sum := by decide
  have hdescent : baseEnd_6040075 < baseStart_6040075 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040101 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 3, 2, 3]
def baseStart_6040101 : Nat := 118140960795 + 6040101 * 2 ^ 59
def prefixEnd_6040101 : Nat := 4983230072969 + 3 ^ 40 * 6040101 * 2
def baseEnd_6040101 : Nat := 3101475014702577810759587

theorem tailTrace_6040101 : CollatzResearch.WordTrace tailWord_6040101 prefixEnd_6040101 3101475014702577810759587 := by
  unfold tailWord_6040101
  simp only [CollatzResearch.WordTrace]
  refine ⟨220300581890753118968656157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146867054593835412645770771 220300581890753118968656157)
  ·
    refine ⟨82612718209032419613246059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220300581890753118968656157 82612718209032419613246059)
    ·
      refine ⟨123919077313548629419869089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82612718209032419613246059 123919077313548629419869089)
      ·
        refine ⟨92939307985161472064901817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123919077313548629419869089 92939307985161472064901817)
        ·
          refine ⟨69704480988871104048676363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92939307985161472064901817 69704480988871104048676363)
          ·
            refine ⟨104556721483306656073014545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69704480988871104048676363 104556721483306656073014545)
            ·
              refine ⟨78417541112479992054760909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104556721483306656073014545 78417541112479992054760909)
              ·
                refine ⟨29406577917179997020535341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78417541112479992054760909 29406577917179997020535341)
                ·
                  refine ⟨11027466718942498882700753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29406577917179997020535341 11027466718942498882700753)
                  ·
                    refine ⟨8270600039206874162025565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11027466718942498882700753 8270600039206874162025565)
                    ·
                      refine ⟨3101475014702577810759587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8270600039206874162025565 3101475014702577810759587)
                      ·
                        rfl

theorem cell23_6040101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_6040101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040101 prefixEnd_6040101 := by exact prefixLift 6040101
  have htrace : WordTrace (prefixWord ++ tailWord_6040101) baseStart_6040101 baseEnd_6040101 := by
    simpa [prefixWord, tailWord_6040101, baseEnd_6040101] using wordTrace_append hprefix tailTrace_6040101
  have hstable : (prefixWord ++ tailWord_6040101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040101).length < 2 ^ (prefixWord ++ tailWord_6040101).sum := by decide
  have hdescent : baseEnd_6040101 < baseStart_6040101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040118 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_6040118 : Nat := 118140960795 + 6040118 * 2 ^ 59
def prefixEnd_6040118 : Nat := 4983230072969 + 3 ^ 40 * 6040118 * 2
def baseEnd_6040118 : Nat := 3101483743873704244247009

theorem tailTrace_6040118 : CollatzResearch.WordTrace tailWord_6040118 prefixEnd_6040118 3101483743873704244247009 := by
  unfold tailWord_6040118
  simp only [CollatzResearch.WordTrace]
  refine ⟨13768825120730720679501563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146867467954461020581350005 13768825120730720679501563)
  ·
    refine ⟨20653237681096081019252345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13768825120730720679501563 20653237681096081019252345)
    ·
      refine ⟨15489928260822060764439259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20653237681096081019252345 15489928260822060764439259)
      ·
        refine ⟨23234892391233091146658889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15489928260822060764439259 23234892391233091146658889)
        ·
          refine ⟨17426169293424818359994167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23234892391233091146658889 17426169293424818359994167)
          ·
            refine ⟨26139253940137227539991251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17426169293424818359994167 26139253940137227539991251)
            ·
              refine ⟨39208880910205841309986877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26139253940137227539991251 39208880910205841309986877)
              ·
                refine ⟨14703330341327190491245079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39208880910205841309986877 14703330341327190491245079)
                ·
                  refine ⟨22054995511990785736867619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14703330341327190491245079 22054995511990785736867619)
                  ·
                    refine ⟨33082493267986178605301429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22054995511990785736867619 33082493267986178605301429)
                    ·
                      refine ⟨3101483743873704244247009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33082493267986178605301429 3101483743873704244247009)
                      ·
                        rfl

theorem cell23_6040118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_6040118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040118 prefixEnd_6040118 := by exact prefixLift 6040118
  have htrace : WordTrace (prefixWord ++ tailWord_6040118) baseStart_6040118 baseEnd_6040118 := by
    simpa [prefixWord, tailWord_6040118, baseEnd_6040118] using wordTrace_append hprefix tailTrace_6040118
  have hstable : (prefixWord ++ tailWord_6040118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040118).length < 2 ^ (prefixWord ++ tailWord_6040118).sum := by decide
  have hdescent : baseEnd_6040118 < baseStart_6040118 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040126 : List Nat := [4, 2, 1, 4, 1, 1, 3, 2, 1, 1, 3]
def baseStart_6040126 : Nat := 118140960795 + 6040126 * 2 ^ 59
def prefixEnd_6040126 : Nat := 4983230072969 + 3 ^ 40 * 6040126 * 2
def baseEnd_6040126 : Nat := 3101487851718940212946973

theorem tailTrace_6040126 : CollatzResearch.WordTrace tailWord_6040126 prefixEnd_6040126 3101487851718940212946973 := by
  unfold tailWord_6040126
  simp only [CollatzResearch.WordTrace]
  refine ⟨27537686714457818529789529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146867662477108365492210821 27537686714457818529789529)
  ·
    refine ⟨20653265035843363897342147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27537686714457818529789529 20653265035843363897342147)
    ·
      refine ⟨30979897553765045846013221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20653265035843363897342147 30979897553765045846013221)
      ·
        refine ⟨5808730791330946096127479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30979897553765045846013221 5808730791330946096127479)
        ·
          refine ⟨8713096186996419144191219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5808730791330946096127479 8713096186996419144191219)
          ·
            refine ⟨13069644280494628716286829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8713096186996419144191219 13069644280494628716286829)
            ·
              refine ⟨4901116605185485768607561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13069644280494628716286829 4901116605185485768607561)
              ·
                refine ⟨3675837453889114326455671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4901116605185485768607561 3675837453889114326455671)
                ·
                  refine ⟨5513756180833671489683507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675837453889114326455671 5513756180833671489683507)
                  ·
                    refine ⟨8270634271250507234525261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5513756180833671489683507 8270634271250507234525261)
                    ·
                      refine ⟨3101487851718940212946973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8270634271250507234525261 3101487851718940212946973)
                      ·
                        rfl

theorem cell23_6040126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_6040126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040126 prefixEnd_6040126 := by exact prefixLift 6040126
  have htrace : WordTrace (prefixWord ++ tailWord_6040126) baseStart_6040126 baseEnd_6040126 := by
    simpa [prefixWord, tailWord_6040126, baseEnd_6040126] using wordTrace_append hprefix tailTrace_6040126
  have hstable : (prefixWord ++ tailWord_6040126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040126).length < 2 ^ (prefixWord ++ tailWord_6040126).sum := by decide
  have hdescent : baseEnd_6040126 < baseStart_6040126 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040144 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 5]
def baseStart_6040144 : Nat := 118140960795 + 6040144 * 2 ^ 59
def prefixEnd_6040144 : Nat := 4983230072969 + 3 ^ 40 * 6040144 * 2
def baseEnd_6040144 : Nat := 3101497094370721142521889

theorem tailTrace_6040144 : CollatzResearch.WordTrace tailWord_6040144 prefixEnd_6040144 3101497094370721142521889 := by
  unfold tailWord_6040144
  simp only [CollatzResearch.WordTrace]
  refine ⟨110151075114798668656235743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146868100153064891541647657 110151075114798668656235743)
  ·
    refine ⟨165226612672198002984353615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110151075114798668656235743 165226612672198002984353615)
    ·
      refine ⟨247839919008297004476530423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165226612672198002984353615 247839919008297004476530423)
      ·
        refine ⟨371759878512445506714795635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247839919008297004476530423 371759878512445506714795635)
        ·
          refine ⟨557639817768668260072193453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371759878512445506714795635 557639817768668260072193453)
          ·
            refine ⟨209114931663250597527072545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 557639817768668260072193453 209114931663250597527072545)
            ·
              refine ⟨156836198747437948145304409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209114931663250597527072545 156836198747437948145304409)
              ·
                refine ⟨117627149060578461108978307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156836198747437948145304409 117627149060578461108978307)
                ·
                  refine ⟨176440723590867691663467461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117627149060578461108978307 176440723590867691663467461)
                  ·
                    refine ⟨33082635673287692186900149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 176440723590867691663467461 33082635673287692186900149)
                    ·
                      refine ⟨3101497094370721142521889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33082635673287692186900149 3101497094370721142521889)
                      ·
                        rfl

theorem cell23_6040144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 5].length) (baseStart_6040144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040144 prefixEnd_6040144 := by exact prefixLift 6040144
  have htrace : WordTrace (prefixWord ++ tailWord_6040144) baseStart_6040144 baseEnd_6040144 := by
    simpa [prefixWord, tailWord_6040144, baseEnd_6040144] using wordTrace_append hprefix tailTrace_6040144
  have hstable : (prefixWord ++ tailWord_6040144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040144).length < 2 ^ (prefixWord ++ tailWord_6040144).sum := by decide
  have hdescent : baseEnd_6040144 < baseStart_6040144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040154 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10]
def baseStart_6040154 : Nat := 118140960795 + 6040154 * 2 ^ 59
def prefixEnd_6040154 : Nat := 4983230072969 + 3 ^ 40 * 6040154 * 2
def baseEnd_6040154 : Nat := 3101502229177266103396843

theorem tailTrace_6040154 : CollatzResearch.WordTrace tailWord_6040154 prefixEnd_6040154 3101502229177266103396843 := by
  unfold tailWord_6040154
  simp only [CollatzResearch.WordTrace]
  refine ⟨55075628739890277255083879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146868343306374072680223677 55075628739890277255083879)
  ·
    refine ⟨82613443109835415882625819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55075628739890277255083879 82613443109835415882625819)
    ·
      refine ⟨123920164664753123823938729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82613443109835415882625819 123920164664753123823938729)
      ·
        refine ⟨92940123498564842867954047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123920164664753123823938729 92940123498564842867954047)
        ·
          refine ⟨139410185247847264301931071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92940123498564842867954047 139410185247847264301931071)
          ·
            refine ⟨209115277871770896452896607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139410185247847264301931071 209115277871770896452896607)
            ·
              refine ⟨313672916807656344679344911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209115277871770896452896607 313672916807656344679344911)
              ·
                refine ⟨470509375211484517019017367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313672916807656344679344911 470509375211484517019017367)
                ·
                  refine ⟨705764062817226775528526051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470509375211484517019017367 705764062817226775528526051)
                  ·
                    refine ⟨1058646094225840163292789077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 705764062817226775528526051 1058646094225840163292789077)
                    ·
                      refine ⟨3101502229177266103396843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1058646094225840163292789077 3101502229177266103396843)
                      ·
                        rfl

theorem cell23_6040154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_6040154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040154 prefixEnd_6040154 := by exact prefixLift 6040154
  have htrace : WordTrace (prefixWord ++ tailWord_6040154) baseStart_6040154 baseEnd_6040154 := by
    simpa [prefixWord, tailWord_6040154, baseEnd_6040154] using wordTrace_append hprefix tailTrace_6040154
  have hstable : (prefixWord ++ tailWord_6040154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040154).length < 2 ^ (prefixWord ++ tailWord_6040154).sum := by decide
  have hdescent : baseEnd_6040154 < baseStart_6040154 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040222 : List Nat := [4, 3, 1, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_6040222 : Nat := 118140960795 + 6040222 * 2 ^ 59
def prefixEnd_6040222 : Nat := 4983230072969 + 3 ^ 40 * 6040222 * 2
def baseEnd_6040222 : Nat := 3101537145861771837346531

theorem tailTrace_6040222 : CollatzResearch.WordTrace tailWord_6040222 prefixEnd_6040222 3101537145861771837346531 := by
  unfold tailWord_6040222
  simp only [CollatzResearch.WordTrace]
  refine ⟨27538124390414344579226365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146869996748876504422540613 27538124390414344579226365)
  ·
    refine ⟨10326796646405379217209887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27538124390414344579226365 10326796646405379217209887)
    ·
      refine ⟨15490194969608068825814831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10326796646405379217209887 15490194969608068825814831)
      ·
        refine ⟨23235292454412103238722247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15490194969608068825814831 23235292454412103238722247)
        ·
          refine ⟨34852938681618154858083371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23235292454412103238722247 34852938681618154858083371)
          ·
            refine ⟨52279408022427232287125057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34852938681618154858083371 52279408022427232287125057)
            ·
              refine ⟨39209556016820424215343793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52279408022427232287125057 39209556016820424215343793)
              ·
                refine ⟨29407167012615318161507845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39209556016820424215343793 29407167012615318161507845)
                ·
                  refine ⟨5513843814865372155282721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29407167012615318161507845 5513843814865372155282721)
                  ·
                    refine ⟨4135382861149029116462041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5513843814865372155282721 4135382861149029116462041)
                    ·
                      refine ⟨3101537145861771837346531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135382861149029116462041 3101537145861771837346531)
                      ·
                        rfl

theorem cell23_6040222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_6040222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040222 prefixEnd_6040222 := by exact prefixLift 6040222
  have htrace : WordTrace (prefixWord ++ tailWord_6040222) baseStart_6040222 baseEnd_6040222 := by
    simpa [prefixWord, tailWord_6040222, baseEnd_6040222] using wordTrace_append hprefix tailTrace_6040222
  have hstable : (prefixWord ++ tailWord_6040222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040222).length < 2 ^ (prefixWord ++ tailWord_6040222).sum := by decide
  have hdescent : baseEnd_6040222 < baseStart_6040222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040245 : List Nat := [1, 3, 3, 3, 1, 1, 2, 4, 5]
def baseStart_6040245 : Nat := 118140960795 + 6040245 * 2 ^ 59
def prefixEnd_6040245 : Nat := 4983230072969 + 3 ^ 40 * 6040245 * 2
def baseEnd_6040245 : Nat := 344616550657425027484325

theorem tailTrace_6040245 : CollatzResearch.WordTrace tailWord_6040245 prefixEnd_6040245 344616550657425027484325 := by
  unfold tailWord_6040245
  simp only [CollatzResearch.WordTrace]
  refine ⟨220305834002231431561898189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146870556001487621041265459 220305834002231431561898189)
  ·
    refine ⟨82614687750836786835711821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220305834002231431561898189 82614687750836786835711821)
    ·
      refine ⟨30980507906563795063391933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82614687750836786835711821 30980507906563795063391933)
      ·
        refine ⟨11617690464961423148771975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30980507906563795063391933 11617690464961423148771975)
        ·
          refine ⟨17426535697442134723157963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11617690464961423148771975 17426535697442134723157963)
          ·
            refine ⟨26139803546163202084736945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17426535697442134723157963 26139803546163202084736945)
            ·
              refine ⟨19604852659622401563552709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26139803546163202084736945 19604852659622401563552709)
              ·
                refine ⟨3675909873679200293166133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19604852659622401563552709 3675909873679200293166133)
                ·
                  refine ⟨344616550657425027484325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3675909873679200293166133 344616550657425027484325)
                  ·
                    rfl

theorem cell23_6040245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 5].length) (baseStart_6040245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040245 prefixEnd_6040245 := by exact prefixLift 6040245
  have htrace : WordTrace (prefixWord ++ tailWord_6040245) baseStart_6040245 baseEnd_6040245 := by
    simpa [prefixWord, tailWord_6040245, baseEnd_6040245] using wordTrace_append hprefix tailTrace_6040245
  have hstable : (prefixWord ++ tailWord_6040245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040245).length < 2 ^ (prefixWord ++ tailWord_6040245).sum := by decide
  have hdescent : baseEnd_6040245 < baseStart_6040245 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040356 : List Nat := [2, 3, 1, 3, 3, 2, 2, 2, 1, 4]
def baseStart_6040356 : Nat := 118140960795 + 6040356 * 2 ^ 59
def prefixEnd_6040356 : Nat := 4983230072969 + 3 ^ 40 * 6040356 * 2
def baseEnd_6040356 : Nat := 1033868650756491437690305

theorem tailTrace_6040356 : CollatzResearch.WordTrace tailWord_6040356 prefixEnd_6040356 1033868650756491437690305 := by
  unfold tailWord_6040356
  simp only [CollatzResearch.WordTrace]
  refine ⟨110154941252414648759594461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146873255003219531679459281 110154941252414648759594461)
  ·
    refine ⟨41308102969655493284847923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110154941252414648759594461 41308102969655493284847923)
    ·
      refine ⟨61962154454483239927271885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41308102969655493284847923 61962154454483239927271885)
      ·
        refine ⟨23235807920431214972726957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61962154454483239927271885 23235807920431214972726957)
        ·
          refine ⟨8713427970161705614772609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23235807920431214972726957 8713427970161705614772609)
          ·
            refine ⟨6535070977621279211079457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8713427970161705614772609 6535070977621279211079457)
            ·
              refine ⟨4901303233215959408309593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6535070977621279211079457 4901303233215959408309593)
              ·
                refine ⟨3675977424911969556232195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4901303233215959408309593 3675977424911969556232195)
                ·
                  refine ⟨5513966137367954334348293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3675977424911969556232195 5513966137367954334348293)
                  ·
                    refine ⟨1033868650756491437690305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5513966137367954334348293 1033868650756491437690305)
                    ·
                      rfl

theorem cell23_6040356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_6040356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040356 prefixEnd_6040356 := by exact prefixLift 6040356
  have htrace : WordTrace (prefixWord ++ tailWord_6040356) baseStart_6040356 baseEnd_6040356 := by
    simpa [prefixWord, tailWord_6040356, baseEnd_6040356] using wordTrace_append hprefix tailTrace_6040356
  have hstable : (prefixWord ++ tailWord_6040356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040356).length < 2 ^ (prefixWord ++ tailWord_6040356).sum := by decide
  have hdescent : baseEnd_6040356 < baseStart_6040356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040402 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2]
def baseStart_6040402 : Nat := 118140960795 + 6040402 * 2 ^ 59
def prefixEnd_6040402 : Nat := 4983230072969 + 3 ^ 40 * 6040402 * 2
def baseEnd_6040402 : Nat := 3101629572379581133095703

theorem tailTrace_6040402 : CollatzResearch.WordTrace tailWord_6040402 prefixEnd_6040402 3101629572379581133095703 := by
  unfold tailWord_6040402
  simp only [CollatzResearch.WordTrace]
  refine ⟨55077890065665661843840865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146874373508441764916908973 55077890065665661843840865)
  ·
    refine ⟨41308417549249246382880649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55077890065665661843840865 41308417549249246382880649)
    ·
      refine ⟨30981313161936934787160487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41308417549249246382880649 30981313161936934787160487)
      ·
        refine ⟨46471969742905402180740731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30981313161936934787160487 46471969742905402180740731)
        ·
          refine ⟨69707954614358103271111097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46471969742905402180740731 69707954614358103271111097)
          ·
            refine ⟨52280965960768577453333323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69707954614358103271111097 52280965960768577453333323)
            ·
              refine ⟨78421448941152866179999985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52280965960768577453333323 78421448941152866179999985)
              ·
                refine ⟨58816086705864649634999989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78421448941152866179999985 58816086705864649634999989)
                ·
                  refine ⟨5514008128674810903281249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58816086705864649634999989 5514008128674810903281249)
                  ·
                    refine ⟨4135506096506108177460937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5514008128674810903281249 4135506096506108177460937)
                    ·
                      refine ⟨3101629572379581133095703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135506096506108177460937 3101629572379581133095703)
                      ·
                        rfl

theorem cell23_6040402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_6040402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040402 prefixEnd_6040402 := by exact prefixLift 6040402
  have htrace : WordTrace (prefixWord ++ tailWord_6040402) baseStart_6040402 baseEnd_6040402 := by
    simpa [prefixWord, tailWord_6040402, baseEnd_6040402] using wordTrace_append hprefix tailTrace_6040402
  have hstable : (prefixWord ++ tailWord_6040402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040402).length < 2 ^ (prefixWord ++ tailWord_6040402).sum := by decide
  have hdescent : baseEnd_6040402 < baseStart_6040402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040412 : List Nat := [2, 2, 4, 2, 1, 2, 1, 1, 4, 4]
def baseStart_6040412 : Nat := 118140960795 + 6040412 * 2 ^ 59
def prefixEnd_6040412 : Nat := 4983230072969 + 3 ^ 40 * 6040412 * 2
def baseEnd_6040412 : Nat := 1033878235728708697990219

theorem tailTrace_6040412 : CollatzResearch.WordTrace tailWord_6040412 prefixEnd_6040412 1033878235728708697990219 := by
  unfold tailWord_6040412
  simp only [CollatzResearch.WordTrace]
  refine ⟨110155962496313209541613745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146874616661750946055484993 110155962496313209541613745)
  ·
    refine ⟨82616971872234907156210309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110155962496313209541613745 82616971872234907156210309)
    ·
      refine ⟨15490682226044045091789433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82616971872234907156210309 15490682226044045091789433)
      ·
        refine ⟨11618011669533033818842075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15490682226044045091789433 11618011669533033818842075)
        ·
          refine ⟨17427017504299550728263113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11618011669533033818842075 17427017504299550728263113)
          ·
            refine ⟨13070263128224663046197335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17427017504299550728263113 13070263128224663046197335)
            ·
              refine ⟨19605394692336994569296003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13070263128224663046197335 19605394692336994569296003)
              ·
                refine ⟨29408092038505491853944005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19605394692336994569296003 29408092038505491853944005)
                ·
                  refine ⟨5514017257219779722614501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29408092038505491853944005 5514017257219779722614501)
                  ·
                    refine ⟨1033878235728708697990219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5514017257219779722614501 1033878235728708697990219)
                    ·
                      rfl

theorem cell23_6040412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 1, 4, 4].length) (baseStart_6040412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040412 prefixEnd_6040412 := by exact prefixLift 6040412
  have htrace : WordTrace (prefixWord ++ tailWord_6040412) baseStart_6040412 baseEnd_6040412 := by
    simpa [prefixWord, tailWord_6040412, baseEnd_6040412] using wordTrace_append hprefix tailTrace_6040412
  have hstable : (prefixWord ++ tailWord_6040412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040412).length < 2 ^ (prefixWord ++ tailWord_6040412).sum := by decide
  have hdescent : baseEnd_6040412 < baseStart_6040412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040419 : List Nat := [1, 1, 1, 5, 3, 2, 2, 1, 3, 2, 2]
def baseStart_6040419 : Nat := 118140960795 + 6040419 * 2 ^ 59
def prefixEnd_6040419 : Nat := 4983230072969 + 3 ^ 40 * 6040419 * 2
def baseEnd_6040419 : Nat := 3101638301550707566583125

theorem tailTrace_6040419 : CollatzResearch.WordTrace tailWord_6040419 prefixEnd_6040419 3101638301550707566583125 := by
  unfold tailWord_6040419
  simp only [CollatzResearch.WordTrace]
  refine ⟨220312180303601059278732311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146874786869067372852488207 220312180303601059278732311)
  ·
    refine ⟨330468270455401588918098467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220312180303601059278732311 330468270455401588918098467)
    ·
      refine ⟨495702405683102383377147701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330468270455401588918098467 495702405683102383377147701)
      ·
        refine ⟨46472100532790848441607597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 495702405683102383377147701 46472100532790848441607597)
        ·
          refine ⟨17427037699796568165602849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46472100532790848441607597 17427037699796568165602849)
          ·
            refine ⟨13070278274847426124202137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17427037699796568165602849 13070278274847426124202137)
            ·
              refine ⟨9802708706135569593151603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13070278274847426124202137 9802708706135569593151603)
              ·
                refine ⟨14704063059203354389727405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9802708706135569593151603 14704063059203354389727405)
                ·
                  refine ⟨5514023647201257896147777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14704063059203354389727405 5514023647201257896147777)
                  ·
                    refine ⟨4135517735400943422110833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5514023647201257896147777 4135517735400943422110833)
                    ·
                      refine ⟨3101638301550707566583125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135517735400943422110833 3101638301550707566583125)
                      ·
                        rfl

theorem cell23_6040419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_6040419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040419 prefixEnd_6040419 := by exact prefixLift 6040419
  have htrace : WordTrace (prefixWord ++ tailWord_6040419) baseStart_6040419 baseEnd_6040419 := by
    simpa [prefixWord, tailWord_6040419, baseEnd_6040419] using wordTrace_append hprefix tailTrace_6040419
  have hstable : (prefixWord ++ tailWord_6040419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040419).length < 2 ^ (prefixWord ++ tailWord_6040419).sum := by decide
  have hdescent : baseEnd_6040419 < baseStart_6040419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040435 : List Nat := [1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 3]
def baseStart_6040435 : Nat := 118140960795 + 6040435 * 2 ^ 59
def prefixEnd_6040435 : Nat := 4983230072969 + 3 ^ 40 * 6040435 * 2
def baseEnd_6040435 : Nat := 3101646517241179503983051

theorem tailTrace_6040435 : CollatzResearch.WordTrace tailWord_6040435 prefixEnd_6040435 3101646517241179503983051 := by
  unfold tailWord_6040435
  simp only [CollatzResearch.WordTrace]
  refine ⟨220312763871543094011314759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146875175914362062674209839 220312763871543094011314759)
  ·
    refine ⟨330469145807314641016972139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220312763871543094011314759 330469145807314641016972139)
    ·
      refine ⟨495703718710971961525458209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330469145807314641016972139 495703718710971961525458209)
      ·
        refine ⟨371777789033228971144093657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495703718710971961525458209 371777789033228971144093657)
        ·
          refine ⟨278833341774921728358070243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371777789033228971144093657 278833341774921728358070243)
          ·
            refine ⟨418250012662382592537105365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278833341774921728358070243 418250012662382592537105365)
            ·
              refine ⟨9802734671774592012588407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 418250012662382592537105365 9802734671774592012588407)
              ·
                refine ⟨14704102007661888018882611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9802734671774592012588407 14704102007661888018882611)
                ·
                  refine ⟨22056153011492832028323917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14704102007661888018882611 22056153011492832028323917)
                  ·
                    refine ⟨8271057379309812010621469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22056153011492832028323917 8271057379309812010621469)
                    ·
                      refine ⟨3101646517241179503983051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8271057379309812010621469 3101646517241179503983051)
                      ·
                        rfl

theorem cell23_6040435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 3].length) (baseStart_6040435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040435 prefixEnd_6040435 := by exact prefixLift 6040435
  have htrace : WordTrace (prefixWord ++ tailWord_6040435) baseStart_6040435 baseEnd_6040435 := by
    simpa [prefixWord, tailWord_6040435, baseEnd_6040435] using wordTrace_append hprefix tailTrace_6040435
  have hstable : (prefixWord ++ tailWord_6040435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040435).length < 2 ^ (prefixWord ++ tailWord_6040435).sum := by decide
  have hdescent : baseEnd_6040435 < baseStart_6040435 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040470 : List Nat := [5, 3, 1, 1, 1, 3, 1, 1, 3, 2, 2]
def baseStart_6040470 : Nat := 118140960795 + 6040470 * 2 ^ 59
def prefixEnd_6040470 : Nat := 4983230072969 + 3 ^ 40 * 6040470 * 2
def baseEnd_6040470 : Nat := 3101664489064086867045391

theorem tailTrace_6040470 : CollatzResearch.WordTrace tailWord_6040470 prefixEnd_6040470 3101664489064086867045391 := by
  unfold tailWord_6040470
  simp only [CollatzResearch.WordTrace]
  refine ⟨13769627526651018436802429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146876026950944196659225909 13769627526651018436802429)
  ·
    refine ⟨5163610322494131913800911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13769627526651018436802429 5163610322494131913800911)
    ·
      refine ⟨7745415483741197870701367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5163610322494131913800911 7745415483741197870701367)
      ·
        refine ⟨11618123225611796806052051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7745415483741197870701367 11618123225611796806052051)
        ·
          refine ⟨17427184838417695209078077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11618123225611796806052051 17427184838417695209078077)
          ·
            refine ⟨6535194314406635703404279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17427184838417695209078077 6535194314406635703404279)
            ·
              refine ⟨9802791471609953555106419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6535194314406635703404279 9802791471609953555106419)
              ·
                refine ⟨14704187207414930332659629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9802791471609953555106419 14704187207414930332659629)
                ·
                  refine ⟨5514070202780598874747361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14704187207414930332659629 5514070202780598874747361)
                  ·
                    refine ⟨4135552652085449156060521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5514070202780598874747361 4135552652085449156060521)
                    ·
                      refine ⟨3101664489064086867045391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135552652085449156060521 3101664489064086867045391)
                      ·
                        rfl

theorem cell23_6040470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_6040470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040470 prefixEnd_6040470 := by exact prefixLift 6040470
  have htrace : WordTrace (prefixWord ++ tailWord_6040470) baseStart_6040470 baseEnd_6040470 := by
    simpa [prefixWord, tailWord_6040470, baseEnd_6040470] using wordTrace_append hprefix tailTrace_6040470
  have hstable : (prefixWord ++ tailWord_6040470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040470).length < 2 ^ (prefixWord ++ tailWord_6040470).sum := by decide
  have hdescent : baseEnd_6040470 < baseStart_6040470 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040509 : List Nat := [1, 4, 1, 2, 4, 1, 1, 2, 1, 4, 2]
def baseStart_6040509 : Nat := 118140960795 + 6040509 * 2 ^ 59
def prefixEnd_6040509 : Nat := 4983230072969 + 3 ^ 40 * 6040509 * 2
def baseEnd_6040509 : Nat := 3101684514809612214457711

theorem tailTrace_6040509 : CollatzResearch.WordTrace tailWord_6040509 prefixEnd_6040509 3101684514809612214457711 := by
  unfold tailWord_6040509
  simp only [CollatzResearch.WordTrace]
  refine ⟨220315462873275004649508581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146876975248850003099672387 220315462873275004649508581)
  ·
    refine ⟨41309149288739063371782859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220315462873275004649508581 41309149288739063371782859)
    ·
      refine ⟨61963723933108595057674289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41309149288739063371782859 61963723933108595057674289)
      ·
        refine ⟨46472792949831446293255717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61963723933108595057674289 46472792949831446293255717)
        ·
          refine ⟨8713648678093396179985447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46472792949831446293255717 8713648678093396179985447)
          ·
            refine ⟨13070473017140094269978171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8713648678093396179985447 13070473017140094269978171)
            ·
              refine ⟨19605709525710141404967257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13070473017140094269978171 19605709525710141404967257)
              ·
                refine ⟨14704282144282606053725443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19605709525710141404967257 14704282144282606053725443)
                ·
                  refine ⟨22056423216423909080588165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14704282144282606053725443 22056423216423909080588165)
                  ·
                    refine ⟨4135579353079482952610281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22056423216423909080588165 4135579353079482952610281)
                    ·
                      refine ⟨3101684514809612214457711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135579353079482952610281 3101684514809612214457711)
                      ·
                        rfl

theorem cell23_6040509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_6040509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040509 prefixEnd_6040509 := by exact prefixLift 6040509
  have htrace : WordTrace (prefixWord ++ tailWord_6040509) baseStart_6040509 baseEnd_6040509 := by
    simpa [prefixWord, tailWord_6040509, baseEnd_6040509] using wordTrace_append hprefix tailTrace_6040509
  have hstable : (prefixWord ++ tailWord_6040509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040509).length < 2 ^ (prefixWord ++ tailWord_6040509).sum := by decide
  have hdescent : baseEnd_6040509 < baseStart_6040509 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040526 : List Nat := [4, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2]
def baseStart_6040526 : Nat := 118140960795 + 6040526 * 2 ^ 59
def prefixEnd_6040526 : Nat := 4983230072969 + 3 ^ 40 * 6040526 * 2
def baseEnd_6040526 : Nat := 3101693243980738647945133

theorem tailTrace_6040526 : CollatzResearch.WordTrace tailWord_6040526 prefixEnd_6040526 3101693243980738647945133 := by
  unfold tailWord_6040526
  simp only [CollatzResearch.WordTrace]
  refine ⟨27539510364276677069109679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146877388609475611035251621 27539510364276677069109679)
  ·
    refine ⟨41309265546415015603664519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27539510364276677069109679 41309265546415015603664519)
    ·
      refine ⟨61963898319622523405496779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41309265546415015603664519 61963898319622523405496779)
      ·
        refine ⟨92945847479433785108245169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61963898319622523405496779 92945847479433785108245169)
        ·
          refine ⟨69709385609575338831183877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92945847479433785108245169 69709385609575338831183877)
          ·
            refine ⟨13070509801795376030846977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69709385609575338831183877 13070509801795376030846977)
            ·
              refine ⟨9802882351346532023135233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13070509801795376030846977 9802882351346532023135233)
              ·
                refine ⟨7352161763509899017351425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9802882351346532023135233 7352161763509899017351425)
                ·
                  refine ⟨5514121322632424263013569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7352161763509899017351425 5514121322632424263013569)
                  ·
                    refine ⟨4135590991974318197260177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5514121322632424263013569 4135590991974318197260177)
                    ·
                      refine ⟨3101693243980738647945133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135590991974318197260177 3101693243980738647945133)
                      ·
                        rfl

theorem cell23_6040526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 2, 2, 2, 2].length) (baseStart_6040526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040526 prefixEnd_6040526 := by exact prefixLift 6040526
  have htrace : WordTrace (prefixWord ++ tailWord_6040526) baseStart_6040526 baseEnd_6040526 := by
    simpa [prefixWord, tailWord_6040526, baseEnd_6040526] using wordTrace_append hprefix tailTrace_6040526
  have hstable : (prefixWord ++ tailWord_6040526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040526).length < 2 ^ (prefixWord ++ tailWord_6040526).sum := by decide
  have hdescent : baseEnd_6040526 < baseStart_6040526 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040528 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 3, 7]
def baseStart_6040528 : Nat := 118140960795 + 6040528 * 2 ^ 59
def prefixEnd_6040528 : Nat := 4983230072969 + 3 ^ 40 * 6040528 * 2
def baseEnd_6040528 : Nat := 1033898090314015880040041

theorem tailTrace_6040528 : CollatzResearch.WordTrace tailWord_6040528 prefixEnd_6040528 1033898090314015880040041 := by
  unfold tailWord_6040528
  simp only [CollatzResearch.WordTrace]
  refine ⟨110158077930103085447225119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146877437240137447262966825 110158077930103085447225119)
  ·
    refine ⟨165237116895154628170837679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110158077930103085447225119 165237116895154628170837679)
    ·
      refine ⟨247855675342731942256256519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165237116895154628170837679 247855675342731942256256519)
      ·
        refine ⟨371783513014097913384384779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247855675342731942256256519 371783513014097913384384779)
        ·
          refine ⟨557675269521146870076577169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371783513014097913384384779 557675269521146870076577169)
          ·
            refine ⟨418256452140860152557432877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557675269521146870076577169 418256452140860152557432877)
            ·
              refine ⟨156846169552822557209037329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 418256452140860152557432877 156846169552822557209037329)
              ·
                refine ⟨117634627164616917906777997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156846169552822557209037329 117634627164616917906777997)
                ·
                  refine ⟨44112985186731344215041749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117634627164616917906777997 44112985186731344215041749)
                  ·
                    refine ⟨1033898090314015880040041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 44112985186731344215041749 1033898090314015880040041)
                    ·
                      rfl

theorem cell23_6040528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3, 7].length) (baseStart_6040528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040528 prefixEnd_6040528 := by exact prefixLift 6040528
  have htrace : WordTrace (prefixWord ++ tailWord_6040528) baseStart_6040528 baseEnd_6040528 := by
    simpa [prefixWord, tailWord_6040528, baseEnd_6040528] using wordTrace_append hprefix tailTrace_6040528
  have hstable : (prefixWord ++ tailWord_6040528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040528).length < 2 ^ (prefixWord ++ tailWord_6040528).sum := by decide
  have hdescent : baseEnd_6040528 < baseStart_6040528 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040564 : List Nat := [2, 6, 2, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_6040564 : Nat := 118140960795 + 6040564 * 2 ^ 59
def prefixEnd_6040564 : Nat := 4983230072969 + 3 ^ 40 * 6040564 * 2
def baseEnd_6040564 : Nat := 3101712756245609499269959

theorem tailTrace_6040564 : CollatzResearch.WordTrace tailWord_6040564 prefixEnd_6040564 3101712756245609499269959 := by
  unfold tailWord_6040564
  simp only [CollatzResearch.WordTrace]
  refine ⟨110158734444037874521380373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146878312592050499361840497 110158734444037874521380373)
  ·
    refine ⟨5163690677064275368189705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110158734444037874521380373 5163690677064275368189705)
    ·
      refine ⟨3872768007798206526142279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5163690677064275368189705 3872768007798206526142279)
      ·
        refine ⟨5809152011697309789213419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3872768007798206526142279 5809152011697309789213419)
        ·
          refine ⟨8713728017545964683820129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5809152011697309789213419 8713728017545964683820129)
          ·
            refine ⟨6535296013159473512865097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8713728017545964683820129 6535296013159473512865097)
            ·
              refine ⟨4901472009869605134648823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6535296013159473512865097 4901472009869605134648823)
              ·
                refine ⟨7352208014804407701973235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4901472009869605134648823 7352208014804407701973235)
                ·
                  refine ⟨11028312022206611552959853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7352208014804407701973235 11028312022206611552959853)
                  ·
                    refine ⟨4135617008327479332359945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11028312022206611552959853 4135617008327479332359945)
                    ·
                      refine ⟨3101712756245609499269959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135617008327479332359945 3101712756245609499269959)
                      ·
                        rfl

theorem cell23_6040564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_6040564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040564 prefixEnd_6040564 := by exact prefixLift 6040564
  have htrace : WordTrace (prefixWord ++ tailWord_6040564) baseStart_6040564 baseEnd_6040564 := by
    simpa [prefixWord, tailWord_6040564, baseEnd_6040564] using wordTrace_append hprefix tailTrace_6040564
  have hstable : (prefixWord ++ tailWord_6040564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040564).length < 2 ^ (prefixWord ++ tailWord_6040564).sum := by decide
  have hdescent : baseEnd_6040564 < baseStart_6040564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040599 : List Nat := [1, 1, 3, 5, 1, 1, 2, 1, 2, 4, 2]
def baseStart_6040599 : Nat := 118140960795 + 6040599 * 2 ^ 59
def prefixEnd_6040599 : Nat := 4983230072969 + 3 ^ 40 * 6040599 * 2
def baseEnd_6040599 : Nat := 3101730728068516862332297

theorem tailTrace_6040599 : CollatzResearch.WordTrace tailWord_6040599 prefixEnd_6040599 3101730728068516862332297 := by
  unfold tailWord_6040599
  simp only [CollatzResearch.WordTrace]
  refine ⟨220318745442948950020284851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146879163628632633346856567 220318745442948950020284851)
  ·
    refine ⟨330478118164423425030427277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220318745442948950020284851 330478118164423425030427277)
    ·
      refine ⟨123929294311658784386410229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330478118164423425030427277 123929294311658784386410229)
      ·
        refine ⟨11618371341718011036225959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123929294311658784386410229 11618371341718011036225959)
        ·
          refine ⟨17427557012577016554338939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11618371341718011036225959 17427557012577016554338939)
          ·
            refine ⟨26141335518865524831508409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17427557012577016554338939 26141335518865524831508409)
            ·
              refine ⟨19606001639149143623631307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26141335518865524831508409 19606001639149143623631307)
              ·
                refine ⟨29409002458723715435446961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19606001639149143623631307 29409002458723715435446961)
                ·
                  refine ⟨22056751844042786576585221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29409002458723715435446961 22056751844042786576585221)
                  ·
                    refine ⟨4135640970758022483109729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22056751844042786576585221 4135640970758022483109729)
                    ·
                      refine ⟨3101730728068516862332297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135640970758022483109729 3101730728068516862332297)
                      ·
                        rfl

theorem cell23_6040599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_6040599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040599 prefixEnd_6040599 := by exact prefixLift 6040599
  have htrace : WordTrace (prefixWord ++ tailWord_6040599) baseStart_6040599 baseEnd_6040599 := by
    simpa [prefixWord, tailWord_6040599, baseEnd_6040599] using wordTrace_append hprefix tailTrace_6040599
  have hstable : (prefixWord ++ tailWord_6040599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040599).length < 2 ^ (prefixWord ++ tailWord_6040599).sum := by decide
  have hdescent : baseEnd_6040599 < baseStart_6040599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040672 : List Nat := [2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 4]
def baseStart_6040672 : Nat := 118140960795 + 6040672 * 2 ^ 59
def prefixEnd_6040672 : Nat := 4983230072969 + 3 ^ 40 * 6040672 * 2
def baseEnd_6040672 : Nat := 3101768212156295076719461

theorem tailTrace_6040672 : CollatzResearch.WordTrace tailWord_6040672 prefixEnd_6040672 3101768212156295076719461 := by
  unfold tailWord_6040672
  simp only [CollatzResearch.WordTrace]
  refine ⟨110160703985842241743846135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146880938647789655658461513 110160703985842241743846135)
  ·
    refine ⟨165241055978763362615769203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110160703985842241743846135 165241055978763362615769203)
    ·
      refine ⟨247861583968145043923653805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165241055978763362615769203 247861583968145043923653805)
      ·
        refine ⟨92948093988054391471370177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247861583968145043923653805 92948093988054391471370177)
        ·
          refine ⟨69711070491040793603527633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92948093988054391471370177 69711070491040793603527633)
          ·
            refine ⟨52283302868280595202645725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69711070491040793603527633 52283302868280595202645725)
            ·
              refine ⟨19606238575605223200992147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52283302868280595202645725 19606238575605223200992147)
              ·
                refine ⟨29409357863407834801488221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19606238575605223200992147 29409357863407834801488221)
                ·
                  refine ⟨11028509198777938050558083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29409357863407834801488221 11028509198777938050558083)
                  ·
                    refine ⟨16542763798166907075837125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11028509198777938050558083 16542763798166907075837125)
                    ·
                      refine ⟨3101768212156295076719461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16542763798166907075837125 3101768212156295076719461)
                      ·
                        rfl

theorem cell23_6040672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 4].length) (baseStart_6040672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040672 prefixEnd_6040672 := by exact prefixLift 6040672
  have htrace : WordTrace (prefixWord ++ tailWord_6040672) baseStart_6040672 baseEnd_6040672 := by
    simpa [prefixWord, tailWord_6040672, baseEnd_6040672] using wordTrace_append hprefix tailTrace_6040672
  have hstable : (prefixWord ++ tailWord_6040672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040672).length < 2 ^ (prefixWord ++ tailWord_6040672).sum := by decide
  have hdescent : baseEnd_6040672 < baseStart_6040672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040682 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 3, 6]
def baseStart_6040682 : Nat := 118140960795 + 6040682 * 2 ^ 59
def prefixEnd_6040682 : Nat := 4983230072969 + 3 ^ 40 * 6040682 * 2
def baseEnd_6040682 : Nat := 1033924448987613345864805

theorem tailTrace_6040682 : CollatzResearch.WordTrace tailWord_6040682 prefixEnd_6040682 1033924448987613345864805 := by
  unfold tailWord_6040682
  simp only [CollatzResearch.WordTrace]
  refine ⟨55080443175412063798889075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146881181801098836797037533 55080443175412063798889075)
  ·
    refine ⟨82620664763118095698333613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55080443175412063798889075 82620664763118095698333613)
    ·
      refine ⟨30982749286169285886875105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82620664763118095698333613 30982749286169285886875105)
      ·
        refine ⟨23237061964626964415156329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30982749286169285886875105 23237061964626964415156329)
        ·
          refine ⟨17427796473470223311367247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23237061964626964415156329 17427796473470223311367247)
          ·
            refine ⟨26141694710205334967050871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17427796473470223311367247 26141694710205334967050871)
            ·
              refine ⟨39212542065308002450576307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26141694710205334967050871 39212542065308002450576307)
              ·
                refine ⟨58818813097962003675864461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39212542065308002450576307 58818813097962003675864461)
                ·
                  refine ⟨22057054911735751378449173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58818813097962003675864461 22057054911735751378449173)
                  ·
                    refine ⟨1033924448987613345864805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22057054911735751378449173 1033924448987613345864805)
                    ·
                      rfl

theorem cell23_6040682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_6040682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040682 prefixEnd_6040682 := by exact prefixLift 6040682
  have htrace : WordTrace (prefixWord ++ tailWord_6040682) baseStart_6040682 baseEnd_6040682 := by
    simpa [prefixWord, tailWord_6040682, baseEnd_6040682] using wordTrace_append hprefix tailTrace_6040682
  have hstable : (prefixWord ++ tailWord_6040682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040682).length < 2 ^ (prefixWord ++ tailWord_6040682).sum := by decide
  have hdescent : baseEnd_6040682 < baseStart_6040682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040686 : List Nat := [4, 1, 2, 2, 1, 3, 3, 1, 1, 5]
def baseStart_6040686 : Nat := 118140960795 + 6040686 * 2 ^ 59
def prefixEnd_6040686 : Nat := 4983230072969 + 3 ^ 40 * 6040686 * 2
def baseEnd_6040686 : Nat := 1033925133628486007314799

theorem tailTrace_6040686 : CollatzResearch.WordTrace tailWord_6040686 prefixEnd_6040686 1033925133628486007314799 := by
  unfold tailWord_6040686
  simp only [CollatzResearch.WordTrace]
  refine ⟨27540239824204220484837739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146881279062422509252467941 27540239824204220484837739)
  ·
    refine ⟨41310359736306330727256609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27540239824204220484837739 41310359736306330727256609)
    ·
      refine ⟨30982769802229748045442457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41310359736306330727256609 30982769802229748045442457)
      ·
        refine ⟨23237077351672311034081843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30982769802229748045442457 23237077351672311034081843)
        ·
          refine ⟨34855616027508466551122765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23237077351672311034081843 34855616027508466551122765)
          ·
            refine ⟨13070856010315674956671037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34855616027508466551122765 13070856010315674956671037)
            ·
              refine ⟨4901571003868378108751639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13070856010315674956671037 4901571003868378108751639)
              ·
                refine ⟨7352356505802567163127459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4901571003868378108751639 7352356505802567163127459)
                ·
                  refine ⟨11028534758703850744691189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7352356505802567163127459 11028534758703850744691189)
                  ·
                    refine ⟨1033925133628486007314799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11028534758703850744691189 1033925133628486007314799)
                    ·
                      rfl

theorem cell23_6040686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_6040686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040686 prefixEnd_6040686 := by exact prefixLift 6040686
  have htrace : WordTrace (prefixWord ++ tailWord_6040686) baseStart_6040686 baseEnd_6040686 := by
    simpa [prefixWord, tailWord_6040686, baseEnd_6040686] using wordTrace_append hprefix tailTrace_6040686
  have hstable : (prefixWord ++ tailWord_6040686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040686).length < 2 ^ (prefixWord ++ tailWord_6040686).sum := by decide
  have hdescent : baseEnd_6040686 < baseStart_6040686 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040689 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 7, 2, 2]
def baseStart_6040689 : Nat := 118140960795 + 6040689 * 2 ^ 59
def prefixEnd_6040689 : Nat := 4983230072969 + 3 ^ 40 * 6040689 * 2
def baseEnd_6040689 : Nat := 3101776941327421510206883

theorem tailTrace_6040689 : CollatzResearch.WordTrace tailWord_6040689 prefixEnd_6040689 3101776941327421510206883 := by
  unfold tailWord_6040689
  simp only [CollatzResearch.WordTrace]
  refine ⟨220322028012622895391061121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146881352008415263594040747 220322028012622895391061121)
  ·
    refine ⟨165241521009467171543295841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220322028012622895391061121 165241521009467171543295841)
    ·
      refine ⟨123931140757100378657471881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165241521009467171543295841 123931140757100378657471881)
      ·
        refine ⟨92948355567825283993103911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123931140757100378657471881 92948355567825283993103911)
        ·
          refine ⟨139422533351737925989655867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92948355567825283993103911 139422533351737925989655867)
          ·
            refine ⟨209133800027606888984483801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139422533351737925989655867 209133800027606888984483801)
            ·
              refine ⟨156850350020705166738362851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209133800027606888984483801 156850350020705166738362851)
              ·
                refine ⟨235275525031057750107544277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156850350020705166738362851 235275525031057750107544277)
                ·
                  refine ⟨5514270117915416018145569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 235275525031057750107544277 5514270117915416018145569)
                  ·
                    refine ⟨4135702588436562013609177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5514270117915416018145569 4135702588436562013609177)
                    ·
                      refine ⟨3101776941327421510206883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135702588436562013609177 3101776941327421510206883)
                      ·
                        rfl

theorem cell23_6040689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 7, 2, 2].length) (baseStart_6040689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040689 prefixEnd_6040689 := by exact prefixLift 6040689
  have htrace : WordTrace (prefixWord ++ tailWord_6040689) baseStart_6040689 baseEnd_6040689 := by
    simpa [prefixWord, tailWord_6040689, baseEnd_6040689] using wordTrace_append hprefix tailTrace_6040689
  have hstable : (prefixWord ++ tailWord_6040689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040689).length < 2 ^ (prefixWord ++ tailWord_6040689).sum := by decide
  have hdescent : baseEnd_6040689 < baseStart_6040689 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040715 : List Nat := [1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 6]
def baseStart_6040715 : Nat := 118140960795 + 6040715 * 2 ^ 59
def prefixEnd_6040715 : Nat := 4983230072969 + 3 ^ 40 * 6040715 * 2
def baseEnd_6040715 : Nat := 3101790291824438408481763

theorem tailTrace_6040715 : CollatzResearch.WordTrace tailWord_6040715 prefixEnd_6040715 3101790291824438408481763 := by
  unfold tailWord_6040715
  simp only [CollatzResearch.WordTrace]
  refine ⟨220322976310528701831507599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146881984207019134554338399 220322976310528701831507599)
  ·
    refine ⟨330484464465793052747261399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220322976310528701831507599 330484464465793052747261399)
    ·
      refine ⟨495726696698689579120892099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330484464465793052747261399 495726696698689579120892099)
      ·
        refine ⟨743590045048034368681338149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495726696698689579120892099 743590045048034368681338149)
        ·
          refine ⟨139423133446506444127750903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 743590045048034368681338149 139423133446506444127750903)
          ·
            refine ⟨209134700169759666191626355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139423133446506444127750903 209134700169759666191626355)
            ·
              refine ⟨313702050254639499287439533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209134700169759666191626355 313702050254639499287439533)
              ·
                refine ⟨117638268845489812232789825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313702050254639499287439533 117638268845489812232789825)
                ·
                  refine ⟨88228701634117359174592369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117638268845489812232789825 88228701634117359174592369)
                  ·
                    refine ⟨66171526225588019380944277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88228701634117359174592369 66171526225588019380944277)
                    ·
                      refine ⟨3101790291824438408481763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66171526225588019380944277 3101790291824438408481763)
                      ·
                        rfl

theorem cell23_6040715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 6].length) (baseStart_6040715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040715 prefixEnd_6040715 := by exact prefixLift 6040715
  have htrace : WordTrace (prefixWord ++ tailWord_6040715) baseStart_6040715 baseEnd_6040715 := by
    simpa [prefixWord, tailWord_6040715, baseEnd_6040715] using wordTrace_append hprefix tailTrace_6040715
  have hstable : (prefixWord ++ tailWord_6040715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040715).length < 2 ^ (prefixWord ++ tailWord_6040715).sum := by decide
  have hdescent : baseEnd_6040715 < baseStart_6040715 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040740 : List Nat := [2, 3, 1, 2, 3, 2, 2, 3, 1, 2, 2]
def baseStart_6040740 : Nat := 118140960795 + 6040740 * 2 ^ 59
def prefixEnd_6040740 : Nat := 4983230072969 + 3 ^ 40 * 6040740 * 2
def baseEnd_6040740 : Nat := 3101803128840800810669149

theorem tailTrace_6040740 : CollatzResearch.WordTrace tailWord_6040740 prefixEnd_6040740 3101803128840800810669149 := by
  unfold tailWord_6040740
  simp only [CollatzResearch.WordTrace]
  refine ⟨110161944067719065550583837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146882592090292087400778449 110161944067719065550583837)
  ·
    refine ⟨41310729025394649581468939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110161944067719065550583837 41310729025394649581468939)
    ·
      refine ⟨61966093538091974372203409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41310729025394649581468939 61966093538091974372203409)
      ·
        refine ⟨46474570153568980779152557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61966093538091974372203409 46474570153568980779152557)
        ·
          refine ⟨17427963807588367792182209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46474570153568980779152557 17427963807588367792182209)
          ·
            refine ⟨13070972855691275844136657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17427963807588367792182209 13070972855691275844136657)
            ·
              refine ⟨9803229641768456883102493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13070972855691275844136657 9803229641768456883102493)
              ·
                refine ⟨3676211115663171331163435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9803229641768456883102493 3676211115663171331163435)
                ·
                  refine ⟨5514316673494756996745153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3676211115663171331163435 5514316673494756996745153)
                  ·
                    refine ⟨4135737505121067747558865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5514316673494756996745153 4135737505121067747558865)
                    ·
                      refine ⟨3101803128840800810669149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135737505121067747558865 3101803128840800810669149)
                      ·
                        rfl

theorem cell23_6040740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 3, 1, 2, 2].length) (baseStart_6040740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040740 prefixEnd_6040740 := by exact prefixLift 6040740
  have htrace : WordTrace (prefixWord ++ tailWord_6040740) baseStart_6040740 baseEnd_6040740 := by
    simpa [prefixWord, tailWord_6040740, baseEnd_6040740] using wordTrace_append hprefix tailTrace_6040740
  have hstable : (prefixWord ++ tailWord_6040740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040740).length < 2 ^ (prefixWord ++ tailWord_6040740).sum := by decide
  have hdescent : baseEnd_6040740 < baseStart_6040740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040743 : List Nat := [1, 1, 6, 2, 1, 1, 4, 1, 1, 2, 3]
def baseStart_6040743 : Nat := 118140960795 + 6040743 * 2 ^ 59
def prefixEnd_6040743 : Nat := 4983230072969 + 3 ^ 40 * 6040743 * 2
def baseEnd_6040743 : Nat := 3101804669282764298931635

theorem tailTrace_6040743 : CollatzResearch.WordTrace tailWord_6040743 prefixEnd_6040743 3101804669282764298931635 := by
  unfold tailWord_6040743
  simp only [CollatzResearch.WordTrace]
  refine ⟨220323997554427262613526883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146882665036284841742351255 220323997554427262613526883)
  ·
    refine ⟨330485996331640893920290325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220323997554427262613526883 330485996331640893920290325)
    ·
      refine ⟨15491531078045666902513609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 330485996331640893920290325 15491531078045666902513609)
      ·
        refine ⟨11618648308534250176885207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15491531078045666902513609 11618648308534250176885207)
        ·
          refine ⟨17427972462801375265327811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11618648308534250176885207 17427972462801375265327811)
          ·
            refine ⟨26141958694202062897991717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17427972462801375265327811 26141958694202062897991717)
            ·
              refine ⟨4901617255162886793373447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26141958694202062897991717 4901617255162886793373447)
              ·
                refine ⟨7352425882744330190060171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4901617255162886793373447 7352425882744330190060171)
                ·
                  refine ⟨11028638824116495285090257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7352425882744330190060171 11028638824116495285090257)
                  ·
                    refine ⟨8271479118087371463817693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11028638824116495285090257 8271479118087371463817693)
                    ·
                      refine ⟨3101804669282764298931635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8271479118087371463817693 3101804669282764298931635)
                      ·
                        rfl

theorem cell23_6040743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_6040743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040743 prefixEnd_6040743 := by exact prefixLift 6040743
  have htrace : WordTrace (prefixWord ++ tailWord_6040743) baseStart_6040743 baseEnd_6040743 := by
    simpa [prefixWord, tailWord_6040743, baseEnd_6040743] using wordTrace_append hprefix tailTrace_6040743
  have hstable : (prefixWord ++ tailWord_6040743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040743).length < 2 ^ (prefixWord ++ tailWord_6040743).sum := by decide
  have hdescent : baseEnd_6040743 < baseStart_6040743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040745 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 8]
def baseStart_6040745 : Nat := 118140960795 + 6040745 * 2 ^ 59
def prefixEnd_6040745 : Nat := 4983230072969 + 3 ^ 40 * 6040745 * 2
def baseEnd_6040745 : Nat := 3101805696244073291106625

theorem tailTrace_6040745 : CollatzResearch.WordTrace tailWord_6040745 prefixEnd_6040745 3101805696244073291106625 := by
  unfold tailWord_6040745
  simp only [CollatzResearch.WordTrace]
  refine ⟨220324070500420016955099689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146882713666946677970066459 220324070500420016955099689)
  ·
    refine ⟨165243052875315012716324767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220324070500420016955099689 165243052875315012716324767)
    ·
      refine ⟨247864579312972519074487151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165243052875315012716324767 247864579312972519074487151)
      ·
        refine ⟨371796868969458778611730727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247864579312972519074487151 371796868969458778611730727)
        ·
          refine ⟨557695303454188167917596091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371796868969458778611730727 557695303454188167917596091)
          ·
            refine ⟨836542955181282251876394137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557695303454188167917596091 836542955181282251876394137)
            ·
              refine ⟨627407216385961688907295603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 836542955181282251876394137 627407216385961688907295603)
              ·
                refine ⟨941110824578942533360943405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 627407216385961688907295603 941110824578942533360943405)
                ·
                  refine ⟨352916559217103450010353777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 941110824578942533360943405 352916559217103450010353777)
                  ·
                    refine ⟨264687419412827587507765333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 352916559217103450010353777 264687419412827587507765333)
                    ·
                      refine ⟨3101805696244073291106625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 264687419412827587507765333 3101805696244073291106625)
                      ·
                        rfl

theorem cell23_6040745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 2, 8].length) (baseStart_6040745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040745 prefixEnd_6040745 := by exact prefixLift 6040745
  have htrace : WordTrace (prefixWord ++ tailWord_6040745) baseStart_6040745 baseEnd_6040745 := by
    simpa [prefixWord, tailWord_6040745, baseEnd_6040745] using wordTrace_append hprefix tailTrace_6040745
  have hstable : (prefixWord ++ tailWord_6040745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040745).length < 2 ^ (prefixWord ++ tailWord_6040745).sum := by decide
  have hdescent : baseEnd_6040745 < baseStart_6040745 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040770 : List Nat := [3, 5, 1, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_6040770 : Nat := 118140960795 + 6040770 * 2 ^ 59
def prefixEnd_6040770 : Nat := 4983230072969 + 3 ^ 40 * 6040770 * 2
def baseEnd_6040770 : Nat := 3101818533260435693294011

theorem tailTrace_6040770 : CollatzResearch.WordTrace tailWord_6040770 prefixEnd_6040770 3101818533260435693294011 := by
  unfold tailWord_6040770
  simp only [CollatzResearch.WordTrace]
  refine ⟨55081245581332361556189941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146883321550219630816506509 55081245581332361556189941)
  ·
    refine ⟨5163866773249908895892807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55081245581332361556189941 5163866773249908895892807)
    ·
      refine ⟨7745800159874863343839211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5163866773249908895892807 7745800159874863343839211)
      ·
        refine ⟨11618700239812295015758817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7745800159874863343839211 11618700239812295015758817)
        ·
          refine ⟨8714025179859221261819113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11618700239812295015758817 8714025179859221261819113)
          ·
            refine ⟨6535518884894415946364335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8714025179859221261819113 6535518884894415946364335)
            ·
              refine ⟨9803278327341623919546503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6535518884894415946364335 9803278327341623919546503)
              ·
                refine ⟨14704917491012435879319755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9803278327341623919546503 14704917491012435879319755)
                ·
                  refine ⟨22057376236518653818979633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14704917491012435879319755 22057376236518653818979633)
                  ·
                    refine ⟨16543032177388990364234725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22057376236518653818979633 16543032177388990364234725)
                    ·
                      refine ⟨3101818533260435693294011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16543032177388990364234725 3101818533260435693294011)
                      ·
                        rfl

theorem cell23_6040770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_6040770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040770 prefixEnd_6040770 := by exact prefixLift 6040770
  have htrace : WordTrace (prefixWord ++ tailWord_6040770) baseStart_6040770 baseEnd_6040770 := by
    simpa [prefixWord, tailWord_6040770, baseEnd_6040770] using wordTrace_append hprefix tailTrace_6040770
  have hstable : (prefixWord ++ tailWord_6040770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040770).length < 2 ^ (prefixWord ++ tailWord_6040770).sum := by decide
  have hdescent : baseEnd_6040770 < baseStart_6040770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040779 : List Nat := [1, 1, 1, 1, 3, 2, 2, 5, 1, 4, 2]
def baseStart_6040779 : Nat := 118140960795 + 6040779 * 2 ^ 59
def prefixEnd_6040779 : Nat := 4983230072969 + 3 ^ 40 * 6040779 * 2
def baseEnd_6040779 : Nat := 3101823154586326158081469

theorem tailTrace_6040779 : CollatzResearch.WordTrace tailWord_6040779 prefixEnd_6040779 3101823154586326158081469 := by
  unfold tailWord_6040779
  simp only [CollatzResearch.WordTrace]
  refine ⟨220325310582296840761837391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146883540388197893841224927 220325310582296840761837391)
  ·
    refine ⟨330487965873445261142756087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220325310582296840761837391 330487965873445261142756087)
    ·
      refine ⟨495731948810167891714134131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330487965873445261142756087 495731948810167891714134131)
      ·
        refine ⟨743597923215251837571201197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495731948810167891714134131 743597923215251837571201197)
        ·
          refine ⟨278849221205719439089200449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 743597923215251837571201197 278849221205719439089200449)
          ·
            refine ⟨209136915904289579316900337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278849221205719439089200449 209136915904289579316900337)
            ·
              refine ⟨156852686928217184487675253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209136915904289579316900337 156852686928217184487675253)
              ·
                refine ⟨14704939399520361045719555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156852686928217184487675253 14704939399520361045719555)
                ·
                  refine ⟨22057409099280541568579333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14704939399520361045719555 22057409099280541568579333)
                  ·
                    refine ⟨4135764206115101544108625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22057409099280541568579333 4135764206115101544108625)
                    ·
                      refine ⟨3101823154586326158081469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135764206115101544108625 3101823154586326158081469)
                      ·
                        rfl

theorem cell23_6040779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 5, 1, 4, 2].length) (baseStart_6040779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040779 prefixEnd_6040779 := by exact prefixLift 6040779
  have htrace : WordTrace (prefixWord ++ tailWord_6040779) baseStart_6040779 baseEnd_6040779 := by
    simpa [prefixWord, tailWord_6040779, baseEnd_6040779] using wordTrace_append hprefix tailTrace_6040779
  have hstable : (prefixWord ++ tailWord_6040779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040779).length < 2 ^ (prefixWord ++ tailWord_6040779).sum := by decide
  have hdescent : baseEnd_6040779 < baseStart_6040779 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040813 : List Nat := [1, 5, 1, 2, 2, 1, 2, 1, 4, 2, 2]
def baseStart_6040813 : Nat := 118140960795 + 6040813 * 2 ^ 59
def prefixEnd_6040813 : Nat := 4983230072969 + 3 ^ 40 * 6040813 * 2
def baseEnd_6040813 : Nat := 3101840612928579025056313

theorem tailTrace_6040813 : CollatzResearch.WordTrace tailWord_6040813 prefixEnd_6040813 3101840612928579025056313 := by
  unfold tailWord_6040813
  simp only [CollatzResearch.WordTrace]
  refine ⟨220326550664173664568575093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146884367109449109712383395 220326550664173664568575093)
  ·
    refine ⟨20655614124766281053303915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220326550664173664568575093 20655614124766281053303915)
    ·
      refine ⟨30983421187149421579955873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20655614124766281053303915 30983421187149421579955873)
      ·
        refine ⟨23237565890362066184966905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30983421187149421579955873 23237565890362066184966905)
        ·
          refine ⟨17428174417771549638725179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23237565890362066184966905 17428174417771549638725179)
          ·
            refine ⟨26142261626657324458087769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17428174417771549638725179 26142261626657324458087769)
            ·
              refine ⟨19606696219992993343565827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26142261626657324458087769 19606696219992993343565827)
              ·
                refine ⟨29410044329989490015348741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19606696219992993343565827 29410044329989490015348741)
                ·
                  refine ⟨5514383311873029377877889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29410044329989490015348741 5514383311873029377877889)
                  ·
                    refine ⟨4135787483904772033408417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5514383311873029377877889 4135787483904772033408417)
                    ·
                      refine ⟨3101840612928579025056313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135787483904772033408417 3101840612928579025056313)
                      ·
                        rfl

theorem cell23_6040813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_6040813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040813 prefixEnd_6040813 := by exact prefixLift 6040813
  have htrace : WordTrace (prefixWord ++ tailWord_6040813) baseStart_6040813 baseEnd_6040813 := by
    simpa [prefixWord, tailWord_6040813, baseEnd_6040813] using wordTrace_append hprefix tailTrace_6040813
  have hstable : (prefixWord ++ tailWord_6040813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040813).length < 2 ^ (prefixWord ++ tailWord_6040813).sum := by decide
  have hdescent : baseEnd_6040813 < baseStart_6040813 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040819 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 7]
def baseStart_6040819 : Nat := 118140960795 + 6040819 * 2 ^ 59
def prefixEnd_6040819 : Nat := 4983230072969 + 3 ^ 40 * 6040819 * 2
def baseEnd_6040819 : Nat := 344649299312500666842365

theorem tailTrace_6040819 : CollatzResearch.WordTrace tailWord_6040819 prefixEnd_6040819 344649299312500666842365 := by
  unfold tailWord_6040819
  simp only [CollatzResearch.WordTrace]
  refine ⟨220326769502151927593293511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146884513001434618395529007 220326769502151927593293511)
  ·
    refine ⟨330490154253227891389940267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220326769502151927593293511 330490154253227891389940267)
    ·
      refine ⟨495735231379841837084910401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330490154253227891389940267 495735231379841837084910401)
      ·
        refine ⟨371801423534881377813682801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495735231379841837084910401 371801423534881377813682801)
        ·
          refine ⟨278851067651161033360262101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371801423534881377813682801 278851067651161033360262101)
          ·
            refine ⟨6535571898074086719381143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 278851067651161033360262101 6535571898074086719381143)
            ·
              refine ⟨9803357847111130079071715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6535571898074086719381143 9803357847111130079071715)
              ·
                refine ⟨14705036770666695118607573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9803357847111130079071715 14705036770666695118607573)
                ·
                  refine ⟨344649299312500666842365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14705036770666695118607573 344649299312500666842365)
                  ·
                    rfl

theorem cell23_6040819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 7].length) (baseStart_6040819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040819 prefixEnd_6040819 := by exact prefixLift 6040819
  have htrace : WordTrace (prefixWord ++ tailWord_6040819) baseStart_6040819 baseEnd_6040819 := by
    simpa [prefixWord, tailWord_6040819, baseEnd_6040819] using wordTrace_append hprefix tailTrace_6040819
  have hstable : (prefixWord ++ tailWord_6040819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040819).length < 2 ^ (prefixWord ++ tailWord_6040819).sum := by decide
  have hdescent : baseEnd_6040819 < baseStart_6040819 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040830 : List Nat := [4, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_6040830 : Nat := 118140960795 + 6040830 * 2 ^ 59
def prefixEnd_6040830 : Nat := 4983230072969 + 3 ^ 40 * 6040830 * 2
def baseEnd_6040830 : Nat := 3101849342099705458543735

theorem tailTrace_6040830 : CollatzResearch.WordTrace tailWord_6040830 prefixEnd_6040830 3101849342099705458543735 := by
  unfold tailWord_6040830
  simp only [CollatzResearch.WordTrace]
  refine ⟨27540896338139009558992993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146884780470074717647962629 27540896338139009558992993)
  ·
    refine ⟨20655672253604257169244745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27540896338139009558992993 20655672253604257169244745)
    ·
      refine ⟨15491754190203192876933559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20655672253604257169244745 15491754190203192876933559)
      ·
        refine ⟨23237631285304789315400339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15491754190203192876933559 23237631285304789315400339)
        ·
          refine ⟨34856446927957183973100509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23237631285304789315400339 34856446927957183973100509)
          ·
            refine ⟨13071167597983943989912691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34856446927957183973100509 13071167597983943989912691)
            ·
              refine ⟨19606751396975915984869037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13071167597983943989912691 19606751396975915984869037)
              ·
                refine ⟨7352531773865968494325889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19606751396975915984869037 7352531773865968494325889)
                ·
                  refine ⟨5514398830399476370744417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7352531773865968494325889 5514398830399476370744417)
                  ·
                    refine ⟨4135799122799607278058313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5514398830399476370744417 4135799122799607278058313)
                    ·
                      refine ⟨3101849342099705458543735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135799122799607278058313 3101849342099705458543735)
                      ·
                        rfl

theorem cell23_6040830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_6040830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040830 prefixEnd_6040830 := by exact prefixLift 6040830
  have htrace : WordTrace (prefixWord ++ tailWord_6040830) baseStart_6040830 baseEnd_6040830 := by
    simpa [prefixWord, tailWord_6040830, baseEnd_6040830] using wordTrace_append hprefix tailTrace_6040830
  have hstable : (prefixWord ++ tailWord_6040830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040830).length < 2 ^ (prefixWord ++ tailWord_6040830).sum := by decide
  have hdescent : baseEnd_6040830 < baseStart_6040830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040832 : List Nat := [2, 1, 1, 2, 1, 1, 3, 1, 6, 5]
def baseStart_6040832 : Nat := 118140960795 + 6040832 * 2 ^ 59
def prefixEnd_6040832 : Nat := 4983230072969 + 3 ^ 40 * 6040832 * 2
def baseEnd_6040832 : Nat := 1033950123020338150239575

theorem tailTrace_6040832 : CollatzResearch.WordTrace tailWord_6040832 prefixEnd_6040832 1033950123020338150239575 := by
  unfold tailWord_6040832
  simp only [CollatzResearch.WordTrace]
  refine ⟨110163621825552415406758375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146884829100736553875677833 110163621825552415406758375)
  ·
    refine ⟨165245432738328623110137563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110163621825552415406758375 165245432738328623110137563)
    ·
      refine ⟨247868149107492934665206345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165245432738328623110137563 247868149107492934665206345)
      ·
        refine ⟨185901111830619700998904759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247868149107492934665206345 185901111830619700998904759)
        ·
          refine ⟨278851667745929551498357139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185901111830619700998904759 278851667745929551498357139)
          ·
            refine ⟨418277501618894327247535709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278851667745929551498357139 418277501618894327247535709)
            ·
              refine ⟨156854063107085372717825891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 418277501618894327247535709 156854063107085372717825891)
              ·
                refine ⟨235281094660628059076738837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156854063107085372717825891 235281094660628059076738837)
                ·
                  refine ⟨11028801312216940269222133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 235281094660628059076738837 11028801312216940269222133)
                  ·
                    refine ⟨1033950123020338150239575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11028801312216940269222133 1033950123020338150239575)
                    ·
                      rfl

theorem cell23_6040832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 1, 6, 5].length) (baseStart_6040832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040832 prefixEnd_6040832 := by exact prefixLift 6040832
  have htrace : WordTrace (prefixWord ++ tailWord_6040832) baseStart_6040832 baseEnd_6040832 := by
    simpa [prefixWord, tailWord_6040832, baseEnd_6040832] using wordTrace_append hprefix tailTrace_6040832
  have hstable : (prefixWord ++ tailWord_6040832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040832).length < 2 ^ (prefixWord ++ tailWord_6040832).sum := by decide
  have hdescent : baseEnd_6040832 < baseStart_6040832 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040842 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7]
def baseStart_6040842 : Nat := 118140960795 + 6040842 * 2 ^ 59
def prefixEnd_6040842 : Nat := 4983230072969 + 3 ^ 40 * 6040842 * 2
def baseEnd_6040842 : Nat := 3101855503867559411593679

theorem tailTrace_6040842 : CollatzResearch.WordTrace tailWord_6040842 prefixEnd_6040842 3101855503867559411593679 := by
  unfold tailWord_6040842
  simp only [CollatzResearch.WordTrace]
  refine ⟨55081902095267150630345195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146885072254045735014253853 55081902095267150630345195)
  ·
    refine ⟨82622853142900725945517793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55081902095267150630345195 82622853142900725945517793)
    ·
      refine ⟨61967139857175544459138345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82622853142900725945517793 61967139857175544459138345)
      ·
        refine ⟨46475354892881658344353759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61967139857175544459138345 46475354892881658344353759)
        ·
          refine ⟨69713032339322487516530639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46475354892881658344353759 69713032339322487516530639)
          ·
            refine ⟨104569548508983731274795959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69713032339322487516530639 104569548508983731274795959)
            ·
              refine ⟨156854322763475596912193939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104569548508983731274795959 156854322763475596912193939)
              ·
                refine ⟨235281484145213395368290909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156854322763475596912193939 235281484145213395368290909)
                ·
                  refine ⟨88230556554455023263109091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235281484145213395368290909 88230556554455023263109091)
                  ·
                    refine ⟨132345834831682534894663637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88230556554455023263109091 132345834831682534894663637)
                    ·
                      refine ⟨3101855503867559411593679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132345834831682534894663637 3101855503867559411593679)
                      ·
                        rfl

theorem cell23_6040842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_6040842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040842 prefixEnd_6040842 := by exact prefixLift 6040842
  have htrace : WordTrace (prefixWord ++ tailWord_6040842) baseStart_6040842 baseEnd_6040842 := by
    simpa [prefixWord, tailWord_6040842, baseEnd_6040842] using wordTrace_append hprefix tailTrace_6040842
  have hstable : (prefixWord ++ tailWord_6040842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040842).length < 2 ^ (prefixWord ++ tailWord_6040842).sum := by decide
  have hdescent : baseEnd_6040842 < baseStart_6040842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040849 : List Nat := [1, 2, 2, 1, 1, 4, 4, 1, 2, 5]
def baseStart_6040849 : Nat := 118140960795 + 6040849 * 2 ^ 59
def prefixEnd_6040849 : Nat := 4983230072969 + 3 ^ 40 * 6040849 * 2
def baseEnd_6040849 : Nat := 1033953032744046961402049

theorem tailTrace_6040849 : CollatzResearch.WordTrace tailWord_6040849 prefixEnd_6040849 1033953032744046961402049 := by
  unfold tailWord_6040849
  simp only [CollatzResearch.WordTrace]
  refine ⟨220327863692043242716885601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146885242461362161811257067 220327863692043242716885601)
  ·
    refine ⟨165245897769032432037664201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220327863692043242716885601 165245897769032432037664201)
    ·
      refine ⟨123934423326774324028248151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165245897769032432037664201 123934423326774324028248151)
      ·
        refine ⟨185901634990161486042372227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123934423326774324028248151 185901634990161486042372227)
        ·
          refine ⟨278852452485242229063558341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185901634990161486042372227 278852452485242229063558341)
          ·
            refine ⟨52284834840982917949417189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278852452485242229063558341 52284834840982917949417189)
            ·
              refine ⟨9803406532684297115515723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52284834840982917949417189 9803406532684297115515723)
              ·
                refine ⟨14705109799026445673273585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9803406532684297115515723 14705109799026445673273585)
                ·
                  refine ⟨11028832349269834254955189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14705109799026445673273585 11028832349269834254955189)
                  ·
                    refine ⟨1033953032744046961402049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11028832349269834254955189 1033953032744046961402049)
                    ·
                      rfl

theorem cell23_6040849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_6040849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040849 prefixEnd_6040849 := by exact prefixLift 6040849
  have htrace : WordTrace (prefixWord ++ tailWord_6040849) baseStart_6040849 baseEnd_6040849 := by
    simpa [prefixWord, tailWord_6040849, baseEnd_6040849] using wordTrace_append hprefix tailTrace_6040849
  have hstable : (prefixWord ++ tailWord_6040849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040849).length < 2 ^ (prefixWord ++ tailWord_6040849).sum := by decide
  have hdescent : baseEnd_6040849 < baseStart_6040849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040879 : List Nat := [1, 1, 2, 1, 2, 1, 3, 5, 3, 4]
def baseStart_6040879 : Nat := 118140960795 + 6040879 * 2 ^ 59
def prefixEnd_6040879 : Nat := 4983230072969 + 3 ^ 40 * 6040879 * 2
def baseEnd_6040879 : Nat := 1033958167550591922277003

theorem tailTrace_6040879 : CollatzResearch.WordTrace tailWord_6040879 prefixEnd_6040879 1033958167550591922277003 := by
  unfold tailWord_6040879
  simp only [CollatzResearch.WordTrace]
  refine ⟨220328957881934557840477691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146885971921289705226985127 220328957881934557840477691)
  ·
    refine ⟨330493436822901836760716537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220328957881934557840477691 330493436822901836760716537)
    ·
      refine ⟨247870077617176377570537403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330493436822901836760716537 247870077617176377570537403)
      ·
        refine ⟨371805116425764566355806105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247870077617176377570537403 371805116425764566355806105)
        ·
          refine ⟨278853837319323424766854579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371805116425764566355806105 278853837319323424766854579)
          ·
            refine ⟨418280755978985137150281869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278853837319323424766854579 418280755978985137150281869)
            ·
              refine ⟨156855283492119426431355701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 418280755978985137150281869 156855283492119426431355701)
              ·
                refine ⟨14705182827386196227939597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156855283492119426431355701 14705182827386196227939597)
                ·
                  refine ⟨5514443560269823585477349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14705182827386196227939597 5514443560269823585477349)
                  ·
                    refine ⟨1033958167550591922277003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5514443560269823585477349 1033958167550591922277003)
                    ·
                      rfl

theorem cell23_6040879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 4].length) (baseStart_6040879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040879 prefixEnd_6040879 := by exact prefixLift 6040879
  have htrace : WordTrace (prefixWord ++ tailWord_6040879) baseStart_6040879 baseEnd_6040879 := by
    simpa [prefixWord, tailWord_6040879, baseEnd_6040879] using wordTrace_append hprefix tailTrace_6040879
  have hstable : (prefixWord ++ tailWord_6040879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040879).length < 2 ^ (prefixWord ++ tailWord_6040879).sum := by decide
  have hdescent : baseEnd_6040879 < baseStart_6040879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040913 : List Nat := [1, 2, 2, 1, 4, 1, 4, 3, 1, 4]
def baseStart_6040913 : Nat := 118140960795 + 6040913 * 2 ^ 59
def prefixEnd_6040913 : Nat := 4983230072969 + 3 ^ 40 * 6040913 * 2
def baseEnd_6040913 : Nat := 1033963986998009544601951

theorem tailTrace_6040913 : CollatzResearch.WordTrace tailWord_6040913 prefixEnd_6040913 1033963986998009544601951 := by
  unfold tailWord_6040913
  simp only [CollatzResearch.WordTrace]
  refine ⟨220330197963811381647215393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146886798642540921098143595 220330197963811381647215393)
  ·
    refine ⟨165247648472858536235411545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220330197963811381647215393 165247648472858536235411545)
    ·
      refine ⟨123935736354643902176558659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165247648472858536235411545 123935736354643902176558659)
      ·
        refine ⟨185903604531965853264837989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123935736354643902176558659 185903604531965853264837989)
        ·
          refine ⟨34856925849743597487157123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185903604531965853264837989 34856925849743597487157123)
          ·
            refine ⟨52285388774615396230735685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34856925849743597487157123 52285388774615396230735685)
            ·
              refine ⟨9803510395240386793262941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52285388774615396230735685 9803510395240386793262941)
              ·
                refine ⟨3676316398215145047473603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9803510395240386793262941 3676316398215145047473603)
                ·
                  refine ⟨5514474597322717571210405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3676316398215145047473603 5514474597322717571210405)
                  ·
                    refine ⟨1033963986998009544601951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5514474597322717571210405 1033963986998009544601951)
                    ·
                      rfl

theorem cell23_6040913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_6040913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040913 prefixEnd_6040913 := by exact prefixLift 6040913
  have htrace : WordTrace (prefixWord ++ tailWord_6040913) baseStart_6040913 baseEnd_6040913 := by
    simpa [prefixWord, tailWord_6040913, baseEnd_6040913] using wordTrace_append hprefix tailTrace_6040913
  have hstable : (prefixWord ++ tailWord_6040913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040913).length < 2 ^ (prefixWord ++ tailWord_6040913).sum := by decide
  have hdescent : baseEnd_6040913 < baseStart_6040913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040946 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 3, 5, 2]
def baseStart_6040946 : Nat := 118140960795 + 6040946 * 2 ^ 59
def prefixEnd_6040946 : Nat := 4983230072969 + 3 ^ 40 * 6040946 * 2
def baseEnd_6040946 : Nat := 3101908905855627004693201

theorem tailTrace_6040946 : CollatzResearch.WordTrace tailWord_6040946 prefixEnd_6040946 3101908905855627004693201 := by
  unfold tailWord_6040946
  simp only [CollatzResearch.WordTrace]
  refine ⟨55082850393172957070791673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146887601048461218855444461 55082850393172957070791673)
  ·
    refine ⟨41312137794879717803093755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55082850393172957070791673 41312137794879717803093755)
    ·
      refine ⟨61968206692319576704640633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41312137794879717803093755 61968206692319576704640633)
      ·
        refine ⟨46476155019239682528480475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61968206692319576704640633 46476155019239682528480475)
        ·
          refine ⟨69714232528859523792720713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46476155019239682528480475 69714232528859523792720713)
          ·
            refine ⟨52285674396644642844540535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69714232528859523792720713 52285674396644642844540535)
            ·
              refine ⟨78428511594966964266810803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52285674396644642844540535 78428511594966964266810803)
              ·
                refine ⟨117642767392450446400216205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78428511594966964266810803 117642767392450446400216205)
                ·
                  refine ⟨44116037772168917400081077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 117642767392450446400216205 44116037772168917400081077)
                  ·
                    refine ⟨4135878541140836006257601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44116037772168917400081077 4135878541140836006257601)
                    ·
                      refine ⟨3101908905855627004693201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135878541140836006257601 3101908905855627004693201)
                      ·
                        rfl

theorem cell23_6040946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_6040946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040946 prefixEnd_6040946 := by exact prefixLift 6040946
  have htrace : WordTrace (prefixWord ++ tailWord_6040946) baseStart_6040946 baseEnd_6040946 := by
    simpa [prefixWord, tailWord_6040946, baseEnd_6040946] using wordTrace_append hprefix tailTrace_6040946
  have hstable : (prefixWord ++ tailWord_6040946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040946).length < 2 ^ (prefixWord ++ tailWord_6040946).sum := by decide
  have hdescent : baseEnd_6040946 < baseStart_6040946 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040956 : List Nat := [2, 2, 2, 1, 1, 1, 6, 2, 1, 5]
def baseStart_6040956 : Nat := 118140960795 + 6040956 * 2 ^ 59
def prefixEnd_6040956 : Nat := 4983230072969 + 3 ^ 40 * 6040956 * 2
def baseEnd_6040956 : Nat := 1033971346887390655189385

theorem tailTrace_6040956 : CollatzResearch.WordTrace tailWord_6040956 prefixEnd_6040956 1033971346887390655189385 := by
  unfold tailWord_6040956
  simp only [CollatzResearch.WordTrace]
  refine ⟨110165883151327799995515361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146887844201770399994020481 110165883151327799995515361)
  ·
    refine ⟨82624412363495849996636521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110165883151327799995515361 82624412363495849996636521)
    ·
      refine ⟨61968309272621887497477391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82624412363495849996636521 61968309272621887497477391)
      ·
        refine ⟨92952463908932831246216087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61968309272621887497477391 92952463908932831246216087)
        ·
          refine ⟨139428695863399246869324131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92952463908932831246216087 139428695863399246869324131)
          ·
            refine ⟨209143043795098870303986197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139428695863399246869324131 209143043795098870303986197)
            ·
              refine ⟨9803580177895259545499353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 209143043795098870303986197 9803580177895259545499353)
              ·
                refine ⟨7352685133421444659124515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9803580177895259545499353 7352685133421444659124515)
                ·
                  refine ⟨11029027700132166988686773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7352685133421444659124515 11029027700132166988686773)
                  ·
                    refine ⟨1033971346887390655189385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11029027700132166988686773 1033971346887390655189385)
                    ·
                      rfl

theorem cell23_6040956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_6040956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040956 prefixEnd_6040956 := by exact prefixLift 6040956
  have htrace : WordTrace (prefixWord ++ tailWord_6040956) baseStart_6040956 baseEnd_6040956 := by
    simpa [prefixWord, tailWord_6040956, baseEnd_6040956] using wordTrace_append hprefix tailTrace_6040956
  have hstable : (prefixWord ++ tailWord_6040956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040956).length < 2 ^ (prefixWord ++ tailWord_6040956).sum := by decide
  have hdescent : baseEnd_6040956 < baseStart_6040956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040980 : List Nat := [2, 4, 2, 1, 2, 2, 1, 2, 2, 3, 2]
def baseStart_6040980 : Nat := 118140960795 + 6040980 * 2 ^ 59
def prefixEnd_6040980 : Nat := 4983230072969 + 3 ^ 40 * 6040980 * 2
def baseEnd_6040980 : Nat := 3101926364197879871668045

theorem tailTrace_6040980 : CollatzResearch.WordTrace tailWord_6040980 prefixEnd_6040980 3101926364197879871668045 := by
  unfold tailWord_6040980
  simp only [CollatzResearch.WordTrace]
  refine ⟨110166320827284326044952197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146888427769712434726602929 110166320827284326044952197)
  ·
    refine ⟨20656185155115811133428537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110166320827284326044952197 20656185155115811133428537)
    ·
      refine ⟨15492138866336858350071403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20656185155115811133428537 15492138866336858350071403)
      ·
        refine ⟨23238208299505287525107105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15492138866336858350071403 23238208299505287525107105)
        ·
          refine ⟨17428656224628965643830329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23238208299505287525107105 17428656224628965643830329)
          ·
            refine ⟨13071492168471724232872747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17428656224628965643830329 13071492168471724232872747)
            ·
              refine ⟨19607238252707586349309121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13071492168471724232872747 19607238252707586349309121)
              ·
                refine ⟨14705428689530689761981841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19607238252707586349309121 14705428689530689761981841)
                ·
                  refine ⟨11029071517148017321486381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14705428689530689761981841 11029071517148017321486381)
                  ·
                    refine ⟨4135901818930506495557393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11029071517148017321486381 4135901818930506495557393)
                    ·
                      refine ⟨3101926364197879871668045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135901818930506495557393 3101926364197879871668045)
                      ·
                        rfl

theorem cell23_6040980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_6040980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040980 prefixEnd_6040980 := by exact prefixLift 6040980
  have htrace : WordTrace (prefixWord ++ tailWord_6040980) baseStart_6040980 baseEnd_6040980 := by
    simpa [prefixWord, tailWord_6040980, baseEnd_6040980] using wordTrace_append hprefix tailTrace_6040980
  have hstable : (prefixWord ++ tailWord_6040980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040980).length < 2 ^ (prefixWord ++ tailWord_6040980).sum := by decide
  have hdescent : baseEnd_6040980 < baseStart_6040980 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040986 : List Nat := [3, 1, 1, 4, 1, 1, 1, 3, 4, 4]
def baseStart_6040986 : Nat := 118140960795 + 6040986 * 2 ^ 59
def prefixEnd_6040986 : Nat := 4983230072969 + 3 ^ 40 * 6040986 * 2
def baseEnd_6040986 : Nat := 1033976481693935616064339

theorem tailTrace_6040986 : CollatzResearch.WordTrace tailWord_6040986 prefixEnd_6040986 1033976481693935616064339 := by
  unfold tailWord_6040986
  simp only [CollatzResearch.WordTrace]
  refine ⟨55083215123136728778655703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146888573661697943409748541 55083215123136728778655703)
  ·
    refine ⟨82624822684705093167983555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55083215123136728778655703 82624822684705093167983555)
    ·
      refine ⟨123937234027057639751975333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82624822684705093167983555 123937234027057639751975333)
      ·
        refine ⟨23238231380073307453495375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123937234027057639751975333 23238231380073307453495375)
        ·
          refine ⟨34857347070109961180243063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23238231380073307453495375 34857347070109961180243063)
          ·
            refine ⟨52286020605164941770364595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34857347070109961180243063 52286020605164941770364595)
            ·
              refine ⟨78429030907747412655546893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52286020605164941770364595 78429030907747412655546893)
              ·
                refine ⟨29410886590405279745830085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78429030907747412655546893 29410886590405279745830085)
                ·
                  refine ⟨5514541235700989952343141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29410886590405279745830085 5514541235700989952343141)
                  ·
                    refine ⟨1033976481693935616064339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5514541235700989952343141 1033976481693935616064339)
                    ·
                      rfl

theorem cell23_6040986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_6040986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040986 prefixEnd_6040986 := by exact prefixLift 6040986
  have htrace : WordTrace (prefixWord ++ tailWord_6040986) baseStart_6040986 baseEnd_6040986 := by
    simpa [prefixWord, tailWord_6040986, baseEnd_6040986] using wordTrace_append hprefix tailTrace_6040986
  have hstable : (prefixWord ++ tailWord_6040986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040986).length < 2 ^ (prefixWord ++ tailWord_6040986).sum := by decide
  have hdescent : baseEnd_6040986 < baseStart_6040986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6040996 : List Nat := [2, 3, 1, 2, 1, 1, 1, 4, 3, 2, 3]
def baseStart_6040996 : Nat := 118140960795 + 6040996 * 2 ^ 59
def prefixEnd_6040996 : Nat := 4983230072969 + 3 ^ 40 * 6040996 * 2
def baseEnd_6040996 : Nat := 3101934579888351809067971

theorem tailTrace_6040996 : CollatzResearch.WordTrace tailWord_6040996 prefixEnd_6040996 3101934579888351809067971 := by
  unfold tailWord_6040996
  simp only [CollatzResearch.WordTrace]
  refine ⟨110166612611255343411243421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146888816815007124548324561 110166612611255343411243421)
  ·
    refine ⟨41312479729220753779216283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110166612611255343411243421 41312479729220753779216283)
    ·
      refine ⟨61968719593831130668824425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41312479729220753779216283 61968719593831130668824425)
      ·
        refine ⟨46476539695373348001618319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61968719593831130668824425 46476539695373348001618319)
        ·
          refine ⟨69714809543060022002427479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46476539695373348001618319 69714809543060022002427479)
          ·
            refine ⟨104572214314590033003641219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69714809543060022002427479 104572214314590033003641219)
            ·
              refine ⟨156858321471885049505461829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104572214314590033003641219 156858321471885049505461829)
              ·
                refine ⟨29410935275978446782274093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156858321471885049505461829 29410935275978446782274093)
                ·
                  refine ⟨11029100728491917543352785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29410935275978446782274093 11029100728491917543352785)
                  ·
                    refine ⟨8271825546368938157514589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11029100728491917543352785 8271825546368938157514589)
                    ·
                      refine ⟨3101934579888351809067971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8271825546368938157514589 3101934579888351809067971)
                      ·
                        rfl

theorem cell23_6040996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_6040996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6040996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6040996 prefixEnd_6040996 := by exact prefixLift 6040996
  have htrace : WordTrace (prefixWord ++ tailWord_6040996) baseStart_6040996 baseEnd_6040996 := by
    simpa [prefixWord, tailWord_6040996, baseEnd_6040996] using wordTrace_append hprefix tailTrace_6040996
  have hstable : (prefixWord ++ tailWord_6040996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6040996).length < 2 ^ (prefixWord ++ tailWord_6040996).sum := by decide
  have hdescent : baseEnd_6040996 < baseStart_6040996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6040996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041013 : List Nat := [1, 3, 3, 2, 2, 2, 1, 1, 3, 2, 3]
def baseStart_6041013 : Nat := 118140960795 + 6041013 * 2 ^ 59
def prefixEnd_6041013 : Nat := 4983230072969 + 3 ^ 40 * 6041013 * 2
def baseEnd_6041013 : Nat := 3101943309059478242555393

theorem tailTrace_6041013 : CollatzResearch.WordTrace tailWord_6041013 prefixEnd_6041013 3101943309059478242555393 := by
  unfold tailWord_6041013
  simp only [CollatzResearch.WordTrace]
  refine ⟨220333845263449098725855693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146889230175632732483903795 220333845263449098725855693)
  ·
    refine ⟨82625191973793412022195885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220333845263449098725855693 82625191973793412022195885)
    ·
      refine ⟨30984446990172529508323457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82625191973793412022195885 30984446990172529508323457)
      ·
        refine ⟨23238335242629397131242593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30984446990172529508323457 23238335242629397131242593)
        ·
          refine ⟨17428751431972047848431945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23238335242629397131242593 17428751431972047848431945)
          ·
            refine ⟨13071563573979035886323959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17428751431972047848431945 13071563573979035886323959)
            ·
              refine ⟨19607345360968553829485939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13071563573979035886323959 19607345360968553829485939)
              ·
                refine ⟨29411018041452830744228909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19607345360968553829485939 29411018041452830744228909)
                ·
                  refine ⟨11029131765544811529085841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29411018041452830744228909 11029131765544811529085841)
                  ·
                    refine ⟨8271848824158608646814381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11029131765544811529085841 8271848824158608646814381)
                    ·
                      refine ⟨3101943309059478242555393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8271848824158608646814381 3101943309059478242555393)
                      ·
                        rfl

theorem cell23_6041013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_6041013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041013 prefixEnd_6041013 := by exact prefixLift 6041013
  have htrace : WordTrace (prefixWord ++ tailWord_6041013) baseStart_6041013 baseEnd_6041013 := by
    simpa [prefixWord, tailWord_6041013, baseEnd_6041013] using wordTrace_append hprefix tailTrace_6041013
  have hstable : (prefixWord ++ tailWord_6041013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041013).length < 2 ^ (prefixWord ++ tailWord_6041013).sum := by decide
  have hdescent : baseEnd_6041013 < baseStart_6041013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041039 : List Nat := [1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 5]
def baseStart_6041039 : Nat := 118140960795 + 6041039 * 2 ^ 59
def prefixEnd_6041039 : Nat := 4983230072969 + 3 ^ 40 * 6041039 * 2
def baseEnd_6041039 : Nat := 3101956659556495140830273

theorem tailTrace_6041039 : CollatzResearch.WordTrace tailWord_6041039 prefixEnd_6041039 3101956659556495140830273 := by
  unfold tailWord_6041039
  simp only [CollatzResearch.WordTrace]
  refine ⟨220334793561354905166302171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146889862374236603444201447 220334793561354905166302171)
  ·
    refine ⟨330502190342032357749453257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220334793561354905166302171 330502190342032357749453257)
    ·
      refine ⟨247876642756524268312089943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330502190342032357749453257 247876642756524268312089943)
      ·
        refine ⟨371814964134786402468134915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247876642756524268312089943 371814964134786402468134915)
        ·
          refine ⟨557722446202179603702202373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371814964134786402468134915 557722446202179603702202373)
          ·
            refine ⟨104572958662908675694162945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 557722446202179603702202373 104572958662908675694162945)
            ·
              refine ⟨78429718997181506770622209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104572958662908675694162945 78429718997181506770622209)
              ·
                refine ⟨58822289247886130077966657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78429718997181506770622209 58822289247886130077966657)
                ·
                  refine ⟨44116716935914597558474993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58822289247886130077966657 44116716935914597558474993)
                  ·
                    refine ⟨33087537701935948168856245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44116716935914597558474993 33087537701935948168856245)
                    ·
                      refine ⟨3101956659556495140830273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33087537701935948168856245 3101956659556495140830273)
                      ·
                        rfl

theorem cell23_6041039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 2, 5].length) (baseStart_6041039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041039 prefixEnd_6041039 := by exact prefixLift 6041039
  have htrace : WordTrace (prefixWord ++ tailWord_6041039) baseStart_6041039 baseEnd_6041039 := by
    simpa [prefixWord, tailWord_6041039, baseEnd_6041039] using wordTrace_append hprefix tailTrace_6041039
  have hstable : (prefixWord ++ tailWord_6041039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041039).length < 2 ^ (prefixWord ++ tailWord_6041039).sum := by decide
  have hdescent : baseEnd_6041039 < baseStart_6041039 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041044 : List Nat := [2, 4, 1, 2, 3, 1, 1, 4, 1, 2, 2]
def baseStart_6041044 : Nat := 118140960795 + 6041044 * 2 ^ 59
def prefixEnd_6041044 : Nat := 4983230072969 + 3 ^ 40 * 6041044 * 2
def baseEnd_6041044 : Nat := 3101959226959767621267751

theorem tailTrace_6041044 : CollatzResearch.WordTrace tailWord_6041044 prefixEnd_6041044 3101959226959767621267751 := by
  unfold tailWord_6041044
  simp only [CollatzResearch.WordTrace]
  refine ⟨110167487963168395510117093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146889983950891194013489457 110167487963168395510117093)
  ·
    refine ⟨20656403993094074158146955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 110167487963168395510117093 20656403993094074158146955)
    ·
      refine ⟨30984605989641111237220433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20656403993094074158146955 30984605989641111237220433)
      ·
        refine ⟨23238454492230833427915325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30984605989641111237220433 23238454492230833427915325)
        ·
          refine ⟨8714420434586562535468247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23238454492230833427915325 8714420434586562535468247)
          ·
            refine ⟨13071630651879843803202371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8714420434586562535468247 13071630651879843803202371)
            ·
              refine ⟨19607445977819765704803557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13071630651879843803202371 19607445977819765704803557)
              ·
                refine ⟨3676396120841206069650667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19607445977819765704803557 3676396120841206069650667)
                ·
                  refine ⟨5514594181261809104476001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3676396120841206069650667 5514594181261809104476001)
                  ·
                    refine ⟨4135945635946356828357001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5514594181261809104476001 4135945635946356828357001)
                    ·
                      refine ⟨3101959226959767621267751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135945635946356828357001 3101959226959767621267751)
                      ·
                        rfl

theorem cell23_6041044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_6041044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041044 prefixEnd_6041044 := by exact prefixLift 6041044
  have htrace : WordTrace (prefixWord ++ tailWord_6041044) baseStart_6041044 baseEnd_6041044 := by
    simpa [prefixWord, tailWord_6041044, baseEnd_6041044] using wordTrace_append hprefix tailTrace_6041044
  have hstable : (prefixWord ++ tailWord_6041044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041044).length < 2 ^ (prefixWord ++ tailWord_6041044).sum := by decide
  have hdescent : baseEnd_6041044 < baseStart_6041044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041070 : List Nat := [4, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2]
def baseStart_6041070 : Nat := 118140960795 + 6041070 * 2 ^ 59
def prefixEnd_6041070 : Nat := 4983230072969 + 3 ^ 40 * 6041070 * 2
def baseEnd_6041070 : Nat := 3101972577456784519542631

theorem tailTrace_6041070 : CollatzResearch.WordTrace tailWord_6041070 prefixEnd_6041070 3101972577456784519542631 := by
  unfold tailWord_6041070
  simp only [CollatzResearch.WordTrace]
  refine ⟨27541990528030324682585083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146890616149495064973787109 27541990528030324682585083)
  ·
    refine ⟨41312985792045487023877625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27541990528030324682585083 41312985792045487023877625)
    ·
      refine ⟨30984739344034115267908219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41312985792045487023877625 30984739344034115267908219)
      ·
        refine ⟨46477109016051172901862329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30984739344034115267908219 46477109016051172901862329)
        ·
          refine ⟨34857831762038379676396747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46477109016051172901862329 34857831762038379676396747)
          ·
            refine ⟨52286747643057569514595121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34857831762038379676396747 52286747643057569514595121)
            ·
              refine ⟨39215060732293177135946341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52286747643057569514595121 39215060732293177135946341)
              ·
                refine ⟨7352823887304970712989939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39215060732293177135946341 7352823887304970712989939)
                ·
                  refine ⟨11029235830957456069484909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7352823887304970712989939 11029235830957456069484909)
                  ·
                    refine ⟨4135963436609046026056841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11029235830957456069484909 4135963436609046026056841)
                    ·
                      refine ⟨3101972577456784519542631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135963436609046026056841 3101972577456784519542631)
                      ·
                        rfl

theorem cell23_6041070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_6041070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041070 prefixEnd_6041070 := by exact prefixLift 6041070
  have htrace : WordTrace (prefixWord ++ tailWord_6041070) baseStart_6041070 baseEnd_6041070 := by
    simpa [prefixWord, tailWord_6041070, baseEnd_6041070] using wordTrace_append hprefix tailTrace_6041070
  have hstable : (prefixWord ++ tailWord_6041070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041070).length < 2 ^ (prefixWord ++ tailWord_6041070).sum := by decide
  have hdescent : baseEnd_6041070 < baseStart_6041070 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041083 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 6, 2, 2]
def baseStart_6041083 : Nat := 118140960795 + 6041083 * 2 ^ 59
def prefixEnd_6041083 : Nat := 4983230072969 + 3 ^ 40 * 6041083 * 2
def baseEnd_6041083 : Nat := 3101979252705292968680071

theorem tailTrace_6041083 : CollatzResearch.WordTrace tailWord_6041083 prefixEnd_6041083 3101979252705292968680071 := by
  unfold tailWord_6041083
  simp only [CollatzResearch.WordTrace]
  refine ⟨220336398373195500680903903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146890932248797000453935935 220336398373195500680903903)
  ·
    refine ⟨330504597559793251021355855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220336398373195500680903903 330504597559793251021355855)
    ·
      refine ⟨495756896339689876532033783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330504597559793251021355855 495756896339689876532033783)
      ·
        refine ⟨743635344509534814798050675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495756896339689876532033783 743635344509534814798050675)
        ·
          refine ⟨1115453016764302222197076013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743635344509534814798050675 1115453016764302222197076013)
          ·
            refine ⟨418294881286613333323903505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1115453016764302222197076013 418294881286613333323903505)
            ·
              refine ⟨313721160964959999992927629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418294881286613333323903505 313721160964959999992927629)
              ·
                refine ⟨117645435361859999997347861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 313721160964959999992927629 117645435361859999997347861)
                ·
                  refine ⟨5514629782587187499875681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117645435361859999997347861 5514629782587187499875681)
                  ·
                    refine ⟨4135972336940390624906761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5514629782587187499875681 4135972336940390624906761)
                    ·
                      refine ⟨3101979252705292968680071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4135972336940390624906761 3101979252705292968680071)
                      ·
                        rfl

theorem cell23_6041083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 6, 2, 2].length) (baseStart_6041083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041083 prefixEnd_6041083 := by exact prefixLift 6041083
  have htrace : WordTrace (prefixWord ++ tailWord_6041083) baseStart_6041083 baseEnd_6041083 := by
    simpa [prefixWord, tailWord_6041083, baseEnd_6041083] using wordTrace_append hprefix tailTrace_6041083
  have hstable : (prefixWord ++ tailWord_6041083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041083).length < 2 ^ (prefixWord ++ tailWord_6041083).sum := by decide
  have hdescent : baseEnd_6041083 < baseStart_6041083 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041096 : List Nat := [2, 1, 3, 2, 1, 1, 3, 2, 2, 2, 4]
def baseStart_6041096 : Nat := 118140960795 + 6041096 * 2 ^ 59
def prefixEnd_6041096 : Nat := 4983230072969 + 3 ^ 40 * 6041096 * 2
def baseEnd_6041096 : Nat := 3101985927953801417817511

theorem tailTrace_6041096 : CollatzResearch.WordTrace tailWord_6041096 prefixEnd_6041096 3101985927953801417817511 := by
  unfold tailWord_6041096
  simp only [CollatzResearch.WordTrace]
  refine ⟨110168436261074201950563571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146891248348098935934084761 110168436261074201950563571)
  ·
    refine ⟨165252654391611302925845357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110168436261074201950563571 165252654391611302925845357)
    ·
      refine ⟨61969745396854238597192009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165252654391611302925845357 61969745396854238597192009)
      ·
        refine ⟨46477309047640678947894007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61969745396854238597192009 46477309047640678947894007)
        ·
          refine ⟨69715963571461018421841011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46477309047640678947894007 69715963571461018421841011)
          ·
            refine ⟨104573945357191527632761517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69715963571461018421841011 104573945357191527632761517)
            ·
              refine ⟨39215229508946822862285569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104573945357191527632761517 39215229508946822862285569)
              ·
                refine ⟨29411422131710117146714177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39215229508946822862285569 29411422131710117146714177)
                ·
                  refine ⟨22058566598782587860035633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29411422131710117146714177 22058566598782587860035633)
                  ·
                    refine ⟨16543924949086940895026725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22058566598782587860035633 16543924949086940895026725)
                    ·
                      refine ⟨3101985927953801417817511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16543924949086940895026725 3101985927953801417817511)
                      ·
                        rfl

theorem cell23_6041096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_6041096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041096 prefixEnd_6041096 := by exact prefixLift 6041096
  have htrace : WordTrace (prefixWord ++ tailWord_6041096) baseStart_6041096 baseEnd_6041096 := by
    simpa [prefixWord, tailWord_6041096, baseEnd_6041096] using wordTrace_append hprefix tailTrace_6041096
  have hstable : (prefixWord ++ tailWord_6041096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041096).length < 2 ^ (prefixWord ++ tailWord_6041096).sum := by decide
  have hdescent : baseEnd_6041096 < baseStart_6041096 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041136 : List Nat := [2, 1, 1, 1, 2, 3, 1, 5, 2, 5]
def baseStart_6041136 : Nat := 118140960795 + 6041136 * 2 ^ 59
def prefixEnd_6041136 : Nat := 4983230072969 + 3 ^ 40 * 6041136 * 2
def baseEnd_6041136 : Nat := 1034002155726660420439109

theorem tailTrace_6041136 : CollatzResearch.WordTrace tailWord_6041136 prefixEnd_6041136 1034002155726660420439109 := by
  unfold tailWord_6041136
  simp only [CollatzResearch.WordTrace]
  refine ⟨110169165721001745366291631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146892220961335660488388841 110169165721001745366291631)
  ·
    refine ⟨165253748581502618049437447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110169165721001745366291631 165253748581502618049437447)
    ·
      refine ⟨247880622872253927074156171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165253748581502618049437447 247880622872253927074156171)
      ·
        refine ⟨371820934308380890611234257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247880622872253927074156171 371820934308380890611234257)
        ·
          refine ⟨278865700731285667958425693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371820934308380890611234257 278865700731285667958425693)
          ·
            refine ⟨104574637774232125484409635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278865700731285667958425693 104574637774232125484409635)
            ·
              refine ⟨156861956661348188226614453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104574637774232125484409635 156861956661348188226614453)
              ·
                refine ⟨14705808437001392646245105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156861956661348188226614453 14705808437001392646245105)
                ·
                  refine ⟨11029356327751044484683829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14705808437001392646245105 11029356327751044484683829)
                  ·
                    refine ⟨1034002155726660420439109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11029356327751044484683829 1034002155726660420439109)
                    ·
                      rfl

theorem cell23_6041136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 5, 2, 5].length) (baseStart_6041136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041136 prefixEnd_6041136 := by exact prefixLift 6041136
  have htrace : WordTrace (prefixWord ++ tailWord_6041136) baseStart_6041136 baseEnd_6041136 := by
    simpa [prefixWord, tailWord_6041136, baseEnd_6041136] using wordTrace_append hprefix tailTrace_6041136
  have hstable : (prefixWord ++ tailWord_6041136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041136).length < 2 ^ (prefixWord ++ tailWord_6041136).sum := by decide
  have hdescent : baseEnd_6041136 < baseStart_6041136 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041146 : List Nat := [3, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5]
def baseStart_6041146 : Nat := 118140960795 + 6041146 * 2 ^ 59
def prefixEnd_6041146 : Nat := 4983230072969 + 3 ^ 40 * 6041146 * 2
def baseEnd_6041146 : Nat := 3102011601986526222192281

theorem tailTrace_6041146 : CollatzResearch.WordTrace tailWord_6041146 prefixEnd_6041146 3102011601986526222192281 := by
  unfold tailWord_6041146
  simp only [CollatzResearch.WordTrace]
  refine ⟨55084674042991815610111823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146892464114644841626964861 55084674042991815610111823)
  ·
    refine ⟨82627011064487723415167735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55084674042991815610111823 82627011064487723415167735)
    ·
      refine ⟨123940516596731585122751603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82627011064487723415167735 123940516596731585122751603)
      ·
        refine ⟨185910774895097377684127405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123940516596731585122751603 185910774895097377684127405)
        ·
          refine ⟨69716540585661516631547777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185910774895097377684127405 69716540585661516631547777)
          ·
            refine ⟨52287405439246137473660833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69716540585661516631547777 52287405439246137473660833)
            ·
              refine ⟨39215554079434603105245625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52287405439246137473660833 39215554079434603105245625)
              ·
                refine ⟨29411665559575952328934219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39215554079434603105245625 29411665559575952328934219)
                ·
                  refine ⟨44117498339363928493401329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29411665559575952328934219 44117498339363928493401329)
                  ·
                    refine ⟨33088123754522946370050997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44117498339363928493401329 33088123754522946370050997)
                    ·
                      refine ⟨3102011601986526222192281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33088123754522946370050997 3102011601986526222192281)
                      ·
                        rfl

theorem cell23_6041146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 2, 1, 2, 5].length) (baseStart_6041146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041146 prefixEnd_6041146 := by exact prefixLift 6041146
  have htrace : WordTrace (prefixWord ++ tailWord_6041146) baseStart_6041146 baseEnd_6041146 := by
    simpa [prefixWord, tailWord_6041146, baseEnd_6041146] using wordTrace_append hprefix tailTrace_6041146
  have hstable : (prefixWord ++ tailWord_6041146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041146).length < 2 ^ (prefixWord ++ tailWord_6041146).sum := by decide
  have hdescent : baseEnd_6041146 < baseStart_6041146 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041153 : List Nat := [1, 2, 5, 1, 1, 1, 3, 2, 2, 5]
def baseStart_6041153 : Nat := 118140960795 + 6041153 * 2 ^ 59
def prefixEnd_6041153 : Nat := 4983230072969 + 3 ^ 40 * 6041153 * 2
def baseEnd_6041153 : Nat := 1034005065450369231601583

theorem tailTrace_6041153 : CollatzResearch.WordTrace tailWord_6041153 prefixEnd_6041153 1034005065450369231601583 := by
  unfold tailWord_6041153
  simp only [CollatzResearch.WordTrace]
  refine ⟨220338951482941902635952113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146892634321961268423968075 220338951482941902635952113)
  ·
    refine ⟨165254213612206426976964085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220338951482941902635952113 165254213612206426976964085)
    ·
      refine ⟨15492582526144352529090383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165254213612206426976964085 15492582526144352529090383)
      ·
        refine ⟨23238873789216528793635575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15492582526144352529090383 23238873789216528793635575)
        ·
          refine ⟨34858310683824793190453363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23238873789216528793635575 34858310683824793190453363)
          ·
            refine ⟨52287466025737189785680045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34858310683824793190453363 52287466025737189785680045)
            ·
              refine ⟨19607799759651446169630017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52287466025737189785680045 19607799759651446169630017)
              ·
                refine ⟨14705849819738584627222513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19607799759651446169630017 14705849819738584627222513)
                ·
                  refine ⟨11029387364803938470416885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14705849819738584627222513 11029387364803938470416885)
                  ·
                    refine ⟨1034005065450369231601583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11029387364803938470416885 1034005065450369231601583)
                    ·
                      rfl

theorem cell23_6041153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_6041153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041153 prefixEnd_6041153 := by exact prefixLift 6041153
  have htrace : WordTrace (prefixWord ++ tailWord_6041153) baseStart_6041153 baseEnd_6041153 := by
    simpa [prefixWord, tailWord_6041153, baseEnd_6041153] using wordTrace_append hprefix tailTrace_6041153
  have hstable : (prefixWord ++ tailWord_6041153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041153).length < 2 ^ (prefixWord ++ tailWord_6041153).sum := by decide
  have hdescent : baseEnd_6041153 < baseStart_6041153 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041173 : List Nat := [1, 3, 2, 2, 1, 1, 1, 3, 1, 6, 2]
def baseStart_6041173 : Nat := 118140960795 + 6041173 * 2 ^ 59
def prefixEnd_6041173 : Nat := 4983230072969 + 3 ^ 40 * 6041173 * 2
def baseEnd_6041173 : Nat := 3102025465964197616554657

theorem tailTrace_6041173 : CollatzResearch.WordTrace tailWord_6041173 prefixEnd_6041173 3102025465964197616554657 := by
  unfold tailWord_6041173
  simp only [CollatzResearch.WordTrace]
  refine ⟨220339680942869446051680173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146893120628579630701120115 220339680942869446051680173)
  ·
    refine ⟨82627380353576042269380065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220339680942869446051680173 82627380353576042269380065)
    ·
      refine ⟨61970535265182031702035049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82627380353576042269380065 61970535265182031702035049)
      ·
        refine ⟨46477901448886523776526287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61970535265182031702035049 46477901448886523776526287)
        ·
          refine ⟨69716852173329785664789431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46477901448886523776526287 69716852173329785664789431)
          ·
            refine ⟨104575278259994678497184147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69716852173329785664789431 104575278259994678497184147)
            ·
              refine ⟨156862917389992017745776221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104575278259994678497184147 156862917389992017745776221)
              ·
                refine ⟨58823594021247006654666083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156862917389992017745776221 58823594021247006654666083)
                ·
                  refine ⟨88235391031870509981999125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58823594021247006654666083 88235391031870509981999125)
                  ·
                    refine ⟨4136033954618930155406209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88235391031870509981999125 4136033954618930155406209)
                    ·
                      refine ⟨3102025465964197616554657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4136033954618930155406209 3102025465964197616554657)
                      ·
                        rfl

theorem cell23_6041173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_6041173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041173 prefixEnd_6041173 := by exact prefixLift 6041173
  have htrace : WordTrace (prefixWord ++ tailWord_6041173) baseStart_6041173 baseEnd_6041173 := by
    simpa [prefixWord, tailWord_6041173, baseEnd_6041173] using wordTrace_append hprefix tailTrace_6041173
  have hstable : (prefixWord ++ tailWord_6041173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041173).length < 2 ^ (prefixWord ++ tailWord_6041173).sum := by decide
  have hdescent : baseEnd_6041173 < baseStart_6041173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041193 : List Nat := [1, 2, 1, 1, 1, 4, 3, 3, 2, 2, 3]
def baseStart_6041193 : Nat := 118140960795 + 6041193 * 2 ^ 59
def prefixEnd_6041193 : Nat := 4983230072969 + 3 ^ 40 * 6041193 * 2
def baseEnd_6041193 : Nat := 3102035735577287538304565

theorem tailTrace_6041193 : CollatzResearch.WordTrace tailWord_6041193 prefixEnd_6041193 3102035735577287538304565 := by
  unfold tailWord_6041193
  simp only [CollatzResearch.WordTrace]
  refine ⟨220340410402796989467408233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146893606935197992978272155 220340410402796989467408233)
  ·
    refine ⟨165255307802097742100556175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220340410402796989467408233 165255307802097742100556175)
    ·
      refine ⟨247882961703146613150834263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165255307802097742100556175 247882961703146613150834263)
      ·
        refine ⟨371824442554719919726251395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247882961703146613150834263 371824442554719919726251395)
        ·
          refine ⟨557736663832079879589377093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371824442554719919726251395 557736663832079879589377093)
          ·
            refine ⟨104575624468514977423008205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 557736663832079879589377093 104575624468514977423008205)
            ·
              refine ⟨39215859175693116533628077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104575624468514977423008205 39215859175693116533628077)
              ·
                refine ⟨14705947190884918700110529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39215859175693116533628077 14705947190884918700110529)
                ·
                  refine ⟨11029460393163689025082897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14705947190884918700110529 11029460393163689025082897)
                  ·
                    refine ⟨8272095294872766768812173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11029460393163689025082897 8272095294872766768812173)
                    ·
                      refine ⟨3102035735577287538304565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8272095294872766768812173 3102035735577287538304565)
                      ·
                        rfl

theorem cell23_6041193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2, 2, 3].length) (baseStart_6041193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041193 prefixEnd_6041193 := by exact prefixLift 6041193
  have htrace : WordTrace (prefixWord ++ tailWord_6041193) baseStart_6041193 baseEnd_6041193 := by
    simpa [prefixWord, tailWord_6041193, baseEnd_6041193] using wordTrace_append hprefix tailTrace_6041193
  have hstable : (prefixWord ++ tailWord_6041193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041193).length < 2 ^ (prefixWord ++ tailWord_6041193).sum := by decide
  have hdescent : baseEnd_6041193 < baseStart_6041193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041213 : List Nat := [1, 4, 1, 1, 4, 1, 1, 4, 6]
def baseStart_6041213 : Nat := 118140960795 + 6041213 * 2 ^ 59
def prefixEnd_6041213 : Nat := 4983230072969 + 3 ^ 40 * 6041213 * 2
def baseEnd_6041213 : Nat := 344671778354486384450497

theorem tailTrace_6041213 : CollatzResearch.WordTrace tailWord_6041213 prefixEnd_6041213 344671778354486384450497 := by
  unfold tailWord_6041213
  simp only [CollatzResearch.WordTrace]
  refine ⟨220341139862724532883136293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146894093241816355255424195 220341139862724532883136293)
  ·
    refine ⟨41313963724260849915588055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220341139862724532883136293 41313963724260849915588055)
    ·
      refine ⟨61970945586391274873382083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41313963724260849915588055 61970945586391274873382083)
      ·
        refine ⟨92956418379586912310073125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61970945586391274873382083 92956418379586912310073125)
        ·
          refine ⟨17429328446172546058138711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92956418379586912310073125 17429328446172546058138711)
          ·
            refine ⟨26143992669258819087208067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17429328446172546058138711 26143992669258819087208067)
            ·
              refine ⟨39215989003888228630812101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26143992669258819087208067 39215989003888228630812101)
              ·
                refine ⟨7352997938229042868277269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 39215989003888228630812101 7352997938229042868277269)
                ·
                  refine ⟨344671778354486384450497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7352997938229042868277269 344671778354486384450497)
                  ·
                    rfl

theorem cell23_6041213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 6].length) (baseStart_6041213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041213 prefixEnd_6041213 := by exact prefixLift 6041213
  have htrace : WordTrace (prefixWord ++ tailWord_6041213) baseStart_6041213 baseEnd_6041213 := by
    simpa [prefixWord, tailWord_6041213, baseEnd_6041213] using wordTrace_append hprefix tailTrace_6041213
  have hstable : (prefixWord ++ tailWord_6041213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041213).length < 2 ^ (prefixWord ++ tailWord_6041213).sum := by decide
  have hdescent : baseEnd_6041213 < baseStart_6041213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041216 : List Nat := [2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 6]
def baseStart_6041216 : Nat := 118140960795 + 6041216 * 2 ^ 59
def prefixEnd_6041216 : Nat := 4983230072969 + 3 ^ 40 * 6041216 * 2
def baseEnd_6041216 : Nat := 3102047545632340948316959

theorem tailTrace_6041216 : CollatzResearch.WordTrace tailWord_6041216 prefixEnd_6041216 3102047545632340948316959 := by
  unfold tailWord_6041216
  simp only [CollatzResearch.WordTrace]
  refine ⟨110170624640856832197747751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146894166187809109596997001 110170624640856832197747751)
  ·
    refine ⟨165255936961285248296621627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110170624640856832197747751 165255936961285248296621627)
    ·
      refine ⟨247883905441927872444932441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165255936961285248296621627 247883905441927872444932441)
      ·
        refine ⟨185912929081445904333699331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247883905441927872444932441 185912929081445904333699331)
        ·
          refine ⟨278869393622168856500548997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185912929081445904333699331 278869393622168856500548997)
          ·
            refine ⟨52288011304156660593852937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278869393622168856500548997 52288011304156660593852937)
            ·
              refine ⟨39216008478117495445389703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52288011304156660593852937 39216008478117495445389703)
              ·
                refine ⟨58824012717176243168084555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39216008478117495445389703 58824012717176243168084555)
                ·
                  refine ⟨88236019075764364752126833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58824012717176243168084555 88236019075764364752126833)
                  ·
                    refine ⟨66177014306823273564095125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88236019075764364752126833 66177014306823273564095125)
                    ·
                      refine ⟨3102047545632340948316959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66177014306823273564095125 3102047545632340948316959)
                      ·
                        rfl

theorem cell23_6041216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 6].length) (baseStart_6041216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041216 prefixEnd_6041216 := by exact prefixLift 6041216
  have htrace : WordTrace (prefixWord ++ tailWord_6041216) baseStart_6041216 baseEnd_6041216 := by
    simpa [prefixWord, tailWord_6041216, baseEnd_6041216] using wordTrace_append hprefix tailTrace_6041216
  have hstable : (prefixWord ++ tailWord_6041216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041216).length < 2 ^ (prefixWord ++ tailWord_6041216).sum := by decide
  have hdescent : baseEnd_6041216 < baseStart_6041216 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041217 : List Nat := [1, 2, 4, 2, 1, 3, 1, 4, 1, 4]
def baseStart_6041217 : Nat := 118140960795 + 6041217 * 2 ^ 59
def prefixEnd_6041217 : Nat := 4983230072969 + 3 ^ 40 * 6041217 * 2
def baseEnd_6041217 : Nat := 1034016019704331814801485

theorem tailTrace_6041217 : CollatzResearch.WordTrace tailWord_6041217 prefixEnd_6041217 1034016019704331814801485 := by
  unfold tailWord_6041217
  simp only [CollatzResearch.WordTrace]
  refine ⟨220341285754710041566281905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146894190503140027710854603 220341285754710041566281905)
  ·
    refine ⟨165255964316032531174711429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220341285754710041566281905 165255964316032531174711429)
    ·
      refine ⟨30985493309256099595258393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165255964316032531174711429 30985493309256099595258393)
      ·
        refine ⟨23239119981942074696443795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30985493309256099595258393 23239119981942074696443795)
        ·
          refine ⟨34858679972913112044665693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23239119981942074696443795 34858679972913112044665693)
          ·
            refine ⟨13072004989842417016749635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34858679972913112044665693 13072004989842417016749635)
            ·
              refine ⟨19608007484763625525124453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13072004989842417016749635 19608007484763625525124453)
              ·
                refine ⟨3676501403393179785960835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19608007484763625525124453 3676501403393179785960835)
                ·
                  refine ⟨5514752105089769678941253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3676501403393179785960835 5514752105089769678941253)
                  ·
                    refine ⟨1034016019704331814801485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5514752105089769678941253 1034016019704331814801485)
                    ·
                      rfl

theorem cell23_6041217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_6041217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041217 prefixEnd_6041217 := by exact prefixLift 6041217
  have htrace : WordTrace (prefixWord ++ tailWord_6041217) baseStart_6041217 baseEnd_6041217 := by
    simpa [prefixWord, tailWord_6041217, baseEnd_6041217] using wordTrace_append hprefix tailTrace_6041217
  have hstable : (prefixWord ++ tailWord_6041217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041217).length < 2 ^ (prefixWord ++ tailWord_6041217).sum := by decide
  have hdescent : baseEnd_6041217 < baseStart_6041217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041240 : List Nat := [2, 1, 2, 4, 1, 2, 1, 1, 5, 1, 3]
def baseStart_6041240 : Nat := 118140960795 + 6041240 * 2 ^ 59
def prefixEnd_6041240 : Nat := 4983230072969 + 3 ^ 40 * 6041240 * 2
def baseEnd_6041240 : Nat := 3102059869168048854416849

theorem tailTrace_6041240 : CollatzResearch.WordTrace tailWord_6041240 prefixEnd_6041240 3102059869168048854416849 := by
  unfold tailWord_6041240
  simp only [CollatzResearch.WordTrace]
  refine ⟨110171062316813358247184587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146894749755751144329579449 110171062316813358247184587)
  ·
    refine ⟨165256593475220037370776881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110171062316813358247184587 165256593475220037370776881)
    ·
      refine ⟨123942445106415028028082661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165256593475220037370776881 123942445106415028028082661)
      ·
        refine ⟨23239208457452817755265499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123942445106415028028082661 23239208457452817755265499)
        ·
          refine ⟨34858812686179226632898249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23239208457452817755265499 34858812686179226632898249)
          ·
            refine ⟨26144109514634419974673687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34858812686179226632898249 26144109514634419974673687)
            ·
              refine ⟨39216164271951629962010531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26144109514634419974673687 39216164271951629962010531)
              ·
                refine ⟨58824246407927444943015797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39216164271951629962010531 58824246407927444943015797)
                ·
                  refine ⟨5514773100743197963407731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58824246407927444943015797 5514773100743197963407731)
                  ·
                    refine ⟨8272159651114796945111597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5514773100743197963407731 8272159651114796945111597)
                    ·
                      refine ⟨3102059869168048854416849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8272159651114796945111597 3102059869168048854416849)
                      ·
                        rfl

theorem cell23_6041240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_6041240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041240 prefixEnd_6041240 := by exact prefixLift 6041240
  have htrace : WordTrace (prefixWord ++ tailWord_6041240) baseStart_6041240 baseEnd_6041240 := by
    simpa [prefixWord, tailWord_6041240, baseEnd_6041240] using wordTrace_append hprefix tailTrace_6041240
  have hstable : (prefixWord ++ tailWord_6041240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041240).length < 2 ^ (prefixWord ++ tailWord_6041240).sum := by decide
  have hdescent : baseEnd_6041240 < baseStart_6041240 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041244 : List Nat := [2, 2, 3, 2, 4, 1, 1, 1, 2, 2, 3]
def baseStart_6041244 : Nat := 118140960795 + 6041244 * 2 ^ 59
def prefixEnd_6041244 : Nat := 4983230072969 + 3 ^ 40 * 6041244 * 2
def baseEnd_6041244 : Nat := 3102061923090666838766831

theorem tailTrace_6041244 : CollatzResearch.WordTrace tailWord_6041244 prefixEnd_6041244 3102061923090666838766831 := by
  unfold tailWord_6041244
  simp only [CollatzResearch.WordTrace]
  refine ⟨110171135262806112588757393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146894847017074816785009857 110171135262806112588757393)
  ·
    refine ⟨82628351447104584441568045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110171135262806112588757393 82628351447104584441568045)
    ·
      refine ⟨30985631792664219165588017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82628351447104584441568045 30985631792664219165588017)
      ·
        refine ⟨23239223844498164374191013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30985631792664219165588017 23239223844498164374191013)
        ·
          refine ⟨4357354470843405820160815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23239223844498164374191013 4357354470843405820160815)
          ·
            refine ⟨6536031706265108730241223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357354470843405820160815 6536031706265108730241223)
            ·
              refine ⟨9804047559397663095361835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6536031706265108730241223 9804047559397663095361835)
              ·
                refine ⟨14706071339096494643042753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9804047559397663095361835 14706071339096494643042753)
                ·
                  refine ⟨11029553504322370982282065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14706071339096494643042753 11029553504322370982282065)
                  ·
                    refine ⟨8272165128241778236711549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11029553504322370982282065 8272165128241778236711549)
                    ·
                      refine ⟨3102061923090666838766831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8272165128241778236711549 3102061923090666838766831)
                      ·
                        rfl

theorem cell23_6041244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_6041244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041244 prefixEnd_6041244 := by exact prefixLift 6041244
  have htrace : WordTrace (prefixWord ++ tailWord_6041244) baseStart_6041244 baseEnd_6041244 := by
    simpa [prefixWord, tailWord_6041244, baseEnd_6041244] using wordTrace_append hprefix tailTrace_6041244
  have hstable : (prefixWord ++ tailWord_6041244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041244).length < 2 ^ (prefixWord ++ tailWord_6041244).sum := by decide
  have hdescent : baseEnd_6041244 < baseStart_6041244 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041297 : List Nat := [1, 2, 2, 1, 2, 4, 2, 2, 3, 2, 2]
def baseStart_6041297 : Nat := 118140960795 + 6041297 * 2 ^ 59
def prefixEnd_6041297 : Nat := 4983230072969 + 3 ^ 40 * 6041297 * 2
def baseEnd_6041297 : Nat := 3102089137565355131404087

theorem tailTrace_6041297 : CollatzResearch.WordTrace tailWord_6041297 prefixEnd_6041297 3102089137565355131404087 := by
  unfold tailWord_6041297
  simp only [CollatzResearch.WordTrace]
  refine ⟨220344203594420215229194145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146896135729613476819462763 220344203594420215229194145)
  ·
    refine ⟨165258152695815161421895609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220344203594420215229194145 165258152695815161421895609)
    ·
      refine ⟨123943614521861371066421707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165258152695815161421895609 123943614521861371066421707)
      ·
        refine ⟨185915421782792056599632561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123943614521861371066421707 185915421782792056599632561)
        ·
          refine ⟨139436566337094042449724421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185915421782792056599632561 139436566337094042449724421)
          ·
            refine ⟨26144356188205132959323329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139436566337094042449724421 26144356188205132959323329)
            ·
              refine ⟨19608267141153849719492497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26144356188205132959323329 19608267141153849719492497)
              ·
                refine ⟨14706200355865387289619373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19608267141153849719492497 14706200355865387289619373)
                ·
                  refine ⟨5514825133449520233607265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14706200355865387289619373 5514825133449520233607265)
                  ·
                    refine ⟨4136118850087140175205449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5514825133449520233607265 4136118850087140175205449)
                    ·
                      refine ⟨3102089137565355131404087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4136118850087140175205449 3102089137565355131404087)
                      ·
                        rfl

theorem cell23_6041297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 2, 3, 2, 2].length) (baseStart_6041297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041297 prefixEnd_6041297 := by exact prefixLift 6041297
  have htrace : WordTrace (prefixWord ++ tailWord_6041297) baseStart_6041297 baseEnd_6041297 := by
    simpa [prefixWord, tailWord_6041297, baseEnd_6041297] using wordTrace_append hprefix tailTrace_6041297
  have hstable : (prefixWord ++ tailWord_6041297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041297).length < 2 ^ (prefixWord ++ tailWord_6041297).sum := by decide
  have hdescent : baseEnd_6041297 < baseStart_6041297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041308 : List Nat := [2, 2, 5, 1, 2, 2, 1, 3, 1, 1, 3]
def baseStart_6041308 : Nat := 118140960795 + 6041308 * 2 ^ 59
def prefixEnd_6041308 : Nat := 4983230072969 + 3 ^ 40 * 6041308 * 2
def baseEnd_6041308 : Nat := 3102094785852554588366537

theorem tailTrace_6041308 : CollatzResearch.WordTrace tailWord_6041308 prefixEnd_6041308 3102094785852554588366537 := by
  unfold tailWord_6041308
  simp only [CollatzResearch.WordTrace]
  refine ⟨110172302398690182053922289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146896403198253576071896385 110172302398690182053922289)
  ·
    refine ⟨82629226799017636540441717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110172302398690182053922289 82629226799017636540441717)
    ·
      refine ⟨7746490012407903425666411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 82629226799017636540441717 7746490012407903425666411)
      ·
        refine ⟨11619735018611855138499617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7746490012407903425666411 11619735018611855138499617)
        ·
          refine ⟨8714801263958891353874713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11619735018611855138499617 8714801263958891353874713)
          ·
            refine ⟨6536100947969168515406035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8714801263958891353874713 6536100947969168515406035)
            ·
              refine ⟨9804151421953752773109053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6536100947969168515406035 9804151421953752773109053)
              ·
                refine ⟨3676556783232657289915895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9804151421953752773109053 3676556783232657289915895)
                ·
                  refine ⟨5514835174848985934873843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3676556783232657289915895 5514835174848985934873843)
                  ·
                    refine ⟨8272252762273478902310765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5514835174848985934873843 8272252762273478902310765)
                    ·
                      refine ⟨3102094785852554588366537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8272252762273478902310765 3102094785852554588366537)
                      ·
                        rfl

theorem cell23_6041308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_6041308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041308 prefixEnd_6041308 := by exact prefixLift 6041308
  have htrace : WordTrace (prefixWord ++ tailWord_6041308) baseStart_6041308 baseEnd_6041308 := by
    simpa [prefixWord, tailWord_6041308, baseEnd_6041308] using wordTrace_append hprefix tailTrace_6041308
  have hstable : (prefixWord ++ tailWord_6041308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041308).length < 2 ^ (prefixWord ++ tailWord_6041308).sum := by decide
  have hdescent : baseEnd_6041308 < baseStart_6041308 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041351 : List Nat := [1, 1, 4, 4, 3, 1, 1, 2, 1, 2, 3]
def baseStart_6041351 : Nat := 118140960795 + 6041351 * 2 ^ 59
def prefixEnd_6041351 : Nat := 4983230072969 + 3 ^ 40 * 6041351 * 2
def baseEnd_6041351 : Nat := 3102116865520697920128839

theorem tailTrace_6041351 : CollatzResearch.WordTrace tailWord_6041351 prefixEnd_6041351 3102116865520697920128839 := by
  unfold tailWord_6041351
  simp only [CollatzResearch.WordTrace]
  refine ⟨220346173136224582451659907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146897448757483054967773271 220346173136224582451659907)
  ·
    refine ⟨330519259704336873677489861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220346173136224582451659907 330519259704336873677489861)
    ·
      refine ⟨61972361194563163814529349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 330519259704336873677489861 61972361194563163814529349)
      ·
        refine ⟨11619817723980593215224253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61972361194563163814529349 11619817723980593215224253)
        ·
          refine ⟨4357431646492722455709095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11619817723980593215224253 4357431646492722455709095)
          ·
            refine ⟨6536147469739083683563643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4357431646492722455709095 6536147469739083683563643)
            ·
              refine ⟨9804221204608625525345465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6536147469739083683563643 9804221204608625525345465)
              ·
                refine ⟨7353165903456469144009099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9804221204608625525345465 7353165903456469144009099)
                ·
                  refine ⟨11029748855184703716013649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7353165903456469144009099 11029748855184703716013649)
                  ·
                    refine ⟨8272311641388527787010237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11029748855184703716013649 8272311641388527787010237)
                    ·
                      refine ⟨3102116865520697920128839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8272311641388527787010237 3102116865520697920128839)
                      ·
                        rfl

theorem cell23_6041351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_6041351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041351 prefixEnd_6041351 := by exact prefixLift 6041351
  have htrace : WordTrace (prefixWord ++ tailWord_6041351) baseStart_6041351 baseEnd_6041351 := by
    simpa [prefixWord, tailWord_6041351, baseEnd_6041351] using wordTrace_append hprefix tailTrace_6041351
  have hstable : (prefixWord ++ tailWord_6041351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041351).length < 2 ^ (prefixWord ++ tailWord_6041351).sum := by decide
  have hdescent : baseEnd_6041351 < baseStart_6041351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041400 : List Nat := [2, 1, 2, 1, 3, 4, 1, 1, 2, 2, 4]
def baseStart_6041400 : Nat := 118140960795 + 6041400 * 2 ^ 59
def prefixEnd_6041400 : Nat := 4983230072969 + 3 ^ 40 * 6041400 * 2
def baseEnd_6041400 : Nat := 3102142026072768228416113

theorem tailTrace_6041400 : CollatzResearch.WordTrace tailWord_6041400 prefixEnd_6041400 3102142026072768228416113 := by
  unfold tailWord_6041400
  simp only [CollatzResearch.WordTrace]
  refine ⟨110173980156523531910096827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146898640208698042546795769 110173980156523531910096827)
  ·
    refine ⟨165260970234785297865145241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110173980156523531910096827 165260970234785297865145241)
    ·
      refine ⟨123945727676088973398858931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165260970234785297865145241 123945727676088973398858931)
      ·
        refine ⟨185918591514133460098288397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123945727676088973398858931 185918591514133460098288397)
        ·
          refine ⟨69719471817800047536858149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185918591514133460098288397 69719471817800047536858149)
          ·
            refine ⟨13072400965837508913160903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69719471817800047536858149 13072400965837508913160903)
            ·
              refine ⟨19608601448756263369741355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13072400965837508913160903 19608601448756263369741355)
              ·
                refine ⟨29412902173134395054612033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19608601448756263369741355 29412902173134395054612033)
                ·
                  refine ⟨22059676629850796290959025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29412902173134395054612033 22059676629850796290959025)
                  ·
                    refine ⟨16544757472388097218219269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22059676629850796290959025 16544757472388097218219269)
                    ·
                      refine ⟨3102142026072768228416113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16544757472388097218219269 3102142026072768228416113)
                      ·
                        rfl

theorem cell23_6041400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_6041400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041400 prefixEnd_6041400 := by exact prefixLift 6041400
  have htrace : WordTrace (prefixWord ++ tailWord_6041400) baseStart_6041400 baseEnd_6041400 := by
    simpa [prefixWord, tailWord_6041400, baseEnd_6041400] using wordTrace_append hprefix tailTrace_6041400
  have hstable : (prefixWord ++ tailWord_6041400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041400).length < 2 ^ (prefixWord ++ tailWord_6041400).sum := by decide
  have hdescent : baseEnd_6041400 < baseStart_6041400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041404 : List Nat := [2, 2, 2, 2, 1, 1, 4, 3, 2, 2, 2]
def baseStart_6041404 : Nat := 118140960795 + 6041404 * 2 ^ 59
def prefixEnd_6041404 : Nat := 4983230072969 + 3 ^ 40 * 6041404 * 2
def baseEnd_6041404 : Nat := 3102144079995386212766095

theorem tailTrace_6041404 : CollatzResearch.WordTrace tailWord_6041404 prefixEnd_6041404 3102144079995386212766095 := by
  unfold tailWord_6041404
  simp only [CollatzResearch.WordTrace]
  refine ⟨110174053102516286251669633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146898737470021715002226177 110174053102516286251669633)
  ·
    refine ⟨82630539826887214688752225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110174053102516286251669633 82630539826887214688752225)
    ·
      refine ⟨61972904870165411016564169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82630539826887214688752225 61972904870165411016564169)
      ·
        refine ⟨46479678652624058262423127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61972904870165411016564169 46479678652624058262423127)
        ·
          refine ⟨69719517978936087393634691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46479678652624058262423127 69719517978936087393634691)
          ·
            refine ⟨104579276968404131090452037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69719517978936087393634691 104579276968404131090452037)
            ·
              refine ⟨19608614431575774579459757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104579276968404131090452037 19608614431575774579459757)
              ·
                refine ⟨7353230411840915467297409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19608614431575774579459757 7353230411840915467297409)
                ·
                  refine ⟨5514922808880686600473057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7353230411840915467297409 5514922808880686600473057)
                  ·
                    refine ⟨4136192106660514950354793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5514922808880686600473057 4136192106660514950354793)
                    ·
                      refine ⟨3102144079995386212766095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4136192106660514950354793 3102144079995386212766095)
                      ·
                        rfl

theorem cell23_6041404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 3, 2, 2, 2].length) (baseStart_6041404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041404 prefixEnd_6041404 := by exact prefixLift 6041404
  have htrace : WordTrace (prefixWord ++ tailWord_6041404) baseStart_6041404 baseEnd_6041404 := by
    simpa [prefixWord, tailWord_6041404, baseEnd_6041404] using wordTrace_append hprefix tailTrace_6041404
  have hstable : (prefixWord ++ tailWord_6041404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041404).length < 2 ^ (prefixWord ++ tailWord_6041404).sum := by decide
  have hdescent : baseEnd_6041404 < baseStart_6041404 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041527 : List Nat := [1, 1, 3, 1, 3, 1, 1, 3, 5, 1, 3]
def baseStart_6041527 : Nat := 118140960795 + 6041527 * 2 ^ 59
def prefixEnd_6041527 : Nat := 4983230072969 + 3 ^ 40 * 6041527 * 2
def baseEnd_6041527 : Nat := 3102207238115889231528029

theorem tailTrace_6041527 : CollatzResearch.WordTrace tailWord_6041527 prefixEnd_6041527 3102207238115889231528029 := by
  unfold tailWord_6041527
  simp only [CollatzResearch.WordTrace]
  refine ⟨220352592383586964510066835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146901728255724643006711223 220352592383586964510066835)
  ·
    refine ⟨330528888575380446765100253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220352592383586964510066835 330528888575380446765100253)
    ·
      refine ⟨123948333215767667536912595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330528888575380446765100253 123948333215767667536912595)
      ·
        refine ⟨185922499823651501305368893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123948333215767667536912595 185922499823651501305368893)
        ·
          refine ⟨69720937433869312989513335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185922499823651501305368893 69720937433869312989513335)
          ·
            refine ⟨104581406150803969484270003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69720937433869312989513335 104581406150803969484270003)
            ·
              refine ⟨156872109226205954226405005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104581406150803969484270003 156872109226205954226405005)
              ·
                refine ⟨58827040959827232834901877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156872109226205954226405005 58827040959827232834901877)
                ·
                  refine ⟨5515035089983803078272051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58827040959827232834901877 5515035089983803078272051)
                  ·
                    refine ⟨8272552634975704617408077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5515035089983803078272051 8272552634975704617408077)
                    ·
                      refine ⟨3102207238115889231528029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8272552634975704617408077 3102207238115889231528029)
                      ·
                        rfl

theorem cell23_6041527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_6041527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041527 prefixEnd_6041527 := by exact prefixLift 6041527
  have htrace : WordTrace (prefixWord ++ tailWord_6041527) baseStart_6041527 baseEnd_6041527 := by
    simpa [prefixWord, tailWord_6041527, baseEnd_6041527] using wordTrace_append hprefix tailTrace_6041527
  have hstable : (prefixWord ++ tailWord_6041527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041527).length < 2 ^ (prefixWord ++ tailWord_6041527).sum := by decide
  have hdescent : baseEnd_6041527 < baseStart_6041527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041560 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 3, 6]
def baseStart_6041560 : Nat := 118140960795 + 6041560 * 2 ^ 59
def prefixEnd_6041560 : Nat := 4983230072969 + 3 ^ 40 * 6041560 * 2
def baseEnd_6041560 : Nat := 1034074727659162534138459

theorem tailTrace_6041560 : CollatzResearch.WordTrace tailWord_6041560 prefixEnd_6041560 1034074727659162534138459 := by
  unfold tailWord_6041560
  simp only [CollatzResearch.WordTrace]
  refine ⟨110176897996233705573009067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146902530661644940764012089 110176897996233705573009067)
  ·
    refine ⟨165265346994350558359513601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110176897996233705573009067 165265346994350558359513601)
    ·
      refine ⟨123949010245762918769635201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165265346994350558359513601 123949010245762918769635201)
      ·
        refine ⟨92961757684322189077226401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123949010245762918769635201 92961757684322189077226401)
        ·
          refine ⟨69721318263241641807919801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92961757684322189077226401 69721318263241641807919801)
          ·
            refine ⟨52290988697431231355939851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69721318263241641807919801 52290988697431231355939851)
            ·
              refine ⟨78436483046146847033909777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52290988697431231355939851 78436483046146847033909777)
              ·
                refine ⟨58827362284610135275432333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78436483046146847033909777 58827362284610135275432333)
                ·
                  refine ⟨22060260856728800728287125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58827362284610135275432333 22060260856728800728287125)
                  ·
                    refine ⟨1034074727659162534138459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22060260856728800728287125 1034074727659162534138459)
                    ·
                      rfl

theorem cell23_6041560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 3, 6].length) (baseStart_6041560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041560 prefixEnd_6041560 := by exact prefixLift 6041560
  have htrace : WordTrace (prefixWord ++ tailWord_6041560) baseStart_6041560 baseEnd_6041560 := by
    simpa [prefixWord, tailWord_6041560, baseEnd_6041560] using wordTrace_append hprefix tailTrace_6041560
  have hstable : (prefixWord ++ tailWord_6041560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041560).length < 2 ^ (prefixWord ++ tailWord_6041560).sum := by decide
  have hdescent : baseEnd_6041560 < baseStart_6041560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041567 : List Nat := [1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 4]
def baseStart_6041567 : Nat := 118140960795 + 6041567 * 2 ^ 59
def prefixEnd_6041567 : Nat := 4983230072969 + 3 ^ 40 * 6041567 * 2
def baseEnd_6041567 : Nat := 3102227777342069075027845

theorem tailTrace_6041567 : CollatzResearch.WordTrace tailWord_6041567 prefixEnd_6041567 3102227777342069075027845 := by
  unfold tailWord_6041567
  simp only [CollatzResearch.WordTrace]
  refine ⟨220354051303442051341522955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146902700868961367561015303 220354051303442051341522955)
  ·
    refine ⟨330531076955163077012284433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220354051303442051341522955 330531076955163077012284433)
    ·
      refine ⟨247898307716372307759213325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330531076955163077012284433 247898307716372307759213325)
      ·
        refine ⟨92961865393639615409704997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247898307716372307759213325 92961865393639615409704997)
        ·
          refine ⟨17430349761307427889319687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92961865393639615409704997 17430349761307427889319687)
          ·
            refine ⟨26145524641961141833979531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17430349761307427889319687 26145524641961141833979531)
            ·
              refine ⟨39218286962941712750969297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26145524641961141833979531 39218286962941712750969297)
              ·
                refine ⟨29413715222206284563226973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39218286962941712750969297 29413715222206284563226973)
                ·
                  refine ⟨11030143208327356711210115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29413715222206284563226973 11030143208327356711210115)
                  ·
                    refine ⟨16545214812491035066815173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11030143208327356711210115 16545214812491035066815173)
                    ·
                      refine ⟨3102227777342069075027845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16545214812491035066815173 3102227777342069075027845)
                      ·
                        rfl

theorem cell23_6041567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_6041567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041567 prefixEnd_6041567 := by exact prefixLift 6041567
  have htrace : WordTrace (prefixWord ++ tailWord_6041567) baseStart_6041567 baseEnd_6041567 := by
    simpa [prefixWord, tailWord_6041567, baseEnd_6041567] using wordTrace_append hprefix tailTrace_6041567
  have hstable : (prefixWord ++ tailWord_6041567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041567).length < 2 ^ (prefixWord ++ tailWord_6041567).sum := by decide
  have hdescent : baseEnd_6041567 < baseStart_6041567 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041580 : List Nat := [2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 6]
def baseStart_6041580 : Nat := 118140960795 + 6041580 * 2 ^ 59
def prefixEnd_6041580 : Nat := 4983230072969 + 3 ^ 40 * 6041580 * 2
def baseEnd_6041580 : Nat := 3102234452590577524165285

theorem tailTrace_6041580 : CollatzResearch.WordTrace tailWord_6041580 prefixEnd_6041580 3102234452590577524165285 := by
  unfold tailWord_6041580
  simp only [CollatzResearch.WordTrace]
  refine ⟨110177262726197477280873097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146903016968263303041164129 110177262726197477280873097)
  ·
    refine ⟨82632947044648107960654823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110177262726197477280873097 82632947044648107960654823)
    ·
      refine ⟨123949420566972161940982235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82632947044648107960654823 123949420566972161940982235)
      ·
        refine ⟨185924130850458242911473353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123949420566972161940982235 185924130850458242911473353)
        ·
          refine ⟨139443098137843682183605015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185924130850458242911473353 139443098137843682183605015)
          ·
            refine ⟨209164647206765523275407523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139443098137843682183605015 209164647206765523275407523)
            ·
              refine ⟨313746970810148284913111285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209164647206765523275407523 313746970810148284913111285)
              ·
                refine ⟨29413778513451401710604183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 313746970810148284913111285 29413778513451401710604183)
                ·
                  refine ⟨44120667770177102565906275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29413778513451401710604183 44120667770177102565906275)
                  ·
                    refine ⟨66181001655265653848859413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44120667770177102565906275 66181001655265653848859413)
                    ·
                      refine ⟨3102234452590577524165285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66181001655265653848859413 3102234452590577524165285)
                      ·
                        rfl

theorem cell23_6041580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 6].length) (baseStart_6041580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041580 prefixEnd_6041580 := by exact prefixLift 6041580
  have htrace : WordTrace (prefixWord ++ tailWord_6041580) baseStart_6041580 baseEnd_6041580 := by
    simpa [prefixWord, tailWord_6041580, baseEnd_6041580] using wordTrace_append hprefix tailTrace_6041580
  have hstable : (prefixWord ++ tailWord_6041580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041580).length < 2 ^ (prefixWord ++ tailWord_6041580).sum := by decide
  have hdescent : baseEnd_6041580 < baseStart_6041580 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041584 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 5, 2, 2]
def baseStart_6041584 : Nat := 118140960795 + 6041584 * 2 ^ 59
def prefixEnd_6041584 : Nat := 4983230072969 + 3 ^ 40 * 6041584 * 2
def baseEnd_6041584 : Nat := 3102236506513195508515267

theorem tailTrace_6041584 : CollatzResearch.WordTrace tailWord_6041584 prefixEnd_6041584 3102236506513195508515267 := by
  unfold tailWord_6041584
  simp only [CollatzResearch.WordTrace]
  refine ⟨110177335672190231622445903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146903114229586975496594537 110177335672190231622445903)
  ·
    refine ⟨165266003508285347433668855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110177335672190231622445903 165266003508285347433668855)
    ·
      refine ⟨247899005262428021150503283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165266003508285347433668855 247899005262428021150503283)
      ·
        refine ⟨371848507893642031725754925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247899005262428021150503283 371848507893642031725754925)
        ·
          refine ⟨139443190460115761897158097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371848507893642031725754925 139443190460115761897158097)
          ·
            refine ⟨104582392845086821422868573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139443190460115761897158097 104582392845086821422868573)
            ·
              refine ⟨39218397316907558033575715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104582392845086821422868573 39218397316907558033575715)
              ·
                refine ⟨58827595975361337050363573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39218397316907558033575715 58827595975361337050363573)
                ·
                  refine ⟨5515087122690125348471585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 58827595975361337050363573 5515087122690125348471585)
                  ·
                    refine ⟨4136315342017594011353689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5515087122690125348471585 4136315342017594011353689)
                    ·
                      refine ⟨3102236506513195508515267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4136315342017594011353689 3102236506513195508515267)
                      ·
                        rfl

theorem cell23_6041584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 5, 2, 2].length) (baseStart_6041584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041584 prefixEnd_6041584 := by exact prefixLift 6041584
  have htrace : WordTrace (prefixWord ++ tailWord_6041584) baseStart_6041584 baseEnd_6041584 := by
    simpa [prefixWord, tailWord_6041584, baseEnd_6041584] using wordTrace_append hprefix tailTrace_6041584
  have hstable : (prefixWord ++ tailWord_6041584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041584).length < 2 ^ (prefixWord ++ tailWord_6041584).sum := by decide
  have hdescent : baseEnd_6041584 < baseStart_6041584 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041597 : List Nat := [1, 4, 1, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_6041597 : Nat := 118140960795 + 6041597 * 2 ^ 59
def prefixEnd_6041597 : Nat := 4983230072969 + 3 ^ 40 * 6041597 * 2
def baseEnd_6041597 : Nat := 3102243181761703957652707

theorem tailTrace_6041597 : CollatzResearch.WordTrace tailWord_6041597 prefixEnd_6041597 3102243181761703957652707 := by
  unfold tailWord_6041597
  simp only [CollatzResearch.WordTrace]
  refine ⟨220355145493333366465115045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146903430328888910976743363 220355145493333366465115045)
  ·
    refine ⟨41316589780000006212209071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220355145493333366465115045 41316589780000006212209071)
    ·
      refine ⟨61974884670000009318313607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41316589780000006212209071 61974884670000009318313607)
      ·
        refine ⟨92962327005000013977470411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61974884670000009318313607 92962327005000013977470411)
        ·
          refine ⟨139443490507500020966205617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92962327005000013977470411 139443490507500020966205617)
          ·
            refine ⟨104582617880625015724654213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139443490507500020966205617 104582617880625015724654213)
            ·
              refine ⟨19609240852617190448372665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 104582617880625015724654213 19609240852617190448372665)
              ·
                refine ⟨14706930639462892836279499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19609240852617190448372665 14706930639462892836279499)
                ·
                  refine ⟨22060395959194339254419249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14706930639462892836279499 22060395959194339254419249)
                  ·
                    refine ⟨16545296969395754440814437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22060395959194339254419249 16545296969395754440814437)
                    ·
                      refine ⟨3102243181761703957652707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16545296969395754440814437 3102243181761703957652707)
                      ·
                        rfl

theorem cell23_6041597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_6041597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041597 prefixEnd_6041597 := by exact prefixLift 6041597
  have htrace : WordTrace (prefixWord ++ tailWord_6041597) baseStart_6041597 baseEnd_6041597 := by
    simpa [prefixWord, tailWord_6041597, baseEnd_6041597] using wordTrace_append hprefix tailTrace_6041597
  have hstable : (prefixWord ++ tailWord_6041597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041597).length < 2 ^ (prefixWord ++ tailWord_6041597).sum := by decide
  have hdescent : baseEnd_6041597 < baseStart_6041597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041598 : List Nat := [4, 2, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_6041598 : Nat := 118140960795 + 6041598 * 2 ^ 59
def prefixEnd_6041598 : Nat := 4983230072969 + 3 ^ 40 * 6041598 * 2
def baseEnd_6041598 : Nat := 1034081231747452817913401

theorem tailTrace_6041598 : CollatzResearch.WordTrace tailWord_6041598 prefixEnd_6041598 1034081231747452817913401 := by
  unfold tailWord_6041598
  simp only [CollatzResearch.WordTrace]
  refine ⟨27544397745791217954487681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146903454644219829090600965 27544397745791217954487681)
  ·
    refine ⟨20658298309343413465865761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27544397745791217954487681 20658298309343413465865761)
    ·
      refine ⟨15493723732007560099399321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20658298309343413465865761 15493723732007560099399321)
      ·
        refine ⟨11620292799005670074549491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15493723732007560099399321 11620292799005670074549491)
        ·
          refine ⟨17430439198508505111824237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11620292799005670074549491 17430439198508505111824237)
          ·
            refine ⟨6536414699440689416934089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17430439198508505111824237 6536414699440689416934089)
            ·
              refine ⟨4902311024580517062700567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6536414699440689416934089 4902311024580517062700567)
              ·
                refine ⟨7353466536870775594050851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4902311024580517062700567 7353466536870775594050851)
                ·
                  refine ⟨11030199805306163391076277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7353466536870775594050851 11030199805306163391076277)
                  ·
                    refine ⟨1034081231747452817913401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11030199805306163391076277 1034081231747452817913401)
                    ·
                      rfl

theorem cell23_6041598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_6041598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041598 prefixEnd_6041598 := by exact prefixLift 6041598
  have htrace : WordTrace (prefixWord ++ tailWord_6041598) baseStart_6041598 baseEnd_6041598 := by
    simpa [prefixWord, tailWord_6041598, baseEnd_6041598] using wordTrace_append hprefix tailTrace_6041598
  have hstable : (prefixWord ++ tailWord_6041598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041598).length < 2 ^ (prefixWord ++ tailWord_6041598).sum := by decide
  have hdescent : baseEnd_6041598 < baseStart_6041598 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041627 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 2, 7, 2]
def baseStart_6041627 : Nat := 118140960795 + 6041627 * 2 ^ 59
def prefixEnd_6041627 : Nat := 4983230072969 + 3 ^ 40 * 6041627 * 2
def baseEnd_6041627 : Nat := 3102258586181338840277569

theorem tailTrace_6041627 : CollatzResearch.WordTrace tailWord_6041627 prefixEnd_6041627 3102258586181338840277569 := by
  unfold tailWord_6041627
  simp only [CollatzResearch.WordTrace]
  refine ⟨220356239683224681588707135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146904159788816454392471423 220356239683224681588707135)
  ·
    refine ⟨330534359524837022383060703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220356239683224681588707135 330534359524837022383060703)
    ·
      refine ⟨495801539287255533574591055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330534359524837022383060703 495801539287255533574591055)
      ·
        refine ⟨743702308930883300361886583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495801539287255533574591055 743702308930883300361886583)
        ·
          refine ⟨1115553463396324950542829875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743702308930883300361886583 1115553463396324950542829875)
          ·
            refine ⟨1673330195094487425814244813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1115553463396324950542829875 1673330195094487425814244813)
            ·
              refine ⟨627498823160432784680341805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1673330195094487425814244813 627498823160432784680341805)
              ·
                refine ⟨235312058685162294255128177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 627498823160432784680341805 235312058685162294255128177)
                ·
                  refine ⟨176484044013871720691346133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 235312058685162294255128177 176484044013871720691346133)
                  ·
                    refine ⟨4136344781575118453703425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 176484044013871720691346133 4136344781575118453703425)
                    ·
                      refine ⟨3102258586181338840277569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4136344781575118453703425 3102258586181338840277569)
                      ·
                        rfl

theorem cell23_6041627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 7, 2].length) (baseStart_6041627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041627 prefixEnd_6041627 := by exact prefixLift 6041627
  have htrace : WordTrace (prefixWord ++ tailWord_6041627) baseStart_6041627 baseEnd_6041627 := by
    simpa [prefixWord, tailWord_6041627, baseEnd_6041627] using wordTrace_append hprefix tailTrace_6041627
  have hstable : (prefixWord ++ tailWord_6041627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041627).length < 2 ^ (prefixWord ++ tailWord_6041627).sum := by decide
  have hdescent : baseEnd_6041627 < baseStart_6041627 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041661 : List Nat := [1, 4, 1, 3, 1, 1, 1, 5, 1, 3, 2]
def baseStart_6041661 : Nat := 118140960795 + 6041661 * 2 ^ 59
def prefixEnd_6041661 : Nat := 4983230072969 + 3 ^ 40 * 6041661 * 2
def baseEnd_6041661 : Nat := 3102276044523591707252413

theorem tailTrace_6041661 : CollatzResearch.WordTrace tailWord_6041661 prefixEnd_6041661 3102276044523591707252413 := by
  unfold tailWord_6041661
  simp only [CollatzResearch.WordTrace]
  refine ⟨220357479765101505395444837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146904986510067670263629891 220357479765101505395444837)
  ·
    refine ⟨41317027455956532261645907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220357479765101505395444837 41317027455956532261645907)
    ·
      refine ⟨61975541183934798392468861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41317027455956532261645907 61975541183934798392468861)
      ·
        refine ⟨23240827943975549397175823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61975541183934798392468861 23240827943975549397175823)
        ·
          refine ⟨34861241915963324095763735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23240827943975549397175823 34861241915963324095763735)
          ·
            refine ⟨52291862873944986143645603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34861241915963324095763735 52291862873944986143645603)
            ·
              refine ⟨78437794310917479215468405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52291862873944986143645603 78437794310917479215468405)
              ·
                refine ⟨7353543216648513676450163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78437794310917479215468405 7353543216648513676450163)
                ·
                  refine ⟨11030314824972770514675245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7353543216648513676450163 11030314824972770514675245)
                  ·
                    refine ⟨4136368059364788943003217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11030314824972770514675245 4136368059364788943003217)
                    ·
                      refine ⟨3102276044523591707252413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4136368059364788943003217 3102276044523591707252413)
                      ·
                        rfl

theorem cell23_6041661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_6041661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041661 prefixEnd_6041661 := by exact prefixLift 6041661
  have htrace : WordTrace (prefixWord ++ tailWord_6041661) baseStart_6041661 baseEnd_6041661 := by
    simpa [prefixWord, tailWord_6041661, baseEnd_6041661] using wordTrace_append hprefix tailTrace_6041661
  have hstable : (prefixWord ++ tailWord_6041661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041661).length < 2 ^ (prefixWord ++ tailWord_6041661).sum := by decide
  have hdescent : baseEnd_6041661 < baseStart_6041661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041687 : List Nat := [1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 4]
def baseStart_6041687 : Nat := 118140960795 + 6041687 * 2 ^ 59
def prefixEnd_6041687 : Nat := 4983230072969 + 3 ^ 40 * 6041687 * 2
def baseEnd_6041687 : Nat := 3102289395020608605527293

theorem tailTrace_6041687 : CollatzResearch.WordTrace tailWord_6041687 prefixEnd_6041687 3102289395020608605527293 := by
  unfold tailWord_6041687
  simp only [CollatzResearch.WordTrace]
  refine ⟨220358428063007311835891315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146905618708671541223927543 220358428063007311835891315)
  ·
    refine ⟨330537642094510967753836973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220358428063007311835891315 330537642094510967753836973)
    ·
      refine ⟨123951615785441612907688865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330537642094510967753836973 123951615785441612907688865)
      ·
        refine ⟨92963711839081209680766649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123951615785441612907688865 92963711839081209680766649)
        ·
          refine ⟨69722783879310907260574987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92963711839081209680766649 69722783879310907260574987)
          ·
            refine ⟨104584175818966360890862481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69722783879310907260574987 104584175818966360890862481)
            ·
              refine ⟨78438131864224770668146861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104584175818966360890862481 78438131864224770668146861)
              ·
                refine ⟨29414299449084289000555073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78438131864224770668146861 29414299449084289000555073)
                ·
                  refine ⟨22060724586813216750416305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29414299449084289000555073 22060724586813216750416305)
                  ·
                    refine ⟨16545543440109912562812229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22060724586813216750416305 16545543440109912562812229)
                    ·
                      refine ⟨3102289395020608605527293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16545543440109912562812229 3102289395020608605527293)
                      ·
                        rfl

theorem cell23_6041687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 4].length) (baseStart_6041687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041687 prefixEnd_6041687 := by exact prefixLift 6041687
  have htrace : WordTrace (prefixWord ++ tailWord_6041687) baseStart_6041687 baseEnd_6041687 := by
    simpa [prefixWord, tailWord_6041687, baseEnd_6041687] using wordTrace_append hprefix tailTrace_6041687
  have hstable : (prefixWord ++ tailWord_6041687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041687).length < 2 ^ (prefixWord ++ tailWord_6041687).sum := by decide
  have hdescent : baseEnd_6041687 < baseStart_6041687 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041731 : List Nat := [1, 1, 1, 3, 3, 3, 4, 2, 5]
def baseStart_6041731 : Nat := 118140960795 + 6041731 * 2 ^ 59
def prefixEnd_6041731 : Nat := 4983230072969 + 3 ^ 40 * 6041731 * 2
def baseEnd_6041731 : Nat := 344701332018822937041899

theorem tailTrace_6041731 : CollatzResearch.WordTrace tailWord_6041731 prefixEnd_6041731 344701332018822937041899 := by
  unfold tailWord_6041731
  simp only [CollatzResearch.WordTrace]
  refine ⟨220360032874847907350493047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146906688583231938233662031 220360032874847907350493047)
  ·
    refine ⟨330540049312271861025739571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220360032874847907350493047 330540049312271861025739571)
    ·
      refine ⟨495810073968407791538609357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330540049312271861025739571 495810073968407791538609357)
      ·
        refine ⟨185928777738152921826978509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 495810073968407791538609357 185928777738152921826978509)
        ·
          refine ⟨69723291651807345685116941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185928777738152921826978509 69723291651807345685116941)
          ·
            refine ⟨26146234369427754631918853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69723291651807345685116941 26146234369427754631918853)
            ·
              refine ⟨4902418944267703993484785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26146234369427754631918853 4902418944267703993484785)
              ·
                refine ⟨3676814208200777995113589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4902418944267703993484785 3676814208200777995113589)
                ·
                  refine ⟨344701332018822937041899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3676814208200777995113589 344701332018822937041899)
                  ·
                    rfl

theorem cell23_6041731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 5].length) (baseStart_6041731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041731 prefixEnd_6041731 := by exact prefixLift 6041731
  have htrace : WordTrace (prefixWord ++ tailWord_6041731) baseStart_6041731 baseEnd_6041731 := by
    simpa [prefixWord, tailWord_6041731, baseEnd_6041731] using wordTrace_append hprefix tailTrace_6041731
  have hstable : (prefixWord ++ tailWord_6041731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041731).length < 2 ^ (prefixWord ++ tailWord_6041731).sum := by decide
  have hdescent : baseEnd_6041731 < baseStart_6041731 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041737 : List Nat := [1, 2, 1, 1, 4, 2, 1, 3, 1, 2, 5]
def baseStart_6041737 : Nat := 118140960795 + 6041737 * 2 ^ 59
def prefixEnd_6041737 : Nat := 4983230072969 + 3 ^ 40 * 6041737 * 2
def baseEnd_6041737 : Nat := 3102315069053333409902063

theorem tailTrace_6041737 : CollatzResearch.WordTrace tailWord_6041737 prefixEnd_6041737 3102315069053333409902063 := by
  unfold tailWord_6041737
  simp only [CollatzResearch.WordTrace]
  refine ⟨220360251712826170375211465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146906834475217446916807643 220360251712826170375211465)
  ·
    refine ⟨165270188784619627781408599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220360251712826170375211465 165270188784619627781408599)
    ·
      refine ⟨247905283176929441672112899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165270188784619627781408599 247905283176929441672112899)
      ·
        refine ⟨371857924765394162508169349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247905283176929441672112899 371857924765394162508169349)
        ·
          refine ⟨69723360893511405470281753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 371857924765394162508169349 69723360893511405470281753)
          ·
            refine ⟨52292520670133554102711315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69723360893511405470281753 52292520670133554102711315)
            ·
              refine ⟨78438781005200331154066973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52292520670133554102711315 78438781005200331154066973)
              ·
                refine ⟨29414542876950124182775115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78438781005200331154066973 29414542876950124182775115)
                ·
                  refine ⟨44121814315425186274162673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29414542876950124182775115 44121814315425186274162673)
                  ·
                    refine ⟨33091360736568889705622005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44121814315425186274162673 33091360736568889705622005)
                    ·
                      refine ⟨3102315069053333409902063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33091360736568889705622005 3102315069053333409902063)
                      ·
                        rfl

theorem cell23_6041737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 2, 5].length) (baseStart_6041737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041737 prefixEnd_6041737 := by exact prefixLift 6041737
  have htrace : WordTrace (prefixWord ++ tailWord_6041737) baseStart_6041737 baseEnd_6041737 := by
    simpa [prefixWord, tailWord_6041737, baseEnd_6041737] using wordTrace_append hprefix tailTrace_6041737
  have hstable : (prefixWord ++ tailWord_6041737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041737).length < 2 ^ (prefixWord ++ tailWord_6041737).sum := by decide
  have hdescent : baseEnd_6041737 < baseStart_6041737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041747 : List Nat := [1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 4]
def baseStart_6041747 : Nat := 118140960795 + 6041747 * 2 ^ 59
def prefixEnd_6041747 : Nat := 4983230072969 + 3 ^ 40 * 6041747 * 2
def baseEnd_6041747 : Nat := 3102320203859878370777017

theorem tailTrace_6041747 : CollatzResearch.WordTrace tailWord_6041747 prefixEnd_6041747 3102320203859878370777017 := by
  unfold tailWord_6041747
  simp only [CollatzResearch.WordTrace]
  refine ⟨220360616442789942083075495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146907077628526628055383663 220360616442789942083075495)
  ·
    refine ⟨330540924664184913124613243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220360616442789942083075495 330540924664184913124613243)
    ·
      refine ⟨495811386996277369686919865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330540924664184913124613243 495811386996277369686919865)
      ·
        refine ⟨371858540247208027265189899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495811386996277369686919865 371858540247208027265189899)
        ·
          refine ⟨557787810370812040897784849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371858540247208027265189899 557787810370812040897784849)
          ·
            refine ⟨418340857778109030673338637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557787810370812040897784849 418340857778109030673338637)
            ·
              refine ⟨156877821666790886502501989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 418340857778109030673338637 156877821666790886502501989)
              ·
                refine ⟨29414591562523291219219123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156877821666790886502501989 29414591562523291219219123)
                ·
                  refine ⟨44121887343784936828828685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29414591562523291219219123 44121887343784936828828685)
                  ·
                    refine ⟨16545707753919351310810757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44121887343784936828828685 16545707753919351310810757)
                    ·
                      refine ⟨3102320203859878370777017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16545707753919351310810757 3102320203859878370777017)
                      ·
                        rfl

theorem cell23_6041747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 3, 4].length) (baseStart_6041747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041747 prefixEnd_6041747 := by exact prefixLift 6041747
  have htrace : WordTrace (prefixWord ++ tailWord_6041747) baseStart_6041747 baseEnd_6041747 := by
    simpa [prefixWord, tailWord_6041747, baseEnd_6041747] using wordTrace_append hprefix tailTrace_6041747
  have hstable : (prefixWord ++ tailWord_6041747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041747).length < 2 ^ (prefixWord ++ tailWord_6041747).sum := by decide
  have hdescent : baseEnd_6041747 < baseStart_6041747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041761 : List Nat := [1, 2, 3, 3, 1, 4, 1, 1, 2, 5]
def baseStart_6041761 : Nat := 118140960795 + 6041761 * 2 ^ 59
def prefixEnd_6041761 : Nat := 4983230072969 + 3 ^ 40 * 6041761 * 2
def baseEnd_6041761 : Nat := 1034109130863013772000651

theorem tailTrace_6041761 : CollatzResearch.WordTrace tailWord_6041761 prefixEnd_6041761 1034109130863013772000651 := by
  unfold tailWord_6041761
  simp only [CollatzResearch.WordTrace]
  refine ⟨220361127064739222474085137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146907418043159481649390091 220361127064739222474085137)
  ·
    refine ⟨165270845298554416855563853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220361127064739222474085137 165270845298554416855563853)
    ·
      refine ⟨61976566986957906320836445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165270845298554416855563853 61976566986957906320836445)
      ·
        refine ⟨23241212620109214870313667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61976566986957906320836445 23241212620109214870313667)
        ·
          refine ⟨34861818930163822305470501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23241212620109214870313667 34861818930163822305470501)
          ·
            refine ⟨6536591049405716682275719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34861818930163822305470501 6536591049405716682275719)
            ·
              refine ⟨9804886574108575023413579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6536591049405716682275719 9804886574108575023413579)
              ·
                refine ⟨14707329861162862535120369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9804886574108575023413579 14707329861162862535120369)
                ·
                  refine ⟨11030497395872146901340277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14707329861162862535120369 11030497395872146901340277)
                  ·
                    refine ⟨1034109130863013772000651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11030497395872146901340277 1034109130863013772000651)
                    ·
                      rfl

theorem cell23_6041761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_6041761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041761 prefixEnd_6041761 := by exact prefixLift 6041761
  have htrace : WordTrace (prefixWord ++ tailWord_6041761) baseStart_6041761 baseEnd_6041761 := by
    simpa [prefixWord, tailWord_6041761, baseEnd_6041761] using wordTrace_append hprefix tailTrace_6041761
  have hstable : (prefixWord ++ tailWord_6041761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041761).length < 2 ^ (prefixWord ++ tailWord_6041761).sum := by decide
  have hdescent : baseEnd_6041761 < baseStart_6041761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041784 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 4, 2, 3]
def baseStart_6041784 : Nat := 118140960795 + 6041784 * 2 ^ 59
def prefixEnd_6041784 : Nat := 4983230072969 + 3 ^ 40 * 6041784 * 2
def baseEnd_6041784 : Nat := 3102339202644094726014347

theorem tailTrace_6041784 : CollatzResearch.WordTrace tailWord_6041784 prefixEnd_6041784 3102339202644094726014347 := by
  unfold tailWord_6041784
  simp only [CollatzResearch.WordTrace]
  refine ⟨110180982971827948701086203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146907977295770598268114937 110180982971827948701086203)
  ·
    refine ⟨165271474457741923051629305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110180982971827948701086203 165271474457741923051629305)
    ·
      refine ⟨123953605843306442288721979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165271474457741923051629305 123953605843306442288721979)
      ·
        refine ⟨185930408764959663433082969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123953605843306442288721979 185930408764959663433082969)
        ·
          refine ⟨139447806573719747574812227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185930408764959663433082969 139447806573719747574812227)
          ·
            refine ⟨209171709860579621362218341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139447806573719747574812227 209171709860579621362218341)
            ·
              refine ⟨39219695598858679005415939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 209171709860579621362218341 39219695598858679005415939)
              ·
                refine ⟨58829543398288018508123909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39219695598858679005415939 58829543398288018508123909)
                ·
                  refine ⟨11030539387179003470273233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58829543398288018508123909 11030539387179003470273233)
                  ·
                    refine ⟨8272904540384252602704925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11030539387179003470273233 8272904540384252602704925)
                    ·
                      refine ⟨3102339202644094726014347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8272904540384252602704925 3102339202644094726014347)
                      ·
                        rfl

theorem cell23_6041784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_6041784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041784 prefixEnd_6041784 := by exact prefixLift 6041784
  have htrace : WordTrace (prefixWord ++ tailWord_6041784) baseStart_6041784 baseEnd_6041784 := by
    simpa [prefixWord, tailWord_6041784, baseEnd_6041784] using wordTrace_append hprefix tailTrace_6041784
  have hstable : (prefixWord ++ tailWord_6041784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041784).length < 2 ^ (prefixWord ++ tailWord_6041784).sum := by decide
  have hdescent : baseEnd_6041784 < baseStart_6041784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041787 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 8]
def baseStart_6041787 : Nat := 118140960795 + 6041787 * 2 ^ 59
def prefixEnd_6041787 : Nat := 4983230072969 + 3 ^ 40 * 6041787 * 2
def baseEnd_6041787 : Nat := 344704527009562023808537

theorem tailTrace_6041787 : CollatzResearch.WordTrace tailWord_6041787 prefixEnd_6041787 344704527009562023808537 := by
  unfold tailWord_6041787
  simp only [CollatzResearch.WordTrace]
  refine ⟨220362075362645028914531615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146908050241763352609687743 220362075362645028914531615)
  ·
    refine ⟨330543113043967543371797423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220362075362645028914531615 330543113043967543371797423)
    ·
      refine ⟨495814669565951315057696135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330543113043967543371797423 495814669565951315057696135)
      ·
        refine ⟨743722004348926972586544203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495814669565951315057696135 743722004348926972586544203)
        ·
          refine ⟨1115583006523390458879816305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743722004348926972586544203 1115583006523390458879816305)
          ·
            refine ⟨836687254892542844159862229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1115583006523390458879816305 836687254892542844159862229)
            ·
              refine ⟨19609857536543972909996771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 836687254892542844159862229 19609857536543972909996771)
              ·
                refine ⟨29414786304815959364995157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19609857536543972909996771 29414786304815959364995157)
                ·
                  refine ⟨344704527009562023808537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29414786304815959364995157 344704527009562023808537)
                  ·
                    rfl

theorem cell23_6041787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 8].length) (baseStart_6041787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041787 prefixEnd_6041787 := by exact prefixLift 6041787
  have htrace : WordTrace (prefixWord ++ tailWord_6041787) baseStart_6041787 baseEnd_6041787 := by
    simpa [prefixWord, tailWord_6041787, baseEnd_6041787] using wordTrace_append hprefix tailTrace_6041787
  have hstable : (prefixWord ++ tailWord_6041787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041787).length < 2 ^ (prefixWord ++ tailWord_6041787).sum := by decide
  have hdescent : baseEnd_6041787 < baseStart_6041787 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041807 : List Nat := [1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 6]
def baseStart_6041807 : Nat := 118140960795 + 6041807 * 2 ^ 59
def prefixEnd_6041807 : Nat := 4983230072969 + 3 ^ 40 * 6041807 * 2
def baseEnd_6041807 : Nat := 3102351012699148136026741

theorem tailTrace_6041807 : CollatzResearch.WordTrace tailWord_6041807 prefixEnd_6041807 3102351012699148136026741 := by
  unfold tailWord_6041807
  simp only [CollatzResearch.WordTrace]
  refine ⟨220362804822572572330259675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146908536548381714886839783 220362804822572572330259675)
  ·
    refine ⟨330544207233858858495389513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220362804822572572330259675 330544207233858858495389513)
    ·
      refine ⟨247908155425394143871542135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330544207233858858495389513 247908155425394143871542135)
      ·
        refine ⟨371862233138091215807313203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247908155425394143871542135 371862233138091215807313203)
        ·
          refine ⟨557793349707136823710969805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371862233138091215807313203 557793349707136823710969805)
          ·
            refine ⟨209172506140176308891613677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 557793349707136823710969805 209172506140176308891613677)
            ·
              refine ⟨78439689802566115834355129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209172506140176308891613677 78439689802566115834355129)
              ·
                refine ⟨58829767351924586875766347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78439689802566115834355129 58829767351924586875766347)
                ·
                  refine ⟨88244651027886880313649521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58829767351924586875766347 88244651027886880313649521)
                  ·
                    refine ⟨66183488270915160235237141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88244651027886880313649521 66183488270915160235237141)
                    ·
                      refine ⟨3102351012699148136026741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66183488270915160235237141 3102351012699148136026741)
                      ·
                        rfl

theorem cell23_6041807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 6].length) (baseStart_6041807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041807 prefixEnd_6041807 := by exact prefixLift 6041807
  have htrace : WordTrace (prefixWord ++ tailWord_6041807) baseStart_6041807 baseEnd_6041807 := by
    simpa [prefixWord, tailWord_6041807, baseEnd_6041807] using wordTrace_append hprefix tailTrace_6041807
  have hstable : (prefixWord ++ tailWord_6041807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041807).length < 2 ^ (prefixWord ++ tailWord_6041807).sum := by decide
  have hdescent : baseEnd_6041807 < baseStart_6041807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041841 : List Nat := [1, 2, 2, 2, 2, 1, 3, 1, 4, 3, 2]
def baseStart_6041841 : Nat := 118140960795 + 6041841 * 2 ^ 59
def prefixEnd_6041841 : Nat := 4983230072969 + 3 ^ 40 * 6041841 * 2
def baseEnd_6041841 : Nat := 3102368471041401003001585

theorem tailTrace_6041841 : CollatzResearch.WordTrace tailWord_6041841 prefixEnd_6041841 3102368471041401003001585 := by
  unfold tailWord_6041841
  simp only [CollatzResearch.WordTrace]
  refine ⟨220364044904449396136997377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146909363269632930757998251 220364044904449396136997377)
  ·
    refine ⟨165273033678337047102748033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220364044904449396136997377 165273033678337047102748033)
    ·
      refine ⟨123954775258752785327061025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165273033678337047102748033 123954775258752785327061025)
      ·
        refine ⟨92966081444064588995295769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123954775258752785327061025 92966081444064588995295769)
        ·
          refine ⟨69724561083048441746471827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92966081444064588995295769 69724561083048441746471827)
          ·
            refine ⟨104586841624572662619707741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69724561083048441746471827 104586841624572662619707741)
            ·
              refine ⟨39220065609214748482390403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104586841624572662619707741 39220065609214748482390403)
              ·
                refine ⟨58830098413822122723585605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39220065609214748482390403 58830098413822122723585605)
                ·
                  refine ⟨11030643452591648010672301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58830098413822122723585605 11030643452591648010672301)
                  ·
                    refine ⟨4136491294721868004002113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11030643452591648010672301 4136491294721868004002113)
                    ·
                      refine ⟨3102368471041401003001585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4136491294721868004002113 3102368471041401003001585)
                      ·
                        rfl

theorem cell23_6041841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 1, 4, 3, 2].length) (baseStart_6041841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041841 prefixEnd_6041841 := by exact prefixLift 6041841
  have htrace : WordTrace (prefixWord ++ tailWord_6041841) baseStart_6041841 baseEnd_6041841 := by
    simpa [prefixWord, tailWord_6041841, baseEnd_6041841] using wordTrace_append hprefix tailTrace_6041841
  have hstable : (prefixWord ++ tailWord_6041841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041841).length < 2 ^ (prefixWord ++ tailWord_6041841).sum := by decide
  have hdescent : baseEnd_6041841 < baseStart_6041841 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041847 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 2, 10]
def baseStart_6041847 : Nat := 118140960795 + 6041847 * 2 ^ 59
def prefixEnd_6041847 : Nat := 4983230072969 + 3 ^ 40 * 6041847 * 2
def baseEnd_6041847 : Nat := 1034123850641775993175519

theorem tailTrace_6041847 : CollatzResearch.WordTrace tailWord_6041847 prefixEnd_6041847 1034123850641775993175519 := by
  unfold tailWord_6041847
  simp only [CollatzResearch.WordTrace]
  refine ⟨220364263742427659161715795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146909509161618439441143863 220364263742427659161715795)
  ·
    refine ⟨330546395613641488742573693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220364263742427659161715795 330546395613641488742573693)
    ·
      refine ⟨123954898355115558278465135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330546395613641488742573693 123954898355115558278465135)
      ·
        refine ⟨185932347532673337417697703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123954898355115558278465135 185932347532673337417697703)
        ·
          refine ⟨278898521299010006126546555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185932347532673337417697703 278898521299010006126546555)
          ·
            refine ⟨418347781948515009189819833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278898521299010006126546555 418347781948515009189819833)
            ·
              refine ⟨313760836461386256892364875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418347781948515009189819833 313760836461386256892364875)
              ·
                refine ⟨470641254692079385338547313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313760836461386256892364875 470641254692079385338547313)
                ·
                  refine ⟨352980941019059539003910485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 470641254692079385338547313 352980941019059539003910485)
                  ·
                    refine ⟨1034123850641775993175519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 352980941019059539003910485 1034123850641775993175519)
                    ·
                      rfl

theorem cell23_6041847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_6041847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041847 prefixEnd_6041847 := by exact prefixLift 6041847
  have htrace : WordTrace (prefixWord ++ tailWord_6041847) baseStart_6041847 baseEnd_6041847 := by
    simpa [prefixWord, tailWord_6041847, baseEnd_6041847] using wordTrace_append hprefix tailTrace_6041847
  have hstable : (prefixWord ++ tailWord_6041847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041847).length < 2 ^ (prefixWord ++ tailWord_6041847).sum := by decide
  have hdescent : baseEnd_6041847 < baseStart_6041847 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041848 : List Nat := [2, 1, 2, 1, 1, 2, 1, 8, 1, 1, 3]
def baseStart_6041848 : Nat := 118140960795 + 6041848 * 2 ^ 59
def prefixEnd_6041848 : Nat := 4983230072969 + 3 ^ 40 * 6041848 * 2
def baseEnd_6041848 : Nat := 3102372065405982475614053

theorem tailTrace_6041848 : CollatzResearch.WordTrace tailWord_6041848 prefixEnd_6041848 3102372065405982475614053 := by
  unfold tailWord_6041848
  simp only [CollatzResearch.WordTrace]
  refine ⟨110182150107712018166251099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146909533476949357555001465 110182150107712018166251099)
  ·
    refine ⟨165273225161568027249376649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110182150107712018166251099 165273225161568027249376649)
    ·
      refine ⟨123954918871176020437032487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165273225161568027249376649 123954918871176020437032487)
      ·
        refine ⟨185932378306764030655548731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123954918871176020437032487 185932378306764030655548731)
        ·
          refine ⟨278898567460146045983323097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185932378306764030655548731 278898567460146045983323097)
          ·
            refine ⟨209173925595109534487492323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278898567460146045983323097 209173925595109534487492323)
            ·
              refine ⟨313760888392664301731238485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209173925595109534487492323 313760888392664301731238485)
              ·
                refine ⟨3676885410851534785912951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 313760888392664301731238485 3676885410851534785912951)
                ·
                  refine ⟨5515328116277302178869427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3676885410851534785912951 5515328116277302178869427)
                  ·
                    refine ⟨8272992174415953268304141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5515328116277302178869427 8272992174415953268304141)
                    ·
                      refine ⟨3102372065405982475614053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8272992174415953268304141 3102372065405982475614053)
                      ·
                        rfl

theorem cell23_6041848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 8, 1, 1, 3].length) (baseStart_6041848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041848 prefixEnd_6041848 := by exact prefixLift 6041848
  have htrace : WordTrace (prefixWord ++ tailWord_6041848) baseStart_6041848 baseEnd_6041848 := by
    simpa [prefixWord, tailWord_6041848, baseEnd_6041848] using wordTrace_append hprefix tailTrace_6041848
  have hstable : (prefixWord ++ tailWord_6041848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041848).length < 2 ^ (prefixWord ++ tailWord_6041848).sum := by decide
  have hdescent : baseEnd_6041848 < baseStart_6041848 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041885 : List Nat := [1, 4, 2, 3, 2, 1, 3, 1, 1, 5]
def baseStart_6041885 : Nat := 118140960795 + 6041885 * 2 ^ 59
def prefixEnd_6041885 : Nat := 4983230072969 + 3 ^ 40 * 6041885 * 2
def baseEnd_6041885 : Nat := 1034130354730066276950461

theorem tailTrace_6041885 : CollatzResearch.WordTrace tailWord_6041885 prefixEnd_6041885 1034130354730066276950461 := by
  unfold tailWord_6041885
  simp only [CollatzResearch.WordTrace]
  refine ⟨220365649716289991651599109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146910433144193327767732739 220365649716289991651599109)
  ·
    refine ⟨41318559321804373434674833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220365649716289991651599109 41318559321804373434674833)
    ·
      refine ⟨30988919491353280076006125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41318559321804373434674833 30988919491353280076006125)
      ·
        refine ⟨11620844809257480028502297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30988919491353280076006125 11620844809257480028502297)
        ·
          refine ⟨8715633606943110021376723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11620844809257480028502297 8715633606943110021376723)
          ·
            refine ⟨13073450410414665032065085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8715633606943110021376723 13073450410414665032065085)
            ·
              refine ⟨4902543903905499387024407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13073450410414665032065085 4902543903905499387024407)
              ·
                refine ⟨7353815855858249080536611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4902543903905499387024407 7353815855858249080536611)
                ·
                  refine ⟨11030723783787373620804917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7353815855858249080536611 11030723783787373620804917)
                  ·
                    refine ⟨1034130354730066276950461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11030723783787373620804917 1034130354730066276950461)
                    ·
                      rfl

theorem cell23_6041885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_6041885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041885 prefixEnd_6041885 := by exact prefixLift 6041885
  have htrace : WordTrace (prefixWord ++ tailWord_6041885) baseStart_6041885 baseEnd_6041885 := by
    simpa [prefixWord, tailWord_6041885, baseEnd_6041885] using wordTrace_append hprefix tailTrace_6041885
  have hstable : (prefixWord ++ tailWord_6041885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041885).length < 2 ^ (prefixWord ++ tailWord_6041885).sum := by decide
  have hdescent : baseEnd_6041885 < baseStart_6041885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041908 : List Nat := [2, 5, 1, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_6041908 : Nat := 118140960795 + 6041908 * 2 ^ 59
def prefixEnd_6041908 : Nat := 4983230072969 + 3 ^ 40 * 6041908 * 2
def baseEnd_6041908 : Nat := 3102402874245252240863777

theorem tailTrace_6041908 : CollatzResearch.WordTrace tailWord_6041908 prefixEnd_6041908 3102402874245252240863777 := by
  unfold tailWord_6041908
  simp only [CollatzResearch.WordTrace]
  refine ⟨110183244297603333289843189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146910992396804444386457585 110183244297603333289843189)
  ·
    refine ⟨10329679152900312495922799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110183244297603333289843189 10329679152900312495922799)
    ·
      refine ⟨15494518729350468743884199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10329679152900312495922799 15494518729350468743884199)
      ·
        refine ⟨23241778094025703115826299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15494518729350468743884199 23241778094025703115826299)
        ·
          refine ⟨34862667141038554673739449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23241778094025703115826299 34862667141038554673739449)
          ·
            refine ⟨26147000355778916005304587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34862667141038554673739449 26147000355778916005304587)
            ·
              refine ⟨39220500533668374007956881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26147000355778916005304587 39220500533668374007956881)
              ·
                refine ⟨29415375400251280505967661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39220500533668374007956881 29415375400251280505967661)
                ·
                  refine ⟨11030765775094230189737873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29415375400251280505967661 11030765775094230189737873)
                  ·
                    refine ⟨8273074331320672642303405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11030765775094230189737873 8273074331320672642303405)
                    ·
                      refine ⟨3102402874245252240863777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8273074331320672642303405 3102402874245252240863777)
                      ·
                        rfl

theorem cell23_6041908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_6041908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041908 prefixEnd_6041908 := by exact prefixLift 6041908
  have htrace : WordTrace (prefixWord ++ tailWord_6041908) baseStart_6041908 baseEnd_6041908 := by
    simpa [prefixWord, tailWord_6041908, baseEnd_6041908] using wordTrace_append hprefix tailTrace_6041908
  have hstable : (prefixWord ++ tailWord_6041908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041908).length < 2 ^ (prefixWord ++ tailWord_6041908).sum := by decide
  have hdescent : baseEnd_6041908 < baseStart_6041908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041918 : List Nat := [4, 2, 1, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_6041918 : Nat := 118140960795 + 6041918 * 2 ^ 59
def prefixEnd_6041918 : Nat := 4983230072969 + 3 ^ 40 * 6041918 * 2
def baseEnd_6041918 : Nat := 3102408009051797201738731

theorem tailTrace_6041918 : CollatzResearch.WordTrace tailWord_6041918 prefixEnd_6041918 3102408009051797201738731 := by
  unfold tailWord_6041918
  simp only [CollatzResearch.WordTrace]
  refine ⟨27545856665646304785943801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146911235550113625525033605 27545856665646304785943801)
  ·
    refine ⟨20659392499234728589457851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27545856665646304785943801 20659392499234728589457851)
    ·
      refine ⟨30989088748852092884186777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20659392499234728589457851 30989088748852092884186777)
      ·
        refine ⟨23241816561639069663140083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30989088748852092884186777 23241816561639069663140083)
        ·
          refine ⟨34862724842458604494710125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23241816561639069663140083 34862724842458604494710125)
          ·
            refine ⟨13073521815921976685516297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34862724842458604494710125 13073521815921976685516297)
            ·
              refine ⟨9805141361941482514137223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13073521815921976685516297 9805141361941482514137223)
              ·
                refine ⟨14707712042912223771205835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9805141361941482514137223 14707712042912223771205835)
                ·
                  refine ⟨22061568064368335656808753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14707712042912223771205835 22061568064368335656808753)
                  ·
                    refine ⟨16546176048276251742606565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22061568064368335656808753 16546176048276251742606565)
                    ·
                      refine ⟨3102408009051797201738731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16546176048276251742606565 3102408009051797201738731)
                      ·
                        rfl

theorem cell23_6041918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_6041918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041918 prefixEnd_6041918 := by exact prefixLift 6041918
  have htrace : WordTrace (prefixWord ++ tailWord_6041918) baseStart_6041918 baseEnd_6041918 := by
    simpa [prefixWord, tailWord_6041918, baseEnd_6041918] using wordTrace_append hprefix tailTrace_6041918
  have hstable : (prefixWord ++ tailWord_6041918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041918).length < 2 ^ (prefixWord ++ tailWord_6041918).sum := by decide
  have hdescent : baseEnd_6041918 < baseStart_6041918 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041944 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 1, 5, 4]
def baseStart_6041944 : Nat := 118140960795 + 6041944 * 2 ^ 59
def prefixEnd_6041944 : Nat := 4983230072969 + 3 ^ 40 * 6041944 * 2
def baseEnd_6041944 : Nat := 3102421359548814100013611

theorem tailTrace_6041944 : CollatzResearch.WordTrace tailWord_6041944 prefixEnd_6041944 3102421359548814100013611 := by
  unfold tailWord_6041944
  simp only [CollatzResearch.WordTrace]
  refine ⟨110183900811538122363998443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146911867748717496485331257 110183900811538122363998443)
  ·
    refine ⟨165275851217307183545997665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110183900811538122363998443 165275851217307183545997665)
    ·
      refine ⟨123956888412980387659498249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165275851217307183545997665 123956888412980387659498249)
      ·
        refine ⟨92967666309735290744623687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123956888412980387659498249 92967666309735290744623687)
        ·
          refine ⟨139451499464602936116935531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92967666309735290744623687 139451499464602936116935531)
          ·
            refine ⟨209177249196904404175403297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139451499464602936116935531 209177249196904404175403297)
            ·
              refine ⟨156882936897678303131552473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209177249196904404175403297 156882936897678303131552473)
              ·
                refine ⟨117662202673258727348664355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156882936897678303131552473 117662202673258727348664355)
                ·
                  refine ⟨176493304009888091022996533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 117662202673258727348664355 176493304009888091022996533)
                  ·
                    refine ⟨16546247250927008533405925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 176493304009888091022996533 16546247250927008533405925)
                    ·
                      refine ⟨3102421359548814100013611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16546247250927008533405925 3102421359548814100013611)
                      ·
                        rfl

theorem cell23_6041944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_6041944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041944 prefixEnd_6041944 := by exact prefixLift 6041944
  have htrace : WordTrace (prefixWord ++ tailWord_6041944) baseStart_6041944 baseEnd_6041944 := by
    simpa [prefixWord, tailWord_6041944, baseEnd_6041944] using wordTrace_append hprefix tailTrace_6041944
  have hstable : (prefixWord ++ tailWord_6041944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041944).length < 2 ^ (prefixWord ++ tailWord_6041944).sum := by decide
  have hdescent : baseEnd_6041944 < baseStart_6041944 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041978 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2]
def baseStart_6041978 : Nat := 118140960795 + 6041978 * 2 ^ 59
def prefixEnd_6041978 : Nat := 4983230072969 + 3 ^ 40 * 6041978 * 2
def baseEnd_6041978 : Nat := 3102438817891066966988455

theorem tailTrace_6041978 : CollatzResearch.WordTrace tailWord_6041978 prefixEnd_6041978 3102438817891066966988455 := by
  unfold tailWord_6041978
  simp only [CollatzResearch.WordTrace]
  refine ⟨55092260426238267133683647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146912694469968712356489725 55092260426238267133683647)
  ·
    refine ⟨82638390639357400700525471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55092260426238267133683647 82638390639357400700525471)
    ·
      refine ⟨123957585959036101050788207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82638390639357400700525471 123957585959036101050788207)
      ·
        refine ⟨185936378938554151576182311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123957585959036101050788207 185936378938554151576182311)
        ·
          refine ⟨278904568407831227364273467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185936378938554151576182311 278904568407831227364273467)
          ·
            refine ⟨418356852611746841046410201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278904568407831227364273467 418356852611746841046410201)
            ·
              refine ⟨313767639458810130784807651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418356852611746841046410201 313767639458810130784807651)
              ·
                refine ⟨470651459188215196177211477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313767639458810130784807651 470651459188215196177211477)
                ·
                  refine ⟨5515446787361896830201697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 470651459188215196177211477 5515446787361896830201697)
                  ·
                    refine ⟨4136585090521422622651273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5515446787361896830201697 4136585090521422622651273)
                    ·
                      refine ⟨3102438817891066966988455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4136585090521422622651273 3102438817891066966988455)
                      ·
                        rfl

theorem cell23_6041978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 8, 2, 2].length) (baseStart_6041978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041978 prefixEnd_6041978 := by exact prefixLift 6041978
  have htrace : WordTrace (prefixWord ++ tailWord_6041978) baseStart_6041978 baseEnd_6041978 := by
    simpa [prefixWord, tailWord_6041978, baseEnd_6041978] using wordTrace_append hprefix tailTrace_6041978
  have hstable : (prefixWord ++ tailWord_6041978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041978).length < 2 ^ (prefixWord ++ tailWord_6041978).sum := by decide
  have hdescent : baseEnd_6041978 < baseStart_6041978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6041998 : List Nat := [4, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5]
def baseStart_6041998 : Nat := 118140960795 + 6041998 * 2 ^ 59
def prefixEnd_6041998 : Nat := 4983230072969 + 3 ^ 40 * 6041998 * 2
def baseEnd_6041998 : Nat := 3102449087504156888738363

theorem tailTrace_6041998 : CollatzResearch.WordTrace tailWord_6041998 prefixEnd_6041998 3102449087504156888738363 := by
  unfold tailWord_6041998
  simp only [CollatzResearch.WordTrace]
  refine ⟨27546221395610076493807831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146913180776587074633641765 27546221395610076493807831)
  ·
    refine ⟨41319332093415114740711747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27546221395610076493807831 41319332093415114740711747)
    ·
      refine ⟨61978998140122672111067621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41319332093415114740711747 61978998140122672111067621)
      ·
        refine ⟨11621062151273001020825179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61978998140122672111067621 11621062151273001020825179)
        ·
          refine ⟨17431593226909501531237769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11621062151273001020825179 17431593226909501531237769)
          ·
            refine ⟨13073694920182126148428327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17431593226909501531237769 13073694920182126148428327)
            ·
              refine ⟨19610542380273189222642491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13073694920182126148428327 19610542380273189222642491)
              ·
                refine ⟨29415813570409783833963737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19610542380273189222642491 29415813570409783833963737)
                ·
                  refine ⟨22061860177807337875472803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29415813570409783833963737 22061860177807337875472803)
                  ·
                    refine ⟨33092790266711006813209205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22061860177807337875472803 33092790266711006813209205)
                    ·
                      refine ⟨3102449087504156888738363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33092790266711006813209205 3102449087504156888738363)
                      ·
                        rfl

theorem cell23_6041998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_6041998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6041998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6041998 prefixEnd_6041998 := by exact prefixLift 6041998
  have htrace : WordTrace (prefixWord ++ tailWord_6041998) baseStart_6041998 baseEnd_6041998 := by
    simpa [prefixWord, tailWord_6041998, baseEnd_6041998] using wordTrace_append hprefix tailTrace_6041998
  have hstable : (prefixWord ++ tailWord_6041998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6041998).length < 2 ^ (prefixWord ++ tailWord_6041998).sum := by decide
  have hdescent : baseEnd_6041998 < baseStart_6041998 := by decide
  rcases family_descends (prefixWord ++ tailWord_6041998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042029 : List Nat := [1, 5, 2, 2, 2, 1, 1, 3, 2, 2, 2]
def baseStart_6042029 : Nat := 118140960795 + 6042029 * 2 ^ 59
def prefixEnd_6042029 : Nat := 4983230072969 + 3 ^ 40 * 6042029 * 2
def baseEnd_6042029 : Nat := 3102465005404446267450721

theorem tailTrace_6042029 : CollatzResearch.WordTrace tailWord_6042029 prefixEnd_6042029 3102465005404446267450721 := by
  unfold tailWord_6042029
  simp only [CollatzResearch.WordTrace]
  refine ⟨220370901827768304244841141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146913934551845536163227427 220370901827768304244841141)
  ·
    refine ⟨20659772046353278522953857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220370901827768304244841141 20659772046353278522953857)
    ·
      refine ⟨15494829034764958892215393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20659772046353278522953857 15494829034764958892215393)
      ·
        refine ⟨11621121776073719169161545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15494829034764958892215393 11621121776073719169161545)
        ·
          refine ⟨8715841332055289376871159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11621121776073719169161545 8715841332055289376871159)
          ·
            refine ⟨13073761998082934065306739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8715841332055289376871159 13073761998082934065306739)
            ·
              refine ⟨19610642997124401097960109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13073761998082934065306739 19610642997124401097960109)
              ·
                refine ⟨7353991123921650411735041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19610642997124401097960109 7353991123921650411735041)
                ·
                  refine ⟨5515493342941237808801281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7353991123921650411735041 5515493342941237808801281)
                  ·
                    refine ⟨4136620007205928356600961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5515493342941237808801281 4136620007205928356600961)
                    ·
                      refine ⟨3102465005404446267450721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4136620007205928356600961 3102465005404446267450721)
                      ·
                        rfl

theorem cell23_6042029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_6042029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042029 prefixEnd_6042029 := by exact prefixLift 6042029
  have htrace : WordTrace (prefixWord ++ tailWord_6042029) baseStart_6042029 baseEnd_6042029 := by
    simpa [prefixWord, tailWord_6042029, baseEnd_6042029] using wordTrace_append hprefix tailTrace_6042029
  have hstable : (prefixWord ++ tailWord_6042029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042029).length < 2 ^ (prefixWord ++ tailWord_6042029).sum := by decide
  have hdescent : baseEnd_6042029 < baseStart_6042029 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042071 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 3]
def baseStart_6042071 : Nat := 118140960795 + 6042071 * 2 ^ 59
def prefixEnd_6042071 : Nat := 4983230072969 + 3 ^ 40 * 6042071 * 2
def baseEnd_6042071 : Nat := 3102486571591935103125527

theorem tailTrace_6042071 : CollatzResearch.WordTrace tailWord_6042071 prefixEnd_6042071 3102486571591935103125527 := by
  unfold tailWord_6042071
  simp only [CollatzResearch.WordTrace]
  refine ⟨220372433693616145417870067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146914955795744096945246711 220372433693616145417870067)
  ·
    refine ⟨330558650540424218126805101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220372433693616145417870067 330558650540424218126805101)
    ·
      refine ⟨123959493952659081797551913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330558650540424218126805101 123959493952659081797551913)
      ·
        refine ⟨92969620464494311348163935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123959493952659081797551913 92969620464494311348163935)
        ·
          refine ⟨139454430696741467022245903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92969620464494311348163935 139454430696741467022245903)
          ·
            refine ⟨209181646045112200533368855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139454430696741467022245903 209181646045112200533368855)
            ·
              refine ⟨313772469067668300800053283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209181646045112200533368855 313772469067668300800053283)
              ·
                refine ⟨470658703601502451200079925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313772469067668300800053283 470658703601502451200079925)
                ·
                  refine ⟨44124253462640854800007493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 470658703601502451200079925 44124253462640854800007493)
                  ·
                    refine ⟨8273297524245160275001405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44124253462640854800007493 8273297524245160275001405)
                    ·
                      refine ⟨3102486571591935103125527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8273297524245160275001405 3102486571591935103125527)
                      ·
                        rfl

theorem cell23_6042071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 5, 4, 3].length) (baseStart_6042071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042071 prefixEnd_6042071 := by exact prefixLift 6042071
  have htrace : WordTrace (prefixWord ++ tailWord_6042071) baseStart_6042071 baseEnd_6042071 := by
    simpa [prefixWord, tailWord_6042071, baseEnd_6042071] using wordTrace_append hprefix tailTrace_6042071
  have hstable : (prefixWord ++ tailWord_6042071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042071).length < 2 ^ (prefixWord ++ tailWord_6042071).sum := by decide
  have hdescent : baseEnd_6042071 < baseStart_6042071 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042091 : List Nat := [1, 1, 1, 1, 2, 3, 3, 5, 6]
def baseStart_6042091 : Nat := 118140960795 + 6042091 * 2 ^ 59
def prefixEnd_6042091 : Nat := 4983230072969 + 3 ^ 40 * 6042091 * 2
def baseEnd_6042091 : Nat := 344721871245002780541715

theorem tailTrace_6042091 : CollatzResearch.WordTrace tailWord_6042091 prefixEnd_6042091 344721871245002780541715 := by
  unfold tailWord_6042091
  simp only [CollatzResearch.WordTrace]
  refine ⟨220373163153543688833598127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146915442102362459222398751 220373163153543688833598127)
  ·
    refine ⟨330559744730315533250397191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220373163153543688833598127 330559744730315533250397191)
    ·
      refine ⟨495839617095473299875595787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330559744730315533250397191 495839617095473299875595787)
      ·
        refine ⟨743759425643209949813393681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495839617095473299875595787 743759425643209949813393681)
        ·
          refine ⟨557819569232407462360045261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 743759425643209949813393681 557819569232407462360045261)
          ·
            refine ⟨209182338462152798385016973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 557819569232407462360045261 209182338462152798385016973)
            ·
              refine ⟨78443376923307299394381365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209182338462152798385016973 78443376923307299394381365)
              ·
                refine ⟨7354066586560059318223253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78443376923307299394381365 7354066586560059318223253)
                ·
                  refine ⟨344721871245002780541715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7354066586560059318223253 344721871245002780541715)
                  ·
                    rfl

theorem cell23_6042091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 6].length) (baseStart_6042091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042091 prefixEnd_6042091 := by exact prefixLift 6042091
  have htrace : WordTrace (prefixWord ++ tailWord_6042091) baseStart_6042091 baseEnd_6042091 := by
    simpa [prefixWord, tailWord_6042091, baseEnd_6042091] using wordTrace_append hprefix tailTrace_6042091
  have hstable : (prefixWord ++ tailWord_6042091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042091).length < 2 ^ (prefixWord ++ tailWord_6042091).sum := by decide
  have hdescent : baseEnd_6042091 < baseStart_6042091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042121 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 5, 5]
def baseStart_6042121 : Nat := 118140960795 + 6042121 * 2 ^ 59
def prefixEnd_6042121 : Nat := 4983230072969 + 3 ^ 40 * 6042121 * 2
def baseEnd_6042121 : Nat := 1034170748541553302500099

theorem tailTrace_6042121 : CollatzResearch.WordTrace tailWord_6042121 prefixEnd_6042121 1034170748541553302500099 := by
  unfold tailWord_6042121
  simp only [CollatzResearch.WordTrace]
  refine ⟨220374257343435003957190217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146916171562290002638126811 220374257343435003957190217)
  ·
    refine ⟨165280693007576252967892663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220374257343435003957190217 165280693007576252967892663)
    ·
      refine ⟨247921039511364379451838995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165280693007576252967892663 247921039511364379451838995)
      ·
        refine ⟨371881559267046569177758493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247921039511364379451838995 371881559267046569177758493)
        ·
          refine ⟨139455584725142463441659435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371881559267046569177758493 139455584725142463441659435)
          ·
            refine ⟨209183377087713695162489153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139455584725142463441659435 209183377087713695162489153)
            ·
              refine ⟨156887532815785271371866865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209183377087713695162489153 156887532815785271371866865)
              ·
                refine ⟨117665649611838953528900149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156887532815785271371866865 117665649611838953528900149)
                ·
                  refine ⟨11031154651109901893334389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117665649611838953528900149 11031154651109901893334389)
                  ·
                    refine ⟨1034170748541553302500099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11031154651109901893334389 1034170748541553302500099)
                    ·
                      rfl

theorem cell23_6042121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 5, 5].length) (baseStart_6042121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042121 prefixEnd_6042121 := by exact prefixLift 6042121
  have htrace : WordTrace (prefixWord ++ tailWord_6042121) baseStart_6042121 baseEnd_6042121 := by
    simpa [prefixWord, tailWord_6042121, baseEnd_6042121] using wordTrace_append hprefix tailTrace_6042121
  have hstable : (prefixWord ++ tailWord_6042121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042121).length < 2 ^ (prefixWord ++ tailWord_6042121).sum := by decide
  have hdescent : baseEnd_6042121 < baseStart_6042121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042152 : List Nat := [2, 1, 5, 2, 1, 1, 2, 2, 3, 1, 3]
def baseStart_6042152 : Nat := 118140960795 + 6042152 * 2 ^ 59
def prefixEnd_6042152 : Nat := 4983230072969 + 3 ^ 40 * 6042152 * 2
def baseEnd_6042152 : Nat := 3102528163524949286212655

theorem tailTrace_6042152 : CollatzResearch.WordTrace tailWord_6042152 prefixEnd_6042152 3102528163524949286212655 := by
  unfold tailWord_6042152
  simp only [CollatzResearch.WordTrace]
  refine ⟨110187694003161348125784355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146916925337548464167712473 110187694003161348125784355)
  ·
    refine ⟨165281541004742022188676533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110187694003161348125784355 165281541004742022188676533)
    ·
      refine ⟨15495144469194564580188425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 165281541004742022188676533 15495144469194564580188425)
      ·
        refine ⟨11621358351895923435141319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15495144469194564580188425 11621358351895923435141319)
        ·
          refine ⟨17432037527843885152711979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11621358351895923435141319 17432037527843885152711979)
          ·
            refine ⟨26148056291765827729067969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17432037527843885152711979 26148056291765827729067969)
            ·
              refine ⟨19611042218824370796800977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26148056291765827729067969 19611042218824370796800977)
              ·
                refine ⟨14708281664118278097600733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19611042218824370796800977 14708281664118278097600733)
                ·
                  refine ⟨5515605624044354286600275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14708281664118278097600733 5515605624044354286600275)
                  ·
                    refine ⟨8273408436066531429900413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5515605624044354286600275 8273408436066531429900413)
                    ·
                      refine ⟨3102528163524949286212655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8273408436066531429900413 3102528163524949286212655)
                      ·
                        rfl

theorem cell23_6042152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_6042152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042152 prefixEnd_6042152 := by exact prefixLift 6042152
  have htrace : WordTrace (prefixWord ++ tailWord_6042152) baseStart_6042152 baseEnd_6042152 := by
    simpa [prefixWord, tailWord_6042152, baseEnd_6042152] using wordTrace_append hprefix tailTrace_6042152
  have hstable : (prefixWord ++ tailWord_6042152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042152).length < 2 ^ (prefixWord ++ tailWord_6042152).sum := by decide
  have hdescent : baseEnd_6042152 < baseStart_6042152 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042168 : List Nat := [2, 1, 2, 1, 4, 1, 1, 1, 6, 4]
def baseStart_6042168 : Nat := 118140960795 + 6042168 * 2 ^ 59
def prefixEnd_6042168 : Nat := 4983230072969 + 3 ^ 40 * 6042168 * 2
def baseEnd_6042168 : Nat := 1034178793071807074537527

theorem tailTrace_6042168 : CollatzResearch.WordTrace tailWord_6042168 prefixEnd_6042168 1034178793071807074537527 := by
  unfold tailWord_6042168
  simp only [CollatzResearch.WordTrace]
  refine ⟨110187985787132365492075579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146917314382843153989434105 110187985787132365492075579)
  ·
    refine ⟨165281978680698548238113369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110187985787132365492075579 165281978680698548238113369)
    ·
      refine ⟨123961484010523911178585027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165281978680698548238113369 123961484010523911178585027)
      ·
        refine ⟨185942226015785866767877541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123961484010523911178585027 185942226015785866767877541)
        ·
          refine ⟨34864167377959850018977039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185942226015785866767877541 34864167377959850018977039)
          ·
            refine ⟨52296251066939775028465559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34864167377959850018977039 52296251066939775028465559)
            ·
              refine ⟨78444376600409662542698339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52296251066939775028465559 78444376600409662542698339)
              ·
                refine ⟨117666564900614493814047509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78444376600409662542698339 117666564900614493814047509)
                ·
                  refine ⟨5515620229716304397533477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117666564900614493814047509 5515620229716304397533477)
                  ·
                    refine ⟨1034178793071807074537527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5515620229716304397533477 1034178793071807074537527)
                    ·
                      rfl

theorem cell23_6042168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 1, 6, 4].length) (baseStart_6042168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042168 prefixEnd_6042168 := by exact prefixLift 6042168
  have htrace : WordTrace (prefixWord ++ tailWord_6042168) baseStart_6042168 baseEnd_6042168 := by
    simpa [prefixWord, tailWord_6042168, baseEnd_6042168] using wordTrace_append hprefix tailTrace_6042168
  have hstable : (prefixWord ++ tailWord_6042168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042168).length < 2 ^ (prefixWord ++ tailWord_6042168).sum := by decide
  have hdescent : baseEnd_6042168 < baseStart_6042168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042181 : List Nat := [1, 3, 1, 1, 1, 5, 11]
def baseStart_6042181 : Nat := 118140960795 + 6042181 * 2 ^ 59
def prefixEnd_6042181 : Nat := 4983230072969 + 3 ^ 40 * 6042181 * 2
def baseEnd_6042181 : Nat := 38303000672394193490741

theorem tailTrace_6042181 : CollatzResearch.WordTrace tailWord_6042181 prefixEnd_6042181 38303000672394193490741 := by
  unfold tailWord_6042181
  simp only [CollatzResearch.WordTrace]
  refine ⟨220376445723217634204374397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146917630482145089469582931 220376445723217634204374397)
  ·
    refine ⟨82641167146206612826640399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220376445723217634204374397 82641167146206612826640399)
    ·
      refine ⟨123961750719309919239960599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82641167146206612826640399 123961750719309919239960599)
      ·
        refine ⟨185942626078964878859940899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123961750719309919239960599 185942626078964878859940899)
        ·
          refine ⟨278913939118447318289911349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185942626078964878859940899 278913939118447318289911349)
          ·
            refine ⟨26148181792354436089679189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 278913939118447318289911349 26148181792354436089679189)
            ·
              refine ⟨38303000672394193490741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 26148181792354436089679189 38303000672394193490741)
              ·
                rfl

theorem cell23_6042181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 11].length) (baseStart_6042181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042181 prefixEnd_6042181 := by exact prefixLift 6042181
  have htrace : WordTrace (prefixWord ++ tailWord_6042181) baseStart_6042181 baseEnd_6042181 := by
    simpa [prefixWord, tailWord_6042181, baseEnd_6042181] using wordTrace_append hprefix tailTrace_6042181
  have hstable : (prefixWord ++ tailWord_6042181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042181).length < 2 ^ (prefixWord ++ tailWord_6042181).sum := by decide
  have hdescent : baseEnd_6042181 < baseStart_6042181 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042229 : List Nat := [1, 3, 4, 2, 3, 1, 1, 1, 1, 1, 5]
def baseStart_6042229 : Nat := 118140960795 + 6042229 * 2 ^ 59
def prefixEnd_6042229 : Nat := 4983230072969 + 3 ^ 40 * 6042229 * 2
def baseEnd_6042229 : Nat := 3102567701535345484949801

theorem tailTrace_6042229 : CollatzResearch.WordTrace tailWord_6042229 prefixEnd_6042229 3102567701535345484949801 := by
  unfold tailWord_6042229
  simp only [CollatzResearch.WordTrace]
  refine ⟨220378196427043738402121741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146918797618029158934747827 220378196427043738402121741)
  ·
    refine ⟨82641823660141401900795653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220378196427043738402121741 82641823660141401900795653)
    ·
      refine ⟨15495341936276512856399185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82641823660141401900795653 15495341936276512856399185)
      ·
        refine ⟨11621506452207384642299389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15495341936276512856399185 11621506452207384642299389)
        ·
          refine ⟨4358064919577769240862271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11621506452207384642299389 4358064919577769240862271)
          ·
            refine ⟨6537097379366653861293407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4358064919577769240862271 6537097379366653861293407)
            ·
              refine ⟨9805646069049980791940111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6537097379366653861293407 9805646069049980791940111)
              ·
                refine ⟨14708469103574971187910167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9805646069049980791940111 14708469103574971187910167)
                ·
                  refine ⟨22062703655362456781865251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14708469103574971187910167 22062703655362456781865251)
                  ·
                    refine ⟨33094055483043685172797877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22062703655362456781865251 33094055483043685172797877)
                    ·
                      refine ⟨3102567701535345484949801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33094055483043685172797877 3102567701535345484949801)
                      ·
                        rfl

theorem cell23_6042229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_6042229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042229 prefixEnd_6042229 := by exact prefixLift 6042229
  have htrace : WordTrace (prefixWord ++ tailWord_6042229) baseStart_6042229 baseEnd_6042229 := by
    simpa [prefixWord, tailWord_6042229, baseEnd_6042229] using wordTrace_append hprefix tailTrace_6042229
  have hstable : (prefixWord ++ tailWord_6042229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042229).length < 2 ^ (prefixWord ++ tailWord_6042229).sum := by decide
  have hdescent : baseEnd_6042229 < baseStart_6042229 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042286 : List Nat := [4, 1, 4, 1, 1, 2, 1, 3, 1, 3, 2]
def baseStart_6042286 : Nat := 118140960795 + 6042286 * 2 ^ 59
def prefixEnd_6042286 : Nat := 4983230072969 + 3 ^ 40 * 6042286 * 2
def baseEnd_6042286 : Nat := 3102596969932651761937039

theorem tailTrace_6042286 : CollatzResearch.WordTrace tailWord_6042286 prefixEnd_6042286 3102596969932651761937039 := by
  unfold tailWord_6042286
  simp only [CollatzResearch.WordTrace]
  refine ⟨27547534423479654642118339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146920183591891491424631141 27547534423479654642118339)
  ·
    refine ⟨41321301635219481963177509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27547534423479654642118339 41321301635219481963177509)
    ·
      refine ⟨7747744056603652868095783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 41321301635219481963177509 7747744056603652868095783)
      ·
        refine ⟨11621616084905479302143675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7747744056603652868095783 11621616084905479302143675)
        ·
          refine ⟨17432424127358218953215513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11621616084905479302143675 17432424127358218953215513)
          ·
            refine ⟨13074318095518664214911635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17432424127358218953215513 13074318095518664214911635)
            ·
              refine ⟨19611477143277996322367453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13074318095518664214911635 19611477143277996322367453)
              ·
                refine ⟨7354303928729248620887795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19611477143277996322367453 7354303928729248620887795)
                ·
                  refine ⟨11031455893093872931331693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7354303928729248620887795 11031455893093872931331693)
                  ·
                    refine ⟨4136795959910202349249385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11031455893093872931331693 4136795959910202349249385)
                    ·
                      refine ⟨3102596969932651761937039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4136795959910202349249385 3102596969932651761937039)
                      ·
                        rfl

theorem cell23_6042286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_6042286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042286 prefixEnd_6042286 := by exact prefixLift 6042286
  have htrace : WordTrace (prefixWord ++ tailWord_6042286) baseStart_6042286 baseEnd_6042286 := by
    simpa [prefixWord, tailWord_6042286, baseEnd_6042286] using wordTrace_append hprefix tailTrace_6042286
  have hstable : (prefixWord ++ tailWord_6042286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042286).length < 2 ^ (prefixWord ++ tailWord_6042286).sum := by decide
  have hdescent : baseEnd_6042286 < baseStart_6042286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042310 : List Nat := [6, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_6042310 : Nat := 118140960795 + 6042310 * 2 ^ 59
def prefixEnd_6042310 : Nat := 4983230072969 + 3 ^ 40 * 6042310 * 2
def baseEnd_6042310 : Nat := 3102609293468359668036929

theorem tailTrace_6042310 : CollatzResearch.WordTrace tailWord_6042310 prefixEnd_6042310 3102609293468359668036929 := by
  unfold tailWord_6042310
  simp only [CollatzResearch.WordTrace]
  refine ⟨6886910960617196538619387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 146920767159833526157213589 6886910960617196538619387)
  ·
    refine ⟨10330366440925794807929081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6886910960617196538619387 10330366440925794807929081)
    ·
      refine ⟨7747774830694346105946811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10330366440925794807929081 7747774830694346105946811)
      ·
        refine ⟨11621662246041519158920217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7747774830694346105946811 11621662246041519158920217)
        ·
          refine ⟨8716246684531139369190163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11621662246041519158920217 8716246684531139369190163)
          ·
            refine ⟨13074370026796709053785245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8716246684531139369190163 13074370026796709053785245)
            ·
              refine ⟨4902888760048765895169467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13074370026796709053785245 4902888760048765895169467)
              ·
                refine ⟨7354333140073148842754201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4902888760048765895169467 7354333140073148842754201)
                ·
                  refine ⟨5515749855054861632065651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7354333140073148842754201 5515749855054861632065651)
                  ·
                    refine ⟨8273624782582292448098477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5515749855054861632065651 8273624782582292448098477)
                    ·
                      refine ⟨3102609293468359668036929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8273624782582292448098477 3102609293468359668036929)
                      ·
                        rfl

theorem cell23_6042310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_6042310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042310 prefixEnd_6042310 := by exact prefixLift 6042310
  have htrace : WordTrace (prefixWord ++ tailWord_6042310) baseStart_6042310 baseEnd_6042310 := by
    simpa [prefixWord, tailWord_6042310, baseEnd_6042310] using wordTrace_append hprefix tailTrace_6042310
  have hstable : (prefixWord ++ tailWord_6042310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042310).length < 2 ^ (prefixWord ++ tailWord_6042310).sum := by decide
  have hdescent : baseEnd_6042310 < baseStart_6042310 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042339 : List Nat := [1, 1, 1, 7, 1, 3, 1, 3, 5]
def baseStart_6042339 : Nat := 118140960795 + 6042339 * 2 ^ 59
def prefixEnd_6042339 : Nat := 4983230072969 + 3 ^ 40 * 6042339 * 2
def baseEnd_6042339 : Nat := 344736020489704450508255

theorem tailTrace_6042339 : CollatzResearch.WordTrace tailWord_6042339 prefixEnd_6042339 344736020489704450508255 := by
  unfold tailWord_6042339
  simp only [CollatzResearch.WordTrace]
  refine ⟨220382208456645227188626071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146921472304430151459084047 220382208456645227188626071)
  ·
    refine ⟨330573312684967840782939107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220382208456645227188626071 330573312684967840782939107)
    ·
      refine ⟨495859969027451761174408661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330573312684967840782939107 495859969027451761174408661)
      ·
        refine ⟨11621718024080900652525203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 495859969027451761174408661 11621718024080900652525203)
        ·
          refine ⟨17432577036121350978787805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11621718024080900652525203 17432577036121350978787805)
          ·
            refine ⟨6537216388545506617045427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17432577036121350978787805 6537216388545506617045427)
            ·
              refine ⟨9805824582818259925568141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6537216388545506617045427 9805824582818259925568141)
              ·
                refine ⟨3677184218556847472088053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9805824582818259925568141 3677184218556847472088053)
                ·
                  refine ⟨344736020489704450508255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3677184218556847472088053 344736020489704450508255)
                  ·
                    rfl

theorem cell23_6042339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 5].length) (baseStart_6042339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042339 prefixEnd_6042339 := by exact prefixLift 6042339
  have htrace : WordTrace (prefixWord ++ tailWord_6042339) baseStart_6042339 baseEnd_6042339 := by
    simpa [prefixWord, tailWord_6042339, baseEnd_6042339] using wordTrace_append hprefix tailTrace_6042339
  have hstable : (prefixWord ++ tailWord_6042339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042339).length < 2 ^ (prefixWord ++ tailWord_6042339).sum := by decide
  have hdescent : baseEnd_6042339 < baseStart_6042339 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042356 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 7]
def baseStart_6042356 : Nat := 118140960795 + 6042356 * 2 ^ 59
def prefixEnd_6042356 : Nat := 4983230072969 + 3 ^ 40 * 6042356 * 2
def baseEnd_6042356 : Nat := 344736990397607387562413

theorem tailTrace_6042356 : CollatzResearch.WordTrace tailWord_6042356 prefixEnd_6042356 344736990397607387562413 := by
  unfold tailWord_6042356
  simp only [CollatzResearch.WordTrace]
  refine ⟨110191414248791819545997461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146921885665055759394663281 110191414248791819545997461)
  ·
    refine ⟨5165222542912116541218631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110191414248791819545997461 5165222542912116541218631)
    ·
      refine ⟨7747833814368174811827947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5165222542912116541218631 7747833814368174811827947)
      ·
        refine ⟨11621750721552262217741921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7747833814368174811827947 11621750721552262217741921)
        ·
          refine ⟨8716313041164196663306441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11621750721552262217741921 8716313041164196663306441)
          ·
            refine ⟨6537234780873147497479831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8716313041164196663306441 6537234780873147497479831)
            ·
              refine ⟨9805852171309721246219747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6537234780873147497479831 9805852171309721246219747)
              ·
                refine ⟨14708778256964581869329621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9805852171309721246219747 14708778256964581869329621)
                ·
                  refine ⟨344736990397607387562413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14708778256964581869329621 344736990397607387562413)
                  ·
                    rfl

theorem cell23_6042356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_6042356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042356 prefixEnd_6042356 := by exact prefixLift 6042356
  have htrace : WordTrace (prefixWord ++ tailWord_6042356) baseStart_6042356 baseEnd_6042356 := by
    simpa [prefixWord, tailWord_6042356, baseEnd_6042356] using wordTrace_append hprefix tailTrace_6042356
  have hstable : (prefixWord ++ tailWord_6042356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042356).length < 2 ^ (prefixWord ++ tailWord_6042356).sum := by decide
  have hdescent : baseEnd_6042356 < baseStart_6042356 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042372 : List Nat := [2, 3, 2, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_6042372 : Nat := 118140960795 + 6042372 * 2 ^ 59
def prefixEnd_6042372 : Nat := 4983230072969 + 3 ^ 40 * 6042372 * 2
def baseEnd_6042372 : Nat := 3102641129268938425461643

theorem tailTrace_6042372 : CollatzResearch.WordTrace tailWord_6042372 prefixEnd_6042372 3102641129268938425461643 := by
  unfold tailWord_6042372
  simp only [CollatzResearch.WordTrace]
  refine ⟨110191706032762836912288685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146922274710350449216384913 110191706032762836912288685)
  ·
    refine ⟨41321889762286063842108257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110191706032762836912288685 41321889762286063842108257)
    ·
      refine ⟨30991417321714547881581193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41321889762286063842108257 30991417321714547881581193)
      ·
        refine ⟨23243562991285910911185895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30991417321714547881581193 23243562991285910911185895)
        ·
          refine ⟨34865344486928866366778843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23243562991285910911185895 34865344486928866366778843)
          ·
            refine ⟨52298016730393299550168265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34865344486928866366778843 52298016730393299550168265)
            ·
              refine ⟨39223512547794974662626199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52298016730393299550168265 39223512547794974662626199)
              ·
                refine ⟨58835268821692461993939299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39223512547794974662626199 58835268821692461993939299)
                ·
                  refine ⟨88252903232538692990908949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58835268821692461993939299 88252903232538692990908949)
                  ·
                    refine ⟨4136854839025251233948857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 88252903232538692990908949 4136854839025251233948857)
                    ·
                      refine ⟨3102641129268938425461643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4136854839025251233948857 3102641129268938425461643)
                      ·
                        rfl

theorem cell23_6042372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_6042372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042372 prefixEnd_6042372 := by exact prefixLift 6042372
  have htrace : WordTrace (prefixWord ++ tailWord_6042372) baseStart_6042372 baseEnd_6042372 := by
    simpa [prefixWord, tailWord_6042372, baseEnd_6042372] using wordTrace_append hprefix tailTrace_6042372
  have hstable : (prefixWord ++ tailWord_6042372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042372).length < 2 ^ (prefixWord ++ tailWord_6042372).sum := by decide
  have hdescent : baseEnd_6042372 < baseStart_6042372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042432 : List Nat := [2, 1, 1, 2, 2, 1, 1, 4, 4, 3, 2]
def baseStart_6042432 : Nat := 118140960795 + 6042432 * 2 ^ 59
def prefixEnd_6042432 : Nat := 4983230072969 + 3 ^ 40 * 6042432 * 2
def baseEnd_6042432 : Nat := 3102671938108208190711367

theorem tailTrace_6042432 : CollatzResearch.WordTrace tailWord_6042432 prefixEnd_6042432 3102671938108208190711367 := by
  unfold tailWord_6042432
  simp only [CollatzResearch.WordTrace]
  refine ⟨110192800222654152035880775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146923733630205536047841033 110192800222654152035880775)
  ·
    refine ⟨165289200333981228053821163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110192800222654152035880775 165289200333981228053821163)
    ·
      refine ⟨247933800500971842080731745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165289200333981228053821163 247933800500971842080731745)
      ·
        refine ⟨185950350375728881560548809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247933800500971842080731745 185950350375728881560548809)
        ·
          refine ⟨139462762781796661170411607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185950350375728881560548809 139462762781796661170411607)
          ·
            refine ⟨209194144172694991755617411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139462762781796661170411607 209194144172694991755617411)
            ·
              refine ⟨313791216259042487633426117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209194144172694991755617411 313791216259042487633426117)
              ·
                refine ⟨58835853048570466431267397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313791216259042487633426117 58835853048570466431267397)
                ·
                  refine ⟨11031722446606962455862637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58835853048570466431267397 11031722446606962455862637)
                  ·
                    refine ⟨4136895917477610920948489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11031722446606962455862637 4136895917477610920948489)
                    ·
                      refine ⟨3102671938108208190711367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4136895917477610920948489 3102671938108208190711367)
                      ·
                        rfl

theorem cell23_6042432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 4, 4, 3, 2].length) (baseStart_6042432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042432 prefixEnd_6042432 := by exact prefixLift 6042432
  have htrace : WordTrace (prefixWord ++ tailWord_6042432) baseStart_6042432 baseEnd_6042432 := by
    simpa [prefixWord, tailWord_6042432, baseEnd_6042432] using wordTrace_append hprefix tailTrace_6042432
  have hstable : (prefixWord ++ tailWord_6042432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042432).length < 2 ^ (prefixWord ++ tailWord_6042432).sum := by decide
  have hdescent : baseEnd_6042432 < baseStart_6042432 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042449 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 1, 5, 2]
def baseStart_6042449 : Nat := 118140960795 + 6042449 * 2 ^ 59
def prefixEnd_6042449 : Nat := 4983230072969 + 3 ^ 40 * 6042449 * 2
def baseEnd_6042449 : Nat := 3102680667279334624198789

theorem tailTrace_6042449 : CollatzResearch.WordTrace tailWord_6042449 prefixEnd_6042449 3102680667279334624198789 := by
  unfold tailWord_6042449
  simp only [CollatzResearch.WordTrace]
  refine ⟨220386220486246715975130401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146924146990831143983420267 220386220486246715975130401)
  ·
    refine ⟨165289665364685036981347801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220386220486246715975130401 165289665364685036981347801)
    ·
      refine ⟨123967249023513777736010851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165289665364685036981347801 123967249023513777736010851)
      ·
        refine ⟨185950873535270666604016277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123967249023513777736010851 185950873535270666604016277)
        ·
          refine ⟨8716447196965812497063263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 185950873535270666604016277 8716447196965812497063263)
          ·
            refine ⟨13074670795448718745594895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8716447196965812497063263 13074670795448718745594895)
            ·
              refine ⟨19612006193173078118392343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13074670795448718745594895 19612006193173078118392343)
              ·
                refine ⟨29418009289759617177588515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19612006193173078118392343 29418009289759617177588515)
                ·
                  refine ⟨44127013934639425766382773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29418009289759617177588515 44127013934639425766382773)
                  ·
                    refine ⟨4136907556372446165598385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44127013934639425766382773 4136907556372446165598385)
                    ·
                      refine ⟨3102680667279334624198789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4136907556372446165598385 3102680667279334624198789)
                      ·
                        rfl

theorem cell23_6042449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 1, 5, 2].length) (baseStart_6042449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042449 prefixEnd_6042449 := by exact prefixLift 6042449
  have htrace : WordTrace (prefixWord ++ tailWord_6042449) baseStart_6042449 baseEnd_6042449 := by
    simpa [prefixWord, tailWord_6042449, baseEnd_6042449] using wordTrace_append hprefix tailTrace_6042449
  have hstable : (prefixWord ++ tailWord_6042449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042449).length < 2 ^ (prefixWord ++ tailWord_6042449).sum := by decide
  have hdescent : baseEnd_6042449 < baseStart_6042449 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042475 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 4]
def baseStart_6042475 : Nat := 118140960795 + 6042475 * 2 ^ 59
def prefixEnd_6042475 : Nat := 4983230072969 + 3 ^ 40 * 6042475 * 2
def baseEnd_6042475 : Nat := 3102694017776351522473669

theorem tailTrace_6042475 : CollatzResearch.WordTrace tailWord_6042475 prefixEnd_6042475 3102694017776351522473669 := by
  unfold tailWord_6042475
  simp only [CollatzResearch.WordTrace]
  refine ⟨220387168784152522415576879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146924779189435014943717919 220387168784152522415576879)
  ·
    refine ⟨330580753176228783623365319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220387168784152522415576879 330580753176228783623365319)
    ·
      refine ⟨495871129764343175435047979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330580753176228783623365319 495871129764343175435047979)
      ·
        refine ⟨743806694646514763152571969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495871129764343175435047979 743806694646514763152571969)
        ·
          refine ⟨557855020984886072364428977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 743806694646514763152571969 557855020984886072364428977)
          ·
            refine ⟨418391265738664554273321733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557855020984886072364428977 418391265738664554273321733)
            ·
              refine ⟨78448362325999603926247825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 418391265738664554273321733 78448362325999603926247825)
              ·
                refine ⟨58836271744499702944685869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78448362325999603926247825 58836271744499702944685869)
                ·
                  refine ⟨22063601904187388604257201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58836271744499702944685869 22063601904187388604257201)
                  ·
                    refine ⟨16547701428140541453192901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22063601904187388604257201 16547701428140541453192901)
                    ·
                      refine ⟨3102694017776351522473669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16547701428140541453192901 3102694017776351522473669)
                      ·
                        rfl

theorem cell23_6042475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 4].length) (baseStart_6042475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042475 prefixEnd_6042475 := by exact prefixLift 6042475
  have htrace : WordTrace (prefixWord ++ tailWord_6042475) baseStart_6042475 baseEnd_6042475 := by
    simpa [prefixWord, tailWord_6042475, baseEnd_6042475] using wordTrace_append hprefix tailTrace_6042475
  have hstable : (prefixWord ++ tailWord_6042475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042475).length < 2 ^ (prefixWord ++ tailWord_6042475).sum := by decide
  have hdescent : baseEnd_6042475 < baseStart_6042475 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042482 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 5, 2, 3]
def baseStart_6042482 : Nat := 118140960795 + 6042482 * 2 ^ 59
def prefixEnd_6042482 : Nat := 4983230072969 + 3 ^ 40 * 6042482 * 2
def baseEnd_6042482 : Nat := 3102697612140932995086137

theorem tailTrace_6042482 : CollatzResearch.WordTrace tailWord_6042482 prefixEnd_6042482 3102697612140932995086137 := by
  unfold tailWord_6042482
  simp only [CollatzResearch.WordTrace]
  refine ⟨55096856023781790652770425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146924949396751441740721133 55096856023781790652770425)
  ·
    refine ⟨41322642017836342989577819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55096856023781790652770425 41322642017836342989577819)
    ·
      refine ⟨61983963026754514484366729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41322642017836342989577819 61983963026754514484366729)
      ·
        refine ⟨46487972270065885863275047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61983963026754514484366729 46487972270065885863275047)
        ·
          refine ⟨69731958405098828794912571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46487972270065885863275047 69731958405098828794912571)
          ·
            refine ⟨104597937607648243192368857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69731958405098828794912571 104597937607648243192368857)
            ·
              refine ⟨78448453205736182394276643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104597937607648243192368857 78448453205736182394276643)
              ·
                refine ⟨117672679808604273591414965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78448453205736182394276643 117672679808604273591414965)
                ·
                  refine ⟨11031813732056650649195153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 117672679808604273591414965 11031813732056650649195153)
                  ·
                    refine ⟨8273860299042487986896365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11031813732056650649195153 8273860299042487986896365)
                    ·
                      refine ⟨3102697612140932995086137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8273860299042487986896365 3102697612140932995086137)
                      ·
                        rfl

theorem cell23_6042482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_6042482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042482 prefixEnd_6042482 := by exact prefixLift 6042482
  have htrace : WordTrace (prefixWord ++ tailWord_6042482) baseStart_6042482 baseEnd_6042482 := by
    simpa [prefixWord, tailWord_6042482, baseEnd_6042482] using wordTrace_append hprefix tailTrace_6042482
  have hstable : (prefixWord ++ tailWord_6042482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042482).length < 2 ^ (prefixWord ++ tailWord_6042482).sum := by decide
  have hdescent : baseEnd_6042482 < baseStart_6042482 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042499 : List Nat := [1, 1, 1, 3, 4, 1, 4, 2, 1, 2, 3]
def baseStart_6042499 : Nat := 118140960795 + 6042499 * 2 ^ 59
def prefixEnd_6042499 : Nat := 4983230072969 + 3 ^ 40 * 6042499 * 2
def baseEnd_6042499 : Nat := 3102706341312059428573559

theorem tailTrace_6042499 : CollatzResearch.WordTrace tailWord_6042499 prefixEnd_6042499 3102706341312059428573559 := by
  unfold tailWord_6042499
  simp only [CollatzResearch.WordTrace]
  refine ⟨220388044136065574514450551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146925362757377049676300367 220388044136065574514450551)
  ·
    refine ⟨330582066204098361771675827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220388044136065574514450551 330582066204098361771675827)
    ·
      refine ⟨495873099306147542657513741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330582066204098361771675827 495873099306147542657513741)
      ·
        refine ⟨185952412239805328496567653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 495873099306147542657513741 185952412239805328496567653)
        ·
          refine ⟨34866077294963499093106435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 185952412239805328496567653 34866077294963499093106435)
          ·
            refine ⟨52299115942445248639659653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34866077294963499093106435 52299115942445248639659653)
            ·
              refine ⟨9806084239208484119936185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52299115942445248639659653 9806084239208484119936185)
              ·
                refine ⟨7354563179406363089952139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9806084239208484119936185 7354563179406363089952139)
                ·
                  refine ⟨11031844769109544634928209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7354563179406363089952139 11031844769109544634928209)
                  ·
                    refine ⟨8273883576832158476196157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11031844769109544634928209 8273883576832158476196157)
                    ·
                      refine ⟨3102706341312059428573559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8273883576832158476196157 3102706341312059428573559)
                      ·
                        rfl

theorem cell23_6042499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 4, 2, 1, 2, 3].length) (baseStart_6042499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042499 prefixEnd_6042499 := by exact prefixLift 6042499
  have htrace : WordTrace (prefixWord ++ tailWord_6042499) baseStart_6042499 baseEnd_6042499 := by
    simpa [prefixWord, tailWord_6042499, baseEnd_6042499] using wordTrace_append hprefix tailTrace_6042499
  have hstable : (prefixWord ++ tailWord_6042499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042499).length < 2 ^ (prefixWord ++ tailWord_6042499).sum := by decide
  have hdescent : baseEnd_6042499 < baseStart_6042499 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042550 : List Nat := [5, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_6042550 : Nat := 118140960795 + 6042550 * 2 ^ 59
def prefixEnd_6042550 : Nat := 4983230072969 + 3 ^ 40 * 6042550 * 2
def baseEnd_6042550 : Nat := 3102732528825438729035825

theorem tailTrace_6042550 : CollatzResearch.WordTrace tailWord_6042550 prefixEnd_6042550 3102732528825438729035825 := by
  unfold tailWord_6042550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13774369016180050639034819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146926602839253873483038069 13774369016180050639034819)
  ·
    refine ⟨20661553524270075958552229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13774369016180050639034819 20661553524270075958552229)
    ·
      refine ⟨3874041285800639242228543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20661553524270075958552229 3874041285800639242228543)
      ·
        refine ⟨5811061928700958863342815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3874041285800639242228543 5811061928700958863342815)
        ·
          refine ⟨8716592893051438295014223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5811061928700958863342815 8716592893051438295014223)
          ·
            refine ⟨13074889339577157442521335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8716592893051438295014223 13074889339577157442521335)
            ·
              refine ⟨19612334009365736163782003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13074889339577157442521335 19612334009365736163782003)
              ·
                refine ⟨29418501014048604245673005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19612334009365736163782003 29418501014048604245673005)
                ·
                  refine ⟨11031937880268226592127377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29418501014048604245673005 11031937880268226592127377)
                  ·
                    refine ⟨8273953410201169944095533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11031937880268226592127377 8273953410201169944095533)
                    ·
                      refine ⟨3102732528825438729035825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8273953410201169944095533 3102732528825438729035825)
                      ·
                        rfl

theorem cell23_6042550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_6042550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042550 prefixEnd_6042550 := by exact prefixLift 6042550
  have htrace : WordTrace (prefixWord ++ tailWord_6042550) baseStart_6042550 baseEnd_6042550 := by
    simpa [prefixWord, tailWord_6042550, baseEnd_6042550] using wordTrace_append hprefix tailTrace_6042550
  have hstable : (prefixWord ++ tailWord_6042550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042550).length < 2 ^ (prefixWord ++ tailWord_6042550).sum := by decide
  have hdescent : baseEnd_6042550 < baseStart_6042550 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042565 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 6]
def baseStart_6042565 : Nat := 118140960795 + 6042565 * 2 ^ 59
def prefixEnd_6042565 : Nat := 4983230072969 + 3 ^ 40 * 6042565 * 2
def baseEnd_6042565 : Nat := 3102740231035256170348255

theorem tailTrace_6042565 : CollatzResearch.WordTrace tailWord_6042565 prefixEnd_6042565 3102740231035256170348255 := by
  unfold tailWord_6042565
  simp only [CollatzResearch.WordTrace]
  refine ⟨220390451353826467786353149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146926967569217645190902099 220390451353826467786353149)
  ·
    refine ⟨82646419257684925419882431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220390451353826467786353149 82646419257684925419882431)
    ·
      refine ⟨123969628886527388129823647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82646419257684925419882431 123969628886527388129823647)
      ·
        refine ⟨185954443329791082194735471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123969628886527388129823647 185954443329791082194735471)
        ·
          refine ⟨278931664994686623292103207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185954443329791082194735471 278931664994686623292103207)
          ·
            refine ⟨418397497492029934938154811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278931664994686623292103207 418397497492029934938154811)
            ·
              refine ⟨627596246238044902407232217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418397497492029934938154811 627596246238044902407232217)
              ·
                refine ⟨470697184678533676805424163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 627596246238044902407232217 470697184678533676805424163)
                ·
                  refine ⟨706045777017800515208136245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 470697184678533676805424163 706045777017800515208136245)
                  ·
                    refine ⟨66191791595418798300762773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 706045777017800515208136245 66191791595418798300762773)
                    ·
                      refine ⟨3102740231035256170348255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66191791595418798300762773 3102740231035256170348255)
                      ·
                        rfl

theorem cell23_6042565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5, 6].length) (baseStart_6042565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042565 prefixEnd_6042565 := by exact prefixLift 6042565
  have htrace : WordTrace (prefixWord ++ tailWord_6042565) baseStart_6042565 baseEnd_6042565 := by
    simpa [prefixWord, tailWord_6042565, baseEnd_6042565] using wordTrace_append hprefix tailTrace_6042565
  have hstable : (prefixWord ++ tailWord_6042565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042565).length < 2 ^ (prefixWord ++ tailWord_6042565).sum := by decide
  have hdescent : baseEnd_6042565 < baseStart_6042565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042572 : List Nat := [2, 2, 1, 4, 1, 1, 1, 3, 2, 1, 5]
def baseStart_6042572 : Nat := 118140960795 + 6042572 * 2 ^ 59
def prefixEnd_6042572 : Nat := 4983230072969 + 3 ^ 40 * 6042572 * 2
def baseEnd_6042572 : Nat := 3102743825399837642960723

theorem tailTrace_6042572 : CollatzResearch.WordTrace tailWord_6042572 prefixEnd_6042572 3102743825399837642960723 := by
  unfold tailWord_6042572
  simp only [CollatzResearch.WordTrace]
  refine ⟨110195353332400553990928985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146927137776534071987905313 110195353332400553990928985)
  ·
    refine ⟨82646514999300415493196739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110195353332400553990928985 82646514999300415493196739)
    ·
      refine ⟨123969772498950623239795109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82646514999300415493196739 123969772498950623239795109)
      ·
        refine ⟨23244332343553241857461583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123969772498950623239795109 23244332343553241857461583)
        ·
          refine ⟨34866498515329862786192375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23244332343553241857461583 34866498515329862786192375)
          ·
            refine ⟨52299747772994794179288563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34866498515329862786192375 52299747772994794179288563)
            ·
              refine ⟨78449621659492191268932845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52299747772994794179288563 78449621659492191268932845)
              ·
                refine ⟨29418608122309571725849817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78449621659492191268932845 29418608122309571725849817)
                ·
                  refine ⟨22063956091732178794387363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29418608122309571725849817 22063956091732178794387363)
                  ·
                    refine ⟨33095934137598268191581045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22063956091732178794387363 33095934137598268191581045)
                    ·
                      refine ⟨3102743825399837642960723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33095934137598268191581045 3102743825399837642960723)
                      ·
                        rfl

theorem cell23_6042572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_6042572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042572 prefixEnd_6042572 := by exact prefixLift 6042572
  have htrace : WordTrace (prefixWord ++ tailWord_6042572) baseStart_6042572 baseEnd_6042572 := by
    simpa [prefixWord, tailWord_6042572, baseEnd_6042572] using wordTrace_append hprefix tailTrace_6042572
  have hstable : (prefixWord ++ tailWord_6042572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042572).length < 2 ^ (prefixWord ++ tailWord_6042572).sum := by decide
  have hdescent : baseEnd_6042572 < baseStart_6042572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042589 : List Nat := [1, 4, 3, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_6042589 : Nat := 118140960795 + 6042589 * 2 ^ 59
def prefixEnd_6042589 : Nat := 4983230072969 + 3 ^ 40 * 6042589 * 2
def baseEnd_6042589 : Nat := 3102752554570964076448145

theorem tailTrace_6042589 : CollatzResearch.WordTrace tailWord_6042589 prefixEnd_6042589 3102752554570964076448145 := by
  unfold tailWord_6042589
  simp only [CollatzResearch.WordTrace]
  refine ⟨220391326705739519885226821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146927551137159679923484547 220391326705739519885226821)
  ·
    refine ⟨41323373757326159978480029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220391326705739519885226821 41323373757326159978480029)
    ·
      refine ⟨15496265158997309991930011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41323373757326159978480029 15496265158997309991930011)
      ·
        refine ⟨23244397738495964987895017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15496265158997309991930011 23244397738495964987895017)
        ·
          refine ⟨17433298303871973740921263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23244397738495964987895017 17433298303871973740921263)
          ·
            refine ⟨26149947455807960611381895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17433298303871973740921263 26149947455807960611381895)
            ·
              refine ⟨39224921183711940917072843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26149947455807960611381895 39224921183711940917072843)
              ·
                refine ⟨58837381775567911375609265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39224921183711940917072843 58837381775567911375609265)
                ·
                  refine ⟨44128036331675933531706949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58837381775567911375609265 44128036331675933531706949)
                  ·
                    refine ⟨8274006812189237537195053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 44128036331675933531706949 8274006812189237537195053)
                    ·
                      refine ⟨3102752554570964076448145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8274006812189237537195053 3102752554570964076448145)
                      ·
                        rfl

theorem cell23_6042589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_6042589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042589 prefixEnd_6042589 := by exact prefixLift 6042589
  have htrace : WordTrace (prefixWord ++ tailWord_6042589) baseStart_6042589 baseEnd_6042589 := by
    simpa [prefixWord, tailWord_6042589, baseEnd_6042589] using wordTrace_append hprefix tailTrace_6042589
  have hstable : (prefixWord ++ tailWord_6042589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042589).length < 2 ^ (prefixWord ++ tailWord_6042589).sum := by decide
  have hdescent : baseEnd_6042589 < baseStart_6042589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042599 : List Nat := [1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 4]
def baseStart_6042599 : Nat := 118140960795 + 6042599 * 2 ^ 59
def prefixEnd_6042599 : Nat := 4983230072969 + 3 ^ 40 * 6042599 * 2
def baseEnd_6042599 : Nat := 3102757689377509037323099

theorem tailTrace_6042599 : CollatzResearch.WordTrace tailWord_6042599 prefixEnd_6042599 3102757689377509037323099 := by
  unfold tailWord_6042599
  simp only [CollatzResearch.WordTrace]
  refine ⟨220391691435703291593090851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146927794290468861062060567 220391691435703291593090851)
  ·
    refine ⟨330587537153554937389636277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220391691435703291593090851 330587537153554937389636277)
    ·
      refine ⟨30992581608145775380278401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 330587537153554937389636277 30992581608145775380278401)
      ·
        refine ⟨23244436206109331535208801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30992581608145775380278401 23244436206109331535208801)
        ·
          refine ⟨17433327154581998651406601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23244436206109331535208801 17433327154581998651406601)
          ·
            refine ⟨13074995365936498988554951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17433327154581998651406601 13074995365936498988554951)
            ·
              refine ⟨19612493048904748482832427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13074995365936498988554951 19612493048904748482832427)
              ·
                refine ⟨29418739573357122724248641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19612493048904748482832427 29418739573357122724248641)
                ·
                  refine ⟨22064054680017842043186481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 29418739573357122724248641 22064054680017842043186481)
                  ·
                    refine ⟨16548041010013381532389861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22064054680017842043186481 16548041010013381532389861)
                    ·
                      refine ⟨3102757689377509037323099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16548041010013381532389861 3102757689377509037323099)
                      ·
                        rfl

theorem cell23_6042599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_6042599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042599 prefixEnd_6042599 := by exact prefixLift 6042599
  have htrace : WordTrace (prefixWord ++ tailWord_6042599) baseStart_6042599 baseEnd_6042599 := by
    simpa [prefixWord, tailWord_6042599, baseEnd_6042599] using wordTrace_append hprefix tailTrace_6042599
  have hstable : (prefixWord ++ tailWord_6042599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042599).length < 2 ^ (prefixWord ++ tailWord_6042599).sum := by decide
  have hdescent : baseEnd_6042599 < baseStart_6042599 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042672 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 4]
def baseStart_6042672 : Nat := 118140960795 + 6042672 * 2 ^ 59
def prefixEnd_6042672 : Nat := 4983230072969 + 3 ^ 40 * 6042672 * 2
def baseEnd_6042672 : Nat := 3102795173465287251710263

theorem tailTrace_6042672 : CollatzResearch.WordTrace tailWord_6042672 prefixEnd_6042672 3102795173465287251710263 := by
  unfold tailWord_6042672
  simp only [CollatzResearch.WordTrace]
  refine ⟨110197176982219412530249135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146929569309625883373665513 110197176982219412530249135)
  ·
    refine ⟨165295765473329118795373703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110197176982219412530249135 165295765473329118795373703)
    ·
      refine ⟨247943648209993678193060555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165295765473329118795373703 247943648209993678193060555)
      ·
        refine ⟨371915472314990517289590833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247943648209993678193060555 371915472314990517289590833)
        ·
          refine ⟨278936604236242887967193125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371915472314990517289590833 278936604236242887967193125)
          ·
            refine ⟨52300613294295541493848711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278936604236242887967193125 52300613294295541493848711)
            ·
              refine ⟨78450919941443312240773067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52300613294295541493848711 78450919941443312240773067)
              ·
                refine ⟨117676379912164968361159601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78450919941443312240773067 117676379912164968361159601)
                ·
                  refine ⟨88257284934123726270869701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117676379912164968361159601 88257284934123726270869701)
                  ·
                    refine ⟨16548240925148198675788069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88257284934123726270869701 16548240925148198675788069)
                    ·
                      refine ⟨3102795173465287251710263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16548240925148198675788069 3102795173465287251710263)
                      ·
                        rfl

theorem cell23_6042672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 4].length) (baseStart_6042672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042672 prefixEnd_6042672 := by exact prefixLift 6042672
  have htrace : WordTrace (prefixWord ++ tailWord_6042672) baseStart_6042672 baseEnd_6042672 := by
    simpa [prefixWord, tailWord_6042672, baseEnd_6042672] using wordTrace_append hprefix tailTrace_6042672
  have hstable : (prefixWord ++ tailWord_6042672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042672).length < 2 ^ (prefixWord ++ tailWord_6042672).sum := by decide
  have hdescent : baseEnd_6042672 < baseStart_6042672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042676 : List Nat := [2, 5, 1, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_6042676 : Nat := 118140960795 + 6042676 * 2 ^ 59
def prefixEnd_6042676 : Nat := 4983230072969 + 3 ^ 40 * 6042676 * 2
def baseEnd_6042676 : Nat := 3102797227387905236060245

theorem tailTrace_6042676 : CollatzResearch.WordTrace tailWord_6042676 prefixEnd_6042676 3102797227387905236060245 := by
  unfold tailWord_6042676
  simp only [CollatzResearch.WordTrace]
  refine ⟨110197249928212166871821941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146929666570949555829095921 110197249928212166871821941)
  ·
    refine ⟨10330992180769890644233307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 110197249928212166871821941 10330992180769890644233307)
    ·
      refine ⟨15496488271154835966349961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10330992180769890644233307 15496488271154835966349961)
      ·
        refine ⟨11622366203366126974762471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15496488271154835966349961 11622366203366126974762471)
        ·
          refine ⟨17433549305049190462143707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11622366203366126974762471 17433549305049190462143707)
          ·
            refine ⟨26150323957573785693215561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17433549305049190462143707 26150323957573785693215561)
            ·
              refine ⟨19612742968180339269911671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26150323957573785693215561 19612742968180339269911671)
              ·
                refine ⟨29419114452270508904867507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19612742968180339269911671 29419114452270508904867507)
                ·
                  refine ⟨44128671678405763357301261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29419114452270508904867507 44128671678405763357301261)
                  ·
                    refine ⟨16548251879402161258987973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44128671678405763357301261 16548251879402161258987973)
                    ·
                      refine ⟨3102797227387905236060245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16548251879402161258987973 3102797227387905236060245)
                      ·
                        rfl

theorem cell23_6042676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_6042676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042676 prefixEnd_6042676 := by exact prefixLift 6042676
  have htrace : WordTrace (prefixWord ++ tailWord_6042676) baseStart_6042676 baseEnd_6042676 := by
    simpa [prefixWord, tailWord_6042676, baseEnd_6042676] using wordTrace_append hprefix tailTrace_6042676
  have hstable : (prefixWord ++ tailWord_6042676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042676).length < 2 ^ (prefixWord ++ tailWord_6042676).sum := by decide
  have hdescent : baseEnd_6042676 < baseStart_6042676 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042679 : List Nat := [1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 3]
def baseStart_6042679 : Nat := 118140960795 + 6042679 * 2 ^ 59
def prefixEnd_6042679 : Nat := 4983230072969 + 3 ^ 40 * 6042679 * 2
def baseEnd_6042679 : Nat := 3102798767829868724322731

theorem tailTrace_6042679 : CollatzResearch.WordTrace tailWord_6042679 prefixEnd_6042679 3102798767829868724322731 := by
  unfold tailWord_6042679
  simp only [CollatzResearch.WordTrace]
  refine ⟨220394609275413465256003091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146929739516942310170668727 220394609275413465256003091)
  ·
    refine ⟨330591913913120197884004637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220394609275413465256003091 330591913913120197884004637)
    ·
      refine ⟨123971967717420074206501739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330591913913120197884004637 123971967717420074206501739)
      ·
        refine ⟨185957951576130111309752609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123971967717420074206501739 185957951576130111309752609)
        ·
          refine ⟨139468463682097583482314457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185957951576130111309752609 139468463682097583482314457)
          ·
            refine ⟨104601347761573187611735843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139468463682097583482314457 104601347761573187611735843)
            ·
              refine ⟨156902021642359781417603765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104601347761573187611735843 156902021642359781417603765)
              ·
                refine ⟨14709564528971229507900353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156902021642359781417603765 14709564528971229507900353)
                ·
                  refine ⟨11032173396728422130925265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14709564528971229507900353 11032173396728422130925265)
                  ·
                    refine ⟨8274130047546316598193949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11032173396728422130925265 8274130047546316598193949)
                    ·
                      refine ⟨3102798767829868724322731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8274130047546316598193949 3102798767829868724322731)
                      ·
                        rfl

theorem cell23_6042679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 5, 2, 2, 3].length) (baseStart_6042679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042679 prefixEnd_6042679 := by exact prefixLift 6042679
  have htrace : WordTrace (prefixWord ++ tailWord_6042679) baseStart_6042679 baseEnd_6042679 := by
    simpa [prefixWord, tailWord_6042679, baseEnd_6042679] using wordTrace_append hprefix tailTrace_6042679
  have hstable : (prefixWord ++ tailWord_6042679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042679).length < 2 ^ (prefixWord ++ tailWord_6042679).sum := by decide
  have hdescent : baseEnd_6042679 < baseStart_6042679 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042682 : List Nat := [3, 1, 1, 1, 3, 1, 3, 2, 8]
def baseStart_6042682 : Nat := 118140960795 + 6042682 * 2 ^ 59
def prefixEnd_6042682 : Nat := 4983230072969 + 3 ^ 40 * 6042682 * 2
def baseEnd_6042682 : Nat := 344755589807981356953913

theorem tailTrace_6042682 : CollatzResearch.WordTrace tailWord_6042682 prefixEnd_6042682 344755589807981356953913 := by
  unfold tailWord_6042682
  simp only [CollatzResearch.WordTrace]
  refine ⟨55098679673600649192090575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146929812462935064512241533 55098679673600649192090575)
  ·
    refine ⟨82648019510400973788135863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55098679673600649192090575 82648019510400973788135863)
    ·
      refine ⟨123972029265601460682203795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82648019510400973788135863 123972029265601460682203795)
      ·
        refine ⟨185958043898402191023305693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123972029265601460682203795 185958043898402191023305693)
        ·
          refine ⟨69734266461900821633739635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185958043898402191023305693 69734266461900821633739635)
          ·
            refine ⟨104601399692851232450609453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69734266461900821633739635 104601399692851232450609453)
            ·
              refine ⟨39225524884819212168978545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104601399692851232450609453 39225524884819212168978545)
              ·
                refine ⟨29419143663614409126733909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39225524884819212168978545 29419143663614409126733909)
                ·
                  refine ⟨344755589807981356953913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29419143663614409126733909 344755589807981356953913)
                  ·
                    rfl

theorem cell23_6042682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_6042682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042682 prefixEnd_6042682 := by exact prefixLift 6042682
  have htrace : WordTrace (prefixWord ++ tailWord_6042682) baseStart_6042682 baseEnd_6042682 := by
    simpa [prefixWord, tailWord_6042682, baseEnd_6042682] using wordTrace_append hprefix tailTrace_6042682
  have hstable : (prefixWord ++ tailWord_6042682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042682).length < 2 ^ (prefixWord ++ tailWord_6042682).sum := by decide
  have hdescent : baseEnd_6042682 < baseStart_6042682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042729 : List Nat := [1, 2, 1, 1, 1, 7, 1, 1, 3, 5]
def baseStart_6042729 : Nat := 118140960795 + 6042729 * 2 ^ 59
def prefixEnd_6042729 : Nat := 4983230072969 + 3 ^ 40 * 6042729 * 2
def baseEnd_6042729 : Nat := 1034274813954197842899167

theorem tailTrace_6042729 : CollatzResearch.WordTrace tailWord_6042729 prefixEnd_6042729 1034274813954197842899167 := by
  unfold tailWord_6042729
  simp only [CollatzResearch.WordTrace]
  refine ⟨220396432925232323795323241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146930955283488215863548827 220396432925232323795323241)
  ·
    refine ⟨165297324693924242846492431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220396432925232323795323241 165297324693924242846492431)
    ·
      refine ⟨247945987040886364269738647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165297324693924242846492431 247945987040886364269738647)
      ·
        refine ⟨371918980561329546404607971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247945987040886364269738647 371918980561329546404607971)
        ·
          refine ⟨557878470841994319606911957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371918980561329546404607971 557878470841994319606911957)
          ·
            refine ⟨13075276660359241865786999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 557878470841994319606911957 13075276660359241865786999)
            ·
              refine ⟨19612914990538862798680499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13075276660359241865786999 19612914990538862798680499)
              ·
                refine ⟨29419372485808294198020749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19612914990538862798680499 29419372485808294198020749)
                ·
                  refine ⟨11032264682178110324257781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29419372485808294198020749 11032264682178110324257781)
                  ·
                    refine ⟨1034274813954197842899167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11032264682178110324257781 1034274813954197842899167)
                    ·
                      rfl

theorem cell23_6042729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 1, 3, 5].length) (baseStart_6042729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042729 prefixEnd_6042729 := by exact prefixLift 6042729
  have htrace : WordTrace (prefixWord ++ tailWord_6042729) baseStart_6042729 baseEnd_6042729 := by
    simpa [prefixWord, tailWord_6042729, baseEnd_6042729] using wordTrace_append hprefix tailTrace_6042729
  have hstable : (prefixWord ++ tailWord_6042729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042729).length < 2 ^ (prefixWord ++ tailWord_6042729).sum := by decide
  have hdescent : baseEnd_6042729 < baseStart_6042729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042743 : List Nat := [1, 1, 3, 1, 1, 4, 2, 5, 1, 1, 3]
def baseStart_6042743 : Nat := 118140960795 + 6042743 * 2 ^ 59
def prefixEnd_6042743 : Nat := 4983230072969 + 3 ^ 40 * 6042743 * 2
def baseEnd_6042743 : Nat := 3102831630591756473922437

theorem tailTrace_6042743 : CollatzResearch.WordTrace tailWord_6042743 prefixEnd_6042743 3102831630591756473922437 := by
  unfold tailWord_6042743
  simp only [CollatzResearch.WordTrace]
  refine ⟨220396943547181604186332883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146931295698121069457555255 220396943547181604186332883)
  ·
    refine ⟨330595415320772406279499325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220396943547181604186332883 330595415320772406279499325)
    ·
      refine ⟨123973280745289652354812247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330595415320772406279499325 123973280745289652354812247)
      ·
        refine ⟨185959921117934478532218371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123973280745289652354812247 185959921117934478532218371)
        ·
          refine ⟨278939881676901717798327557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185959921117934478532218371 278939881676901717798327557)
          ·
            refine ⟨52301227814419072087186417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 278939881676901717798327557 52301227814419072087186417)
            ·
              refine ⟨39225920860814304065389813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52301227814419072087186417 39225920860814304065389813)
              ·
                refine ⟨3677430080701341006130295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 39225920860814304065389813 3677430080701341006130295)
                ·
                  refine ⟨5516145121052011509195443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3677430080701341006130295 5516145121052011509195443)
                  ·
                    refine ⟨8274217681578017263793165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5516145121052011509195443 8274217681578017263793165)
                    ·
                      refine ⟨3102831630591756473922437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8274217681578017263793165 3102831630591756473922437)
                      ·
                        rfl

theorem cell23_6042743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 5, 1, 1, 3].length) (baseStart_6042743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042743 prefixEnd_6042743 := by exact prefixLift 6042743
  have htrace : WordTrace (prefixWord ++ tailWord_6042743) baseStart_6042743 baseEnd_6042743 := by
    simpa [prefixWord, tailWord_6042743, baseEnd_6042743] using wordTrace_append hprefix tailTrace_6042743
  have hstable : (prefixWord ++ tailWord_6042743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042743).length < 2 ^ (prefixWord ++ tailWord_6042743).sum := by decide
  have hdescent : baseEnd_6042743 < baseStart_6042743 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042753 : List Nat := [1, 2, 4, 2, 2, 1, 2, 2, 2, 3, 2]
def baseStart_6042753 : Nat := 118140960795 + 6042753 * 2 ^ 59
def prefixEnd_6042753 : Nat := 4983230072969 + 3 ^ 40 * 6042753 * 2
def baseEnd_6042753 : Nat := 3102836765398301434797391

theorem tailTrace_6042753 : CollatzResearch.WordTrace tailWord_6042753 prefixEnd_6042753 3102836765398301434797391 := by
  unfold tailWord_6042753
  simp only [CollatzResearch.WordTrace]
  refine ⟨220397308277145375894196913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146931538851430250596131275 220397308277145375894196913)
  ·
    refine ⟨165297981207859031920647685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220397308277145375894196913 165297981207859031920647685)
    ·
      refine ⟨30993371476473568485121441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165297981207859031920647685 30993371476473568485121441)
      ·
        refine ⟨23245028607355176363841081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30993371476473568485121441 23245028607355176363841081)
        ·
          refine ⟨17433771455516382272880811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23245028607355176363841081 17433771455516382272880811)
          ·
            refine ⟨26150657183274573409321217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17433771455516382272880811 26150657183274573409321217)
            ·
              refine ⟨19612992887455930056990913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26150657183274573409321217 19612992887455930056990913)
              ·
                refine ⟨14709744665591947542743185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19612992887455930056990913 14709744665591947542743185)
                ·
                  refine ⟨11032308499193960657057389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14709744665591947542743185 11032308499193960657057389)
                  ·
                    refine ⟨4137115687197735246396521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11032308499193960657057389 4137115687197735246396521)
                    ·
                      refine ⟨3102836765398301434797391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137115687197735246396521 3102836765398301434797391)
                      ·
                        rfl

theorem cell23_6042753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 2, 2, 3, 2].length) (baseStart_6042753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042753 prefixEnd_6042753 := by exact prefixLift 6042753
  have htrace : WordTrace (prefixWord ++ tailWord_6042753) baseStart_6042753 baseEnd_6042753 := by
    simpa [prefixWord, tailWord_6042753, baseEnd_6042753] using wordTrace_append hprefix tailTrace_6042753
  have hstable : (prefixWord ++ tailWord_6042753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042753).length < 2 ^ (prefixWord ++ tailWord_6042753).sum := by decide
  have hdescent : baseEnd_6042753 < baseStart_6042753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042766 : List Nat := [4, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4]
def baseStart_6042766 : Nat := 118140960795 + 6042766 * 2 ^ 59
def prefixEnd_6042766 : Nat := 4983230072969 + 3 ^ 40 * 6042766 * 2
def baseEnd_6042766 : Nat := 3102843440646809883934831

theorem tailTrace_6042766 : CollatzResearch.WordTrace tailWord_6042766 prefixEnd_6042766 3102843440646809883934831 := by
  unfold tailWord_6042766
  simp only [CollatzResearch.WordTrace]
  refine ⟨27549722803262284889302519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146931854950732186076280101 27549722803262284889302519)
  ·
    refine ⟨41324584204893427333953779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27549722803262284889302519 41324584204893427333953779)
    ·
      refine ⟨61986876307340141000930669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41324584204893427333953779 61986876307340141000930669)
      ·
        refine ⟨23245078615252552875349001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61986876307340141000930669 23245078615252552875349001)
        ·
          refine ⟨17433808961439414656511751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23245078615252552875349001 17433808961439414656511751)
          ·
            refine ⟨26150713442159121984767627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17433808961439414656511751 26150713442159121984767627)
            ·
              refine ⟨39226070163238682977151441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26150713442159121984767627 39226070163238682977151441)
              ·
                refine ⟨29419552622429012232863581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39226070163238682977151441 29419552622429012232863581)
                ·
                  refine ⟨11032332233410879587323843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29419552622429012232863581 11032332233410879587323843)
                  ·
                    refine ⟨16548498350116319380985765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11032332233410879587323843 16548498350116319380985765)
                    ·
                      refine ⟨3102843440646809883934831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16548498350116319380985765 3102843440646809883934831)
                      ·
                        rfl

theorem cell23_6042766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_6042766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042766 prefixEnd_6042766 := by exact prefixLift 6042766
  have htrace : WordTrace (prefixWord ++ tailWord_6042766) baseStart_6042766 baseEnd_6042766 := by
    simpa [prefixWord, tailWord_6042766, baseEnd_6042766] using wordTrace_append hprefix tailTrace_6042766
  have hstable : (prefixWord ++ tailWord_6042766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042766).length < 2 ^ (prefixWord ++ tailWord_6042766).sum := by decide
  have hdescent : baseEnd_6042766 < baseStart_6042766 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042776 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 1, 6]
def baseStart_6042776 : Nat := 118140960795 + 6042776 * 2 ^ 59
def prefixEnd_6042776 : Nat := 4983230072969 + 3 ^ 40 * 6042776 * 2
def baseEnd_6042776 : Nat := 1034282858484451614936595

theorem tailTrace_6042776 : CollatzResearch.WordTrace tailWord_6042776 prefixEnd_6042776 1034282858484451614936595 := by
  unfold tailWord_6042776
  simp only [CollatzResearch.WordTrace]
  refine ⟨110199073578031025411142091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146932098104041367214856121 110199073578031025411142091)
  ·
    refine ⟨165298610367046538116713137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110199073578031025411142091 165298610367046538116713137)
    ·
      refine ⟨123973957775284903587534853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165298610367046538116713137 123973957775284903587534853)
      ·
        refine ⟨23245117082865919422662785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 123973957775284903587534853 23245117082865919422662785)
        ·
          refine ⟨17433837812149439566997089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23245117082865919422662785 17433837812149439566997089)
          ·
            refine ⟨13075378359112079675247817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17433837812149439566997089 13075378359112079675247817)
            ·
              refine ⟨9806533769334059756435863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13075378359112079675247817 9806533769334059756435863)
              ·
                refine ⟨14709800654001089634653795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9806533769334059756435863 14709800654001089634653795)
                ·
                  refine ⟨22064700981001634451980693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14709800654001089634653795 22064700981001634451980693)
                  ·
                    refine ⟨1034282858484451614936595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22064700981001634451980693 1034282858484451614936595)
                    ·
                      rfl

theorem cell23_6042776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 1, 6].length) (baseStart_6042776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042776 prefixEnd_6042776 := by exact prefixLift 6042776
  have htrace : WordTrace (prefixWord ++ tailWord_6042776) baseStart_6042776 baseEnd_6042776 := by
    simpa [prefixWord, tailWord_6042776, baseEnd_6042776] using wordTrace_append hprefix tailTrace_6042776
  have hstable : (prefixWord ++ tailWord_6042776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042776).length < 2 ^ (prefixWord ++ tailWord_6042776).sum := by decide
  have hdescent : baseEnd_6042776 < baseStart_6042776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042797 : List Nat := [1, 5, 2, 1, 4, 1, 2, 1, 1, 5]
def baseStart_6042797 : Nat := 118140960795 + 6042797 * 2 ^ 59
def prefixEnd_6042797 : Nat := 4983230072969 + 3 ^ 40 * 6042797 * 2
def baseEnd_6042797 : Nat := 1034286452849033087549063

theorem tailTrace_6042797 : CollatzResearch.WordTrace tailWord_6042797 prefixEnd_6042797 1034286452849033087549063 := by
  unfold tailWord_6042797
  simp only [CollatzResearch.WordTrace]
  refine ⟨220398913088985971408798645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146932608725990647605865763 220398913088985971408798645)
  ·
    refine ⟨20662398102092434819574873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220398913088985971408798645 20662398102092434819574873)
    ·
      refine ⟨15496798576569326114681155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20662398102092434819574873 15496798576569326114681155)
      ·
        refine ⟨23245197864853989172021733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15496798576569326114681155 23245197864853989172021733)
        ·
          refine ⟨4358474599660122969754075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23245197864853989172021733 4358474599660122969754075)
          ·
            refine ⟨6537711899490184454631113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4358474599660122969754075 6537711899490184454631113)
            ·
              refine ⟨4903283924617638340973335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6537711899490184454631113 4903283924617638340973335)
              ·
                refine ⟨7354925886926457511460003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903283924617638340973335 7354925886926457511460003)
                ·
                  refine ⟨11032388830389686267190005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7354925886926457511460003 11032388830389686267190005)
                  ·
                    refine ⟨1034286452849033087549063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11032388830389686267190005 1034286452849033087549063)
                    ·
                      rfl

theorem cell23_6042797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_6042797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042797 prefixEnd_6042797 := by exact prefixLift 6042797
  have htrace : WordTrace (prefixWord ++ tailWord_6042797) baseStart_6042797 baseEnd_6042797 := by
    simpa [prefixWord, tailWord_6042797, baseEnd_6042797] using wordTrace_append hprefix tailTrace_6042797
  have hstable : (prefixWord ++ tailWord_6042797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042797).length < 2 ^ (prefixWord ++ tailWord_6042797).sum := by decide
  have hdescent : baseEnd_6042797 < baseStart_6042797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042803 : List Nat := [1, 1, 1, 2, 3, 2, 6, 1, 1, 2, 3]
def baseStart_6042803 : Nat := 118140960795 + 6042803 * 2 ^ 59
def prefixEnd_6042803 : Nat := 4983230072969 + 3 ^ 40 * 6042803 * 2
def baseEnd_6042803 : Nat := 3102862439431026239172161

theorem tailTrace_6042803 : CollatzResearch.WordTrace tailWord_6042803 prefixEnd_6042803 3102862439431026239172161 := by
  unfold tailWord_6042803
  simp only [CollatzResearch.WordTrace]
  refine ⟨220399131926964234433517063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146932754617976156289011375 220399131926964234433517063)
  ·
    refine ⟨330598697890446351650275595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220399131926964234433517063 330598697890446351650275595)
    ·
      refine ⟨495898046835669527475413393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330598697890446351650275595 495898046835669527475413393)
      ·
        refine ⟨371923535126752145606560045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 495898046835669527475413393 371923535126752145606560045)
        ·
          refine ⟨139471325672532054602460017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371923535126752145606560045 139471325672532054602460017)
          ·
            refine ⟨104603494254399040951845013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139471325672532054602460017 104603494254399040951845013)
            ·
              refine ⟨4903288793174955044617735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 104603494254399040951845013 4903288793174955044617735)
              ·
                refine ⟨7354933189762432566926603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903288793174955044617735 7354933189762432566926603)
                ·
                  refine ⟨11032399784643648850389905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7354933189762432566926603 11032399784643648850389905)
                  ·
                    refine ⟨8274299838482736637792429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11032399784643648850389905 8274299838482736637792429)
                    ·
                      refine ⟨3102862439431026239172161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8274299838482736637792429 3102862439431026239172161)
                      ·
                        rfl

theorem cell23_6042803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 6, 1, 1, 2, 3].length) (baseStart_6042803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042803 prefixEnd_6042803 := by exact prefixLift 6042803
  have htrace : WordTrace (prefixWord ++ tailWord_6042803) baseStart_6042803 baseEnd_6042803 := by
    simpa [prefixWord, tailWord_6042803, baseEnd_6042803] using wordTrace_append hprefix tailTrace_6042803
  have hstable : (prefixWord ++ tailWord_6042803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042803).length < 2 ^ (prefixWord ++ tailWord_6042803).sum := by decide
  have hdescent : baseEnd_6042803 < baseStart_6042803 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042817 : List Nat := [1, 2, 6, 1, 1, 2, 2, 1, 3, 2, 2]
def baseStart_6042817 : Nat := 118140960795 + 6042817 * 2 ^ 59
def prefixEnd_6042817 : Nat := 4983230072969 + 3 ^ 40 * 6042817 * 2
def baseEnd_6042817 : Nat := 3102869628160189184397097

theorem tailTrace_6042817 : CollatzResearch.WordTrace tailWord_6042817 prefixEnd_6042817 3102869628160189184397097 := by
  unfold tailWord_6042817
  simp only [CollatzResearch.WordTrace]
  refine ⟨220399642548913514824526705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146933095032609009883017803 220399642548913514824526705)
  ·
    refine ⟨165299731911685136118395029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220399642548913514824526705 165299731911685136118395029)
    ·
      refine ⟨7748424933360240755549767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 165299731911685136118395029 7748424933360240755549767)
      ·
        refine ⟨11622637400040361133324651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7748424933360240755549767 11622637400040361133324651)
        ·
          refine ⟨17433956100060541699986977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11622637400040361133324651 17433956100060541699986977)
          ·
            refine ⟨13075467075045406274990233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17433956100060541699986977 13075467075045406274990233)
            ·
              refine ⟨9806600306284054706242675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13075467075045406274990233 9806600306284054706242675)
              ·
                refine ⟨14709900459426082059364013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9806600306284054706242675 14709900459426082059364013)
                ·
                  refine ⟨5516212672284780772261505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14709900459426082059364013 5516212672284780772261505)
                  ·
                    refine ⟨4137159504213585579196129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5516212672284780772261505 4137159504213585579196129)
                    ·
                      refine ⟨3102869628160189184397097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137159504213585579196129 3102869628160189184397097)
                      ·
                        rfl

theorem cell23_6042817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_6042817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042817 prefixEnd_6042817 := by exact prefixLift 6042817
  have htrace : WordTrace (prefixWord ++ tailWord_6042817) baseStart_6042817 baseEnd_6042817 := by
    simpa [prefixWord, tailWord_6042817, baseEnd_6042817] using wordTrace_append hprefix tailTrace_6042817
  have hstable : (prefixWord ++ tailWord_6042817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042817).length < 2 ^ (prefixWord ++ tailWord_6042817).sum := by decide
  have hdescent : baseEnd_6042817 < baseStart_6042817 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042830 : List Nat := [4, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4]
def baseStart_6042830 : Nat := 118140960795 + 6042830 * 2 ^ 59
def prefixEnd_6042830 : Nat := 4983230072969 + 3 ^ 40 * 6042830 * 2
def baseEnd_6042830 : Nat := 3102876303408697633534537

theorem tailTrace_6042830 : CollatzResearch.WordTrace tailWord_6042830 prefixEnd_6042830 3102876303408697633534537 := by
  unfold tailWord_6042830
  simp only [CollatzResearch.WordTrace]
  refine ⟨27550014587233302255593743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146933411131910945363166629 27550014587233302255593743)
  ·
    refine ⟨41325021880849953383390615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27550014587233302255593743 41325021880849953383390615)
    ·
      refine ⟨61987532821274930075085923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41325021880849953383390615 61987532821274930075085923)
      ·
        refine ⟨92981299231912395112628885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61987532821274930075085923 92981299231912395112628885)
        ·
          refine ⟨4358498401495893520904479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 92981299231912395112628885 4358498401495893520904479)
          ·
            refine ⟨6537747602243840281356719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4358498401495893520904479 6537747602243840281356719)
            ·
              refine ⟨9806621403365760422035079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6537747602243840281356719 9806621403365760422035079)
              ·
                refine ⟨14709932105048640633052619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9806621403365760422035079 14709932105048640633052619)
                ·
                  refine ⟨22064898157572960949578929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14709932105048640633052619 22064898157572960949578929)
                  ·
                    refine ⟨16548673618179720712184197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22064898157572960949578929 16548673618179720712184197)
                    ·
                      refine ⟨3102876303408697633534537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16548673618179720712184197 3102876303408697633534537)
                      ·
                        rfl

theorem cell23_6042830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 1, 1, 2, 4].length) (baseStart_6042830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042830 prefixEnd_6042830 := by exact prefixLift 6042830
  have htrace : WordTrace (prefixWord ++ tailWord_6042830) baseStart_6042830 baseEnd_6042830 := by
    simpa [prefixWord, tailWord_6042830, baseEnd_6042830] using wordTrace_append hprefix tailTrace_6042830
  have hstable : (prefixWord ++ tailWord_6042830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042830).length < 2 ^ (prefixWord ++ tailWord_6042830).sum := by decide
  have hdescent : baseEnd_6042830 < baseStart_6042830 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042839 : List Nat := [1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 4]
def baseStart_6042839 : Nat := 118140960795 + 6042839 * 2 ^ 59
def prefixEnd_6042839 : Nat := 4983230072969 + 3 ^ 40 * 6042839 * 2
def baseEnd_6042839 : Nat := 3102880924734588098321995

theorem tailTrace_6042839 : CollatzResearch.WordTrace tailWord_6042839 prefixEnd_6042839 3102880924734588098321995 := by
  unfold tailWord_6042839
  simp only [CollatzResearch.WordTrace]
  refine ⟨220400444954833812581827571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146933629969889208387885047 220400444954833812581827571)
  ·
    refine ⟨330600667432250718872741357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220400444954833812581827571 330600667432250718872741357)
    ·
      refine ⟨123975250287094019577278009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330600667432250718872741357 123975250287094019577278009)
      ·
        refine ⟨92981437715320514682958507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123975250287094019577278009 92981437715320514682958507)
        ·
          refine ⟨139472156572980772024437761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92981437715320514682958507 139472156572980772024437761)
          ·
            refine ⟨104604117429735579018328321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139472156572980772024437761 104604117429735579018328321)
            ·
              refine ⟨78453088072301684263746241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104604117429735579018328321 78453088072301684263746241)
              ·
                refine ⟨58839816054226263197809681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78453088072301684263746241 58839816054226263197809681)
                ·
                  refine ⟨44129862040669697398357261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58839816054226263197809681 44129862040669697398357261)
                  ·
                    refine ⟨16548698265251136524383973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44129862040669697398357261 16548698265251136524383973)
                    ·
                      refine ⟨3102880924734588098321995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16548698265251136524383973 3102880924734588098321995)
                      ·
                        rfl

theorem cell23_6042839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 3, 4].length) (baseStart_6042839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042839 prefixEnd_6042839 := by exact prefixLift 6042839
  have htrace : WordTrace (prefixWord ++ tailWord_6042839) baseStart_6042839 baseEnd_6042839 := by
    simpa [prefixWord, tailWord_6042839, baseEnd_6042839] using wordTrace_append hprefix tailTrace_6042839
  have hstable : (prefixWord ++ tailWord_6042839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042839).length < 2 ^ (prefixWord ++ tailWord_6042839).sum := by decide
  have hdescent : baseEnd_6042839 < baseStart_6042839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042859 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 5]
def baseStart_6042859 : Nat := 118140960795 + 6042859 * 2 ^ 59
def prefixEnd_6042859 : Nat := 4983230072969 + 3 ^ 40 * 6042859 * 2
def baseEnd_6042859 : Nat := 3102891194347678020071903

theorem tailTrace_6042859 : CollatzResearch.WordTrace tailWord_6042859 prefixEnd_6042859 3102891194347678020071903 := by
  unfold tailWord_6042859
  simp only [CollatzResearch.WordTrace]
  refine ⟨220401174414761355997555631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146934116276507570665037087 220401174414761355997555631)
  ·
    refine ⟨330601761622142033996333447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220401174414761355997555631 330601761622142033996333447)
    ·
      refine ⟨495902642433213050994500171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330601761622142033996333447 495902642433213050994500171)
      ·
        refine ⟨743853963649819576491750257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495902642433213050994500171 743853963649819576491750257)
        ·
          refine ⟨557890472737364682368812693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 743853963649819576491750257 557890472737364682368812693)
          ·
            refine ⟨26151115909563969486038095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 557890472737364682368812693 26151115909563969486038095)
            ·
              refine ⟨39226673864345954229057143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26151115909563969486038095 39226673864345954229057143)
              ·
                refine ⟨58840010796518931343585715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39226673864345954229057143 58840010796518931343585715)
                ·
                  refine ⟨88260016194778397015378573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58840010796518931343585715 88260016194778397015378573)
                  ·
                    refine ⟨33097506073041898880766965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88260016194778397015378573 33097506073041898880766965)
                    ·
                      refine ⟨3102891194347678020071903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33097506073041898880766965 3102891194347678020071903)
                      ·
                        rfl

theorem cell23_6042859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 3, 5].length) (baseStart_6042859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042859 prefixEnd_6042859 := by exact prefixLift 6042859
  have htrace : WordTrace (prefixWord ++ tailWord_6042859) baseStart_6042859 baseEnd_6042859 := by
    simpa [prefixWord, tailWord_6042859, baseEnd_6042859] using wordTrace_append hprefix tailTrace_6042859
  have hstable : (prefixWord ++ tailWord_6042859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042859).length < 2 ^ (prefixWord ++ tailWord_6042859).sum := by decide
  have hdescent : baseEnd_6042859 < baseStart_6042859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042868 : List Nat := [2, 6, 1, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_6042868 : Nat := 118140960795 + 6042868 * 2 ^ 59
def prefixEnd_6042868 : Nat := 4983230072969 + 3 ^ 40 * 6042868 * 2
def baseEnd_6042868 : Nat := 3102895815673568484859363

theorem tailTrace_6042868 : CollatzResearch.WordTrace tailWord_6042868 prefixEnd_6042868 3102895815673568484859363 := by
  unfold tailWord_6042868
  simp only [CollatzResearch.WordTrace]
  refine ⟨110200751335864375267316629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146934335114485833689755505 110200751335864375267316629)
  ·
    refine ⟨5165660218868642590655467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 110200751335864375267316629 5165660218868642590655467)
    ·
      refine ⟨7748490328302963885983201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5165660218868642590655467 7748490328302963885983201)
      ·
        refine ⟨5811367746227222914487401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7748490328302963885983201 5811367746227222914487401)
        ·
          refine ⟨4358525809670417185865551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5811367746227222914487401 4358525809670417185865551)
          ·
            refine ⟨6537788714505625778798327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4358525809670417185865551 6537788714505625778798327)
            ·
              refine ⟨9806683071758438668197491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6537788714505625778798327 9806683071758438668197491)
              ·
                refine ⟨14710024607637658002296237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9806683071758438668197491 14710024607637658002296237)
                ·
                  refine ⟨5516259227864121750861089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14710024607637658002296237 5516259227864121750861089)
                  ·
                    refine ⟨4137194420898091313145817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5516259227864121750861089 4137194420898091313145817)
                    ·
                      refine ⟨3102895815673568484859363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137194420898091313145817 3102895815673568484859363)
                      ·
                        rfl

theorem cell23_6042868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_6042868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042868 prefixEnd_6042868 := by exact prefixLift 6042868
  have htrace : WordTrace (prefixWord ++ tailWord_6042868) baseStart_6042868 baseEnd_6042868 := by
    simpa [prefixWord, tailWord_6042868, baseEnd_6042868] using wordTrace_append hprefix tailTrace_6042868
  have hstable : (prefixWord ++ tailWord_6042868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042868).length < 2 ^ (prefixWord ++ tailWord_6042868).sum := by decide
  have hdescent : baseEnd_6042868 < baseStart_6042868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042873 : List Nat := [1, 2, 1, 3, 1, 1, 3, 3, 4, 2, 2]
def baseStart_6042873 : Nat := 118140960795 + 6042873 * 2 ^ 59
def prefixEnd_6042873 : Nat := 4983230072969 + 3 ^ 40 * 6042873 * 2
def baseEnd_6042873 : Nat := 3102898383076840965296839

theorem tailTrace_6042873 : CollatzResearch.WordTrace tailWord_6042873 prefixEnd_6042873 3102898383076840965296839 := by
  unfold tailWord_6042873
  simp only [CollatzResearch.WordTrace]
  refine ⟨220401685036710636388565273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146934456691140424259043515 220401685036710636388565273)
  ·
    refine ⟨165301263777532977291423955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220401685036710636388565273 165301263777532977291423955)
    ·
      refine ⟨247951895666299465937135933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165301263777532977291423955 247951895666299465937135933)
      ·
        refine ⟨92981960874862299726425975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247951895666299465937135933 92981960874862299726425975)
        ·
          refine ⟨139472941312293449589638963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92981960874862299726425975 139472941312293449589638963)
          ·
            refine ⟨209209411968440174384458445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139472941312293449589638963 209209411968440174384458445)
            ·
              refine ⟨78453529488165065394171917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209209411968440174384458445 78453529488165065394171917)
              ·
                refine ⟨29420073558061899522814469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78453529488165065394171917 29420073558061899522814469)
                ·
                  refine ⟨5516263792136606160527713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29420073558061899522814469 5516263792136606160527713)
                  ·
                    refine ⟨4137197844102454620395785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5516263792136606160527713 4137197844102454620395785)
                    ·
                      refine ⟨3102898383076840965296839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137197844102454620395785 3102898383076840965296839)
                      ·
                        rfl

theorem cell23_6042873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 3, 4, 2, 2].length) (baseStart_6042873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042873 prefixEnd_6042873 := by exact prefixLift 6042873
  have htrace : WordTrace (prefixWord ++ tailWord_6042873) baseStart_6042873 baseEnd_6042873 := by
    simpa [prefixWord, tailWord_6042873, baseEnd_6042873] using wordTrace_append hprefix tailTrace_6042873
  have hstable : (prefixWord ++ tailWord_6042873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042873).length < 2 ^ (prefixWord ++ tailWord_6042873).sum := by decide
  have hdescent : baseEnd_6042873 < baseStart_6042873 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042930 : List Nat := [3, 2, 1, 1, 4, 1, 4, 2, 5]
def baseStart_6042930 : Nat := 118140960795 + 6042930 * 2 ^ 59
def prefixEnd_6042930 : Nat := 4983230072969 + 3 ^ 40 * 6042930 * 2
def baseEnd_6042930 : Nat := 344769739052683026920453

theorem tailTrace_6042930 : CollatzResearch.WordTrace tailWord_6042930 prefixEnd_6042930 344769739052683026920453 := by
  unfold tailWord_6042930
  simp only [CollatzResearch.WordTrace]
  refine ⟨55100940999376033780847561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146935842665002756748926829 55100940999376033780847561)
  ·
    refine ⟨41325705749532025335635671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55100940999376033780847561 41325705749532025335635671)
    ·
      refine ⟨61988558624298038003453507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41325705749532025335635671 61988558624298038003453507)
      ·
        refine ⟨92982837936447057005180261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61988558624298038003453507 92982837936447057005180261)
        ·
          refine ⟨17434282113083823188471299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92982837936447057005180261 17434282113083823188471299)
          ·
            refine ⟨26151423169625734782706949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17434282113083823188471299 26151423169625734782706949)
            ·
              refine ⟨4903391844304825271757553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 26151423169625734782706949 4903391844304825271757553)
              ·
                refine ⟨3677543883228618953818165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4903391844304825271757553 3677543883228618953818165)
                ·
                  refine ⟨344769739052683026920453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3677543883228618953818165 344769739052683026920453)
                  ·
                    rfl

theorem cell23_6042930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_6042930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042930 prefixEnd_6042930 := by exact prefixLift 6042930
  have htrace : WordTrace (prefixWord ++ tailWord_6042930) baseStart_6042930 baseEnd_6042930 := by
    simpa [prefixWord, tailWord_6042930, baseEnd_6042930] using wordTrace_append hprefix tailTrace_6042930
  have hstable : (prefixWord ++ tailWord_6042930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042930).length < 2 ^ (prefixWord ++ tailWord_6042930).sum := by decide
  have hdescent : baseEnd_6042930 < baseStart_6042930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042933 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 2, 5, 2]
def baseStart_6042933 : Nat := 118140960795 + 6042933 * 2 ^ 59
def prefixEnd_6042933 : Nat := 4983230072969 + 3 ^ 40 * 6042933 * 2
def baseEnd_6042933 : Nat := 3102929191916110730546563

theorem tailTrace_6042933 : CollatzResearch.WordTrace tailWord_6042933 prefixEnd_6042933 3102929191916110730546563 := by
  unfold tailWord_6042933
  simp only [CollatzResearch.WordTrace]
  refine ⟨220403873416493266635749453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146935915610995511090499635 220403873416493266635749453)
  ·
    refine ⟨82651452531184974988406045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220403873416493266635749453 82651452531184974988406045)
    ·
      refine ⟨30994294699194365620652267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 82651452531184974988406045 30994294699194365620652267)
      ·
        refine ⟨46491442048791548430978401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30994294699194365620652267 46491442048791548430978401)
        ·
          refine ⟨34868581536593661323233801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46491442048791548430978401 34868581536593661323233801)
          ·
            refine ⟨26151436152445245992425351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34868581536593661323233801 26151436152445245992425351)
            ·
              refine ⟨39227154228667868988638027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26151436152445245992425351 39227154228667868988638027)
              ·
                refine ⟨58840731343001803482957041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39227154228667868988638027 58840731343001803482957041)
                ·
                  refine ⟨44130548507251352612217781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58840731343001803482957041 44130548507251352612217781)
                  ·
                    refine ⟨4137238922554814307395417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44130548507251352612217781 4137238922554814307395417)
                    ·
                      refine ⟨3102929191916110730546563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137238922554814307395417 3102929191916110730546563)
                      ·
                        rfl

theorem cell23_6042933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 2, 5, 2].length) (baseStart_6042933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042933 prefixEnd_6042933 := by exact prefixLift 6042933
  have htrace : WordTrace (prefixWord ++ tailWord_6042933) baseStart_6042933 baseEnd_6042933 := by
    simpa [prefixWord, tailWord_6042933, baseEnd_6042933] using wordTrace_append hprefix tailTrace_6042933
  have hstable : (prefixWord ++ tailWord_6042933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042933).length < 2 ^ (prefixWord ++ tailWord_6042933).sum := by decide
  have hdescent : baseEnd_6042933 < baseStart_6042933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6042976 : List Nat := [2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 6]
def baseStart_6042976 : Nat := 118140960795 + 6042976 * 2 ^ 59
def prefixEnd_6042976 : Nat := 4983230072969 + 3 ^ 40 * 6042976 * 2
def baseEnd_6042976 : Nat := 3102951271584254062308865

theorem tailTrace_6042976 : CollatzResearch.WordTrace tailWord_6042976 prefixEnd_6042976 3102951271584254062308865 := by
  unfold tailWord_6042976
  simp only [CollatzResearch.WordTrace]
  refine ⟨110202720877668742489782391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146936961170224989986376521 110202720877668742489782391)
  ·
    refine ⟨165304081316503113734673587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110202720877668742489782391 165304081316503113734673587)
    ·
      refine ⟨247956121974754670602010381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165304081316503113734673587 247956121974754670602010381)
      ·
        refine ⟨92983545740533001475753893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247956121974754670602010381 92983545740533001475753893)
        ·
          refine ⟨17434414826349937776703855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92983545740533001475753893 17434414826349937776703855)
          ·
            refine ⟨26151622239524906665055783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17434414826349937776703855 26151622239524906665055783)
            ·
              refine ⟨39227433359287359997583675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26151622239524906665055783 39227433359287359997583675)
              ·
                refine ⟨58841150038931039996375513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39227433359287359997583675 58841150038931039996375513)
                ·
                  refine ⟨44130862529198279997281635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58841150038931039996375513 44130862529198279997281635)
                  ·
                    refine ⟨66196293793797419995922453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44130862529198279997281635 66196293793797419995922453)
                    ·
                      refine ⟨3102951271584254062308865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66196293793797419995922453 3102951271584254062308865)
                      ·
                        rfl

theorem cell23_6042976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_6042976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6042976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6042976 prefixEnd_6042976 := by exact prefixLift 6042976
  have htrace : WordTrace (prefixWord ++ tailWord_6042976) baseStart_6042976 baseEnd_6042976 := by
    simpa [prefixWord, tailWord_6042976, baseEnd_6042976] using wordTrace_append hprefix tailTrace_6042976
  have hstable : (prefixWord ++ tailWord_6042976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6042976).length < 2 ^ (prefixWord ++ tailWord_6042976).sum := by decide
  have hdescent : baseEnd_6042976 < baseStart_6042976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6042976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043003 : List Nat := [1, 1, 1, 1, 1, 6, 5, 1, 6]
def baseStart_6043003 : Nat := 118140960795 + 6043003 * 2 ^ 59
def prefixEnd_6043003 : Nat := 4983230072969 + 3 ^ 40 * 6043003 * 2
def baseEnd_6043003 : Nat := 344773903951325050741249

theorem tailTrace_6043003 : CollatzResearch.WordTrace tailWord_6043003 prefixEnd_6043003 344773903951325050741249 := by
  unfold tailWord_6043003
  simp only [CollatzResearch.WordTrace]
  refine ⟨220406426526239668590797663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146937617684159779060531775 220406426526239668590797663)
  ·
    refine ⟨330609639789359502886196495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220406426526239668590797663 330609639789359502886196495)
    ·
      refine ⟨495914459684039254329294743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330609639789359502886196495 495914459684039254329294743)
      ·
        refine ⟨743871689526058881493942115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495914459684039254329294743 743871689526058881493942115)
        ·
          refine ⟨1115807534289088322240913173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 743871689526058881493942115 1115807534289088322240913173)
          ·
            refine ⟨52303478169801015105042805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1115807534289088322240913173 52303478169801015105042805)
            ·
              refine ⟨4903451078418845166097763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52303478169801015105042805 4903451078418845166097763)
              ·
                refine ⟨7355176617628267749146645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903451078418845166097763 7355176617628267749146645)
                ·
                  refine ⟨344773903951325050741249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7355176617628267749146645 344773903951325050741249)
                  ·
                    rfl

theorem cell23_6043003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 5, 1, 6].length) (baseStart_6043003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043003 prefixEnd_6043003 := by exact prefixLift 6043003
  have htrace : WordTrace (prefixWord ++ tailWord_6043003) baseStart_6043003 baseEnd_6043003 := by
    simpa [prefixWord, tailWord_6043003, baseEnd_6043003] using wordTrace_append hprefix tailTrace_6043003
  have hstable : (prefixWord ++ tailWord_6043003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043003).length < 2 ^ (prefixWord ++ tailWord_6043003).sum := by decide
  have hdescent : baseEnd_6043003 < baseStart_6043003 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043033 : List Nat := [1, 2, 1, 2, 1, 5, 2, 3, 1, 5]
def baseStart_6043033 : Nat := 118140960795 + 6043033 * 2 ^ 59
def prefixEnd_6043033 : Nat := 4983230072969 + 3 ^ 40 * 6043033 * 2
def baseEnd_6043033 : Nat := 1034326846660520113098701

theorem tailTrace_6043033 : CollatzResearch.WordTrace tailWord_6043033 prefixEnd_6043033 1034326846660520113098701 := by
  unfold tailWord_6043033
  simp only [CollatzResearch.WordTrace]
  refine ⟨220407520716130983714389753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146938347144087322476259835 220407520716130983714389753)
  ·
    refine ⟨165305640537098237785792315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220407520716130983714389753 165305640537098237785792315)
    ·
      refine ⟨247958460805647356678688473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165305640537098237785792315 247958460805647356678688473)
      ·
        refine ⟨185968845604235517509016355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247958460805647356678688473 185968845604235517509016355)
        ·
          refine ⟨278953268406353276263524533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185968845604235517509016355 278953268406353276263524533)
          ·
            refine ⟨26151868913095619649705425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 278953268406353276263524533 26151868913095619649705425)
            ·
              refine ⟨19613901684821714737279069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26151868913095619649705425 19613901684821714737279069)
              ·
                refine ⟨7355213131808143026479651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19613901684821714737279069 7355213131808143026479651)
                ·
                  refine ⟨11032819697712214539719477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7355213131808143026479651 11032819697712214539719477)
                  ·
                    refine ⟨1034326846660520113098701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11032819697712214539719477 1034326846660520113098701)
                    ·
                      rfl

theorem cell23_6043033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 3, 1, 5].length) (baseStart_6043033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043033 prefixEnd_6043033 := by exact prefixLift 6043033
  have htrace : WordTrace (prefixWord ++ tailWord_6043033) baseStart_6043033 baseEnd_6043033 := by
    simpa [prefixWord, tailWord_6043033, baseEnd_6043033] using wordTrace_append hprefix tailTrace_6043033
  have hstable : (prefixWord ++ tailWord_6043033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043033).length < 2 ^ (prefixWord ++ tailWord_6043033).sum := by decide
  have hdescent : baseEnd_6043033 < baseStart_6043033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043040 : List Nat := [2, 1, 1, 4, 1, 2, 3, 2, 2, 3, 2]
def baseStart_6043040 : Nat := 118140960795 + 6043040 * 2 ^ 59
def prefixEnd_6043040 : Nat := 4983230072969 + 3 ^ 40 * 6043040 * 2
def baseEnd_6043040 : Nat := 3102984134346141811908571

theorem tailTrace_6043040 : CollatzResearch.WordTrace tailWord_6043040 prefixEnd_6043040 3102984134346141811908571 := by
  unfold tailWord_6043040
  simp only [CollatzResearch.WordTrace]
  refine ⟨110203888013552811954947287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146938517351403749273263049 110203888013552811954947287)
  ·
    refine ⟨165305832020329217932420931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110203888013552811954947287 165305832020329217932420931)
    ·
      refine ⟨247958748030493826898631397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165305832020329217932420931 247958748030493826898631397)
      ·
        refine ⟨46492265255717592543493387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247958748030493826898631397 46492265255717592543493387)
        ·
          refine ⟨69738397883576388815240081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46492265255717592543493387 69738397883576388815240081)
          ·
            refine ⟨52303798412682291611430061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69738397883576388815240081 52303798412682291611430061)
            ·
              refine ⟨19613924404755859354286273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 52303798412682291611430061 19613924404755859354286273)
              ·
                refine ⟨14710443303566894515714705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19613924404755859354286273 14710443303566894515714705)
                ·
                  refine ⟨11032832477675170886786029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14710443303566894515714705 11032832477675170886786029)
                  ·
                    refine ⟨4137312179128189082544761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11032832477675170886786029 4137312179128189082544761)
                    ·
                      refine ⟨3102984134346141811908571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137312179128189082544761 3102984134346141811908571)
                      ·
                        rfl

theorem cell23_6043040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_6043040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043040 prefixEnd_6043040 := by exact prefixLift 6043040
  have htrace : WordTrace (prefixWord ++ tailWord_6043040) baseStart_6043040 baseEnd_6043040 := by
    simpa [prefixWord, tailWord_6043040, baseEnd_6043040] using wordTrace_append hprefix tailTrace_6043040
  have hstable : (prefixWord ++ tailWord_6043040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043040).length < 2 ^ (prefixWord ++ tailWord_6043040).sum := by decide
  have hdescent : baseEnd_6043040 < baseStart_6043040 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043056 : List Nat := [2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 5]
def baseStart_6043056 : Nat := 118140960795 + 6043056 * 2 ^ 59
def prefixEnd_6043056 : Nat := 4983230072969 + 3 ^ 40 * 6043056 * 2
def baseEnd_6043056 : Nat := 3102992350036613749308497

theorem tailTrace_6043056 : CollatzResearch.WordTrace tailWord_6043056 prefixEnd_6043056 3102992350036613749308497 := by
  unfold tailWord_6043056
  simp only [CollatzResearch.WordTrace]
  refine ⟨110204179797523829321238511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146938906396698439094984681 110204179797523829321238511)
  ·
    refine ⟨165306269696285743981857767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110204179797523829321238511 165306269696285743981857767)
    ·
      refine ⟨247959404544428615972786651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165306269696285743981857767 247959404544428615972786651)
      ·
        refine ⟨371939106816642923959179977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247959404544428615972786651 371939106816642923959179977)
        ·
          refine ⟨278954330112482192969384983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 371939106816642923959179977 278954330112482192969384983)
          ·
            refine ⟨418431495168723289454077475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278954330112482192969384983 418431495168723289454077475)
            ·
              refine ⟨627647242753084934181116213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418431495168723289454077475 627647242753084934181116213)
              ·
                refine ⟨58841929008101712579479645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 627647242753084934181116213 58841929008101712579479645)
                ·
                  refine ⟨22065723378038142217304867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58841929008101712579479645 22065723378038142217304867)
                  ·
                    refine ⟨33098585067057213325957301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22065723378038142217304867 33098585067057213325957301)
                    ·
                      refine ⟨3102992350036613749308497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33098585067057213325957301 3102992350036613749308497)
                      ·
                        rfl

theorem cell23_6043056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_6043056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043056 prefixEnd_6043056 := by exact prefixLift 6043056
  have htrace : WordTrace (prefixWord ++ tailWord_6043056) baseStart_6043056 baseEnd_6043056 := by
    simpa [prefixWord, tailWord_6043056, baseEnd_6043056] using wordTrace_append hprefix tailTrace_6043056
  have hstable : (prefixWord ++ tailWord_6043056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043056).length < 2 ^ (prefixWord ++ tailWord_6043056).sum := by decide
  have hdescent : baseEnd_6043056 < baseStart_6043056 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043103 : List Nat := [1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 3]
def baseStart_6043103 : Nat := 118140960795 + 6043103 * 2 ^ 59
def prefixEnd_6043103 : Nat := 4983230072969 + 3 ^ 40 * 6043103 * 2
def baseEnd_6043103 : Nat := 3103016483627375065420781

theorem tailTrace_6043103 : CollatzResearch.WordTrace tailWord_6043103 prefixEnd_6043103 3103016483627375065420781 := by
  unfold tailWord_6043103
  simp only [CollatzResearch.WordTrace]
  refine ⟨220410073825877385669437963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146940049217251590446291975 220410073825877385669437963)
  ·
    refine ⟨330615110738816078504156945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220410073825877385669437963 330615110738816078504156945)
    ·
      refine ⟨247961333054112058878117709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330615110738816078504156945 247961333054112058878117709)
      ·
        refine ⟨92985499895292022079294141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247961333054112058878117709 92985499895292022079294141)
        ·
          refine ⟨34869562460734508279735303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 92985499895292022079294141 34869562460734508279735303)
          ·
            refine ⟨52304343691101762419602955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34869562460734508279735303 52304343691101762419602955)
            ·
              refine ⟨78456515536652643629404433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52304343691101762419602955 78456515536652643629404433)
              ·
                refine ⟨58842386652489482722053325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78456515536652643629404433 58842386652489482722053325)
                ·
                  refine ⟨22065894994683556020769997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58842386652489482722053325 22065894994683556020769997)
                  ·
                    refine ⟨8274710623006333507788749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22065894994683556020769997 8274710623006333507788749)
                    ·
                      refine ⟨3103016483627375065420781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8274710623006333507788749 3103016483627375065420781)
                      ·
                        rfl

theorem cell23_6043103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_6043103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043103 prefixEnd_6043103 := by exact prefixLift 6043103
  have htrace : WordTrace (prefixWord ++ tailWord_6043103) baseStart_6043103 baseEnd_6043103 := by
    simpa [prefixWord, tailWord_6043103, baseEnd_6043103] using wordTrace_append hprefix tailTrace_6043103
  have hstable : (prefixWord ++ tailWord_6043103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043103).length < 2 ^ (prefixWord ++ tailWord_6043103).sum := by decide
  have hdescent : baseEnd_6043103 < baseStart_6043103 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043117 : List Nat := [1, 5, 1, 3, 2, 1, 2, 1, 1, 2, 4]
def baseStart_6043117 : Nat := 118140960795 + 6043117 * 2 ^ 59
def prefixEnd_6043117 : Nat := 4983230072969 + 3 ^ 40 * 6043117 * 2
def baseEnd_6043117 : Nat := 3103023672356538010645717

theorem tailTrace_6043117 : CollatzResearch.WordTrace tailWord_6043117 prefixEnd_6043117 3103023672356538010645717 := by
  unfold tailWord_6043117
  simp only [CollatzResearch.WordTrace]
  refine ⟨220410584447826666060447605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146940389631884444040298403 220410584447826666060447605)
  ·
    refine ⟨20663492291983749943166963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220410584447826666060447605 20663492291983749943166963)
    ·
      refine ⟨30995238437975624914750445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20663492291983749943166963 30995238437975624914750445)
      ·
        refine ⟨11623214414240859343031417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30995238437975624914750445 11623214414240859343031417)
        ·
          refine ⟨8717410810680644507273563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11623214414240859343031417 8717410810680644507273563)
          ·
            refine ⟨13076116216020966760910345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8717410810680644507273563 13076116216020966760910345)
            ·
              refine ⟨9807087162015725070682759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13076116216020966760910345 9807087162015725070682759)
              ·
                refine ⟨14710630743023587606024139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9807087162015725070682759 14710630743023587606024139)
                ·
                  refine ⟨22065946114535381409036209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14710630743023587606024139 22065946114535381409036209)
                  ·
                    refine ⟨16549459585901536056777157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22065946114535381409036209 16549459585901536056777157)
                    ·
                      refine ⟨3103023672356538010645717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16549459585901536056777157 3103023672356538010645717)
                      ·
                        rfl

theorem cell23_6043117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_6043117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043117 prefixEnd_6043117 := by exact prefixLift 6043117
  have htrace : WordTrace (prefixWord ++ tailWord_6043117) baseStart_6043117 baseEnd_6043117 := by
    simpa [prefixWord, tailWord_6043117, baseEnd_6043117] using wordTrace_append hprefix tailTrace_6043117
  have hstable : (prefixWord ++ tailWord_6043117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043117).length < 2 ^ (prefixWord ++ tailWord_6043117).sum := by decide
  have hdescent : baseEnd_6043117 < baseStart_6043117 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043120 : List Nat := [2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 3]
def baseStart_6043120 : Nat := 118140960795 + 6043120 * 2 ^ 59
def prefixEnd_6043120 : Nat := 4983230072969 + 3 ^ 40 * 6043120 * 2
def baseEnd_6043120 : Nat := 3103025212798501498908203

theorem tailTrace_6043120 : CollatzResearch.WordTrace tailWord_6043120 prefixEnd_6043120 3103025212798501498908203 := by
  unfold tailWord_6043120
  simp only [CollatzResearch.WordTrace]
  refine ⟨110205346933407898786403407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146940462577877198381871209 110205346933407898786403407)
  ·
    refine ⟨165308020400111848179605111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110205346933407898786403407 165308020400111848179605111)
    ·
      refine ⟨247962030600167772269407667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165308020400111848179605111 247962030600167772269407667)
      ·
        refine ⟨371943045900251658404111501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247962030600167772269407667 371943045900251658404111501)
        ·
          refine ⟨139478642212594371901541813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371943045900251658404111501 139478642212594371901541813)
          ·
            refine ⟨13076122707430722365769545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 139478642212594371901541813 13076122707430722365769545)
            ·
              refine ⟨9807092030573041774327159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13076122707430722365769545 9807092030573041774327159)
              ·
                refine ⟨14710638045859562661490739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9807092030573041774327159 14710638045859562661490739)
                ·
                  refine ⟨22065957068789343992236109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14710638045859562661490739 22065957068789343992236109)
                  ·
                    refine ⟨8274733900796003997088541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22065957068789343992236109 8274733900796003997088541)
                    ·
                      refine ⟨3103025212798501498908203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8274733900796003997088541 3103025212798501498908203)
                      ·
                        rfl

theorem cell23_6043120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 3].length) (baseStart_6043120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043120 prefixEnd_6043120 := by exact prefixLift 6043120
  have htrace : WordTrace (prefixWord ++ tailWord_6043120) baseStart_6043120 baseEnd_6043120 := by
    simpa [prefixWord, tailWord_6043120, baseEnd_6043120] using wordTrace_append hprefix tailTrace_6043120
  have hstable : (prefixWord ++ tailWord_6043120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043120).length < 2 ^ (prefixWord ++ tailWord_6043120).sum := by decide
  have hdescent : baseEnd_6043120 < baseStart_6043120 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043130 : List Nat := [3, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2]
def baseStart_6043130 : Nat := 118140960795 + 6043130 * 2 ^ 59
def prefixEnd_6043130 : Nat := 4983230072969 + 3 ^ 40 * 6043130 * 2
def baseEnd_6043130 : Nat := 3103030347605046459783157

theorem tailTrace_6043130 : CollatzResearch.WordTrace tailWord_6043130 prefixEnd_6043130 3103030347605046459783157 := by
  unfold tailWord_6043130
  simp only [CollatzResearch.WordTrace]
  refine ⟨55102764649194892320167711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146940705731186379520447229 55102764649194892320167711)
  ·
    refine ⟨82654146973792338480251567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55102764649194892320167711 82654146973792338480251567)
    ·
      refine ⟨123981220460688507720377351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82654146973792338480251567 123981220460688507720377351)
      ·
        refine ⟨185971830691032761580566027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123981220460688507720377351 185971830691032761580566027)
        ·
          refine ⟨278957746036549142370849041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185971830691032761580566027 278957746036549142370849041)
          ·
            refine ⟨209218309527411856778136781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 278957746036549142370849041 209218309527411856778136781)
            ·
              refine ⟨78456866072779446291801293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 209218309527411856778136781 78456866072779446291801293)
              ·
                refine ⟨29421324777292292359425485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78456866072779446291801293 29421324777292292359425485)
                ·
                  refine ⟨11032996791484609634784557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29421324777292292359425485 11032996791484609634784557)
                  ·
                    refine ⟨4137373796806728613044209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11032996791484609634784557 4137373796806728613044209)
                    ·
                      refine ⟨3103030347605046459783157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137373796806728613044209 3103030347605046459783157)
                      ·
                        rfl

theorem cell23_6043130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3, 3, 3, 2].length) (baseStart_6043130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043130 prefixEnd_6043130 := by exact prefixLift 6043130
  have htrace : WordTrace (prefixWord ++ tailWord_6043130) baseStart_6043130 baseEnd_6043130 := by
    simpa [prefixWord, tailWord_6043130, baseEnd_6043130] using wordTrace_append hprefix tailTrace_6043130
  have hstable : (prefixWord ++ tailWord_6043130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043130).length < 2 ^ (prefixWord ++ tailWord_6043130).sum := by decide
  have hdescent : baseEnd_6043130 < baseStart_6043130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043138 : List Nat := [3, 4, 1, 2, 1, 2, 2, 3, 1, 2, 2]
def baseStart_6043138 : Nat := 118140960795 + 6043138 * 2 ^ 59
def prefixEnd_6043138 : Nat := 4983230072969 + 3 ^ 40 * 6043138 * 2
def baseEnd_6043138 : Nat := 3103034455450282428483121

theorem tailTrace_6043138 : CollatzResearch.WordTrace tailWord_6043138 prefixEnd_6043138 3103034455450282428483121 := by
  unfold tailWord_6043138
  simp only [CollatzResearch.WordTrace]
  refine ⟨55102837595187646661740517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146940900253833724431308045 55102837595187646661740517)
  ·
    refine ⟨10331782049097683749076347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55102837595187646661740517 10331782049097683749076347)
    ·
      refine ⟨15497673073646525623614521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10331782049097683749076347 15497673073646525623614521)
      ·
        refine ⟨11623254805234894217710891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15497673073646525623614521 11623254805234894217710891)
        ·
          refine ⟨17434882207852341326566337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11623254805234894217710891 17434882207852341326566337)
          ·
            refine ⟨13076161655889255994924753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17434882207852341326566337 13076161655889255994924753)
            ·
              refine ⟨9807121241916941996193565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13076161655889255994924753 9807121241916941996193565)
              ·
                refine ⟨3677670465718853248572587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9807121241916941996193565 3677670465718853248572587)
                ·
                  refine ⟨5516505698578279872858881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3677670465718853248572587 5516505698578279872858881)
                  ·
                    refine ⟨4137379273933709904644161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5516505698578279872858881 4137379273933709904644161)
                    ·
                      refine ⟨3103034455450282428483121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137379273933709904644161 3103034455450282428483121)
                      ·
                        rfl

theorem cell23_6043138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_6043138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043138 prefixEnd_6043138 := by exact prefixLift 6043138
  have htrace : WordTrace (prefixWord ++ tailWord_6043138) baseStart_6043138 baseEnd_6043138 := by
    simpa [prefixWord, tailWord_6043138, baseEnd_6043138] using wordTrace_append hprefix tailTrace_6043138
  have hstable : (prefixWord ++ tailWord_6043138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043138).length < 2 ^ (prefixWord ++ tailWord_6043138).sum := by decide
  have hdescent : baseEnd_6043138 < baseStart_6043138 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043217 : List Nat := [1, 2, 2, 1, 3, 2, 5, 2, 5]
def baseStart_6043217 : Nat := 118140960795 + 6043217 * 2 ^ 59
def prefixEnd_6043217 : Nat := 4983230072969 + 3 ^ 40 * 6043217 * 2
def baseEnd_6043217 : Nat := 344786113380220846599473

theorem tailTrace_6043217 : CollatzResearch.WordTrace tailWord_6043217 prefixEnd_6043217 344786113380220846599473 := by
  unfold tailWord_6043217
  simp only [CollatzResearch.WordTrace]
  refine ⟨220414231747464383139087905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146942821164976255426058603 220414231747464383139087905)
  ·
    refine ⟨165310673810598287354315929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220414231747464383139087905 165310673810598287354315929)
    ·
      refine ⟨123983005357948715515736947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165310673810598287354315929 123983005357948715515736947)
      ·
        refine ⟨185974508036923073273605421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123983005357948715515736947 185974508036923073273605421)
        ·
          refine ⟨69740440513846152477602033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185974508036923073273605421 69740440513846152477602033)
          ·
            refine ⟨52305330385384614358201525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69740440513846152477602033 52305330385384614358201525)
            ·
              refine ⟨4903624723629807596081393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 52305330385384614358201525 4903624723629807596081393)
              ·
                refine ⟨3677718542722355697061045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4903624723629807596081393 3677718542722355697061045)
                ·
                  refine ⟨344786113380220846599473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3677718542722355697061045 344786113380220846599473)
                  ·
                    rfl

theorem cell23_6043217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 2, 5].length) (baseStart_6043217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043217 prefixEnd_6043217 := by exact prefixLift 6043217
  have htrace : WordTrace (prefixWord ++ tailWord_6043217) baseStart_6043217 baseEnd_6043217 := by
    simpa [prefixWord, tailWord_6043217, baseEnd_6043217] using wordTrace_append hprefix tailTrace_6043217
  have hstable : (prefixWord ++ tailWord_6043217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043217).length < 2 ^ (prefixWord ++ tailWord_6043217).sum := by decide
  have hdescent : baseEnd_6043217 < baseStart_6043217 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043222 : List Nat := [5, 2, 2, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_6043222 : Nat := 118140960795 + 6043222 * 2 ^ 59
def prefixEnd_6043222 : Nat := 4983230072969 + 3 ^ 40 * 6043222 * 2
def baseEnd_6043222 : Nat := 3103077587825260099832735

theorem tailTrace_6043222 : CollatzResearch.WordTrace tailWord_6043222 prefixEnd_6043222 3103077587825260099832735 := by
  unfold tailWord_6043222
  simp only [CollatzResearch.WordTrace]
  refine ⟨13775900882027891812063745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 146942942741630845995346613 13775900882027891812063745)
  ·
    refine ⟨10331925661520918859047809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13775900882027891812063745 10331925661520918859047809)
    ·
      refine ⟨7748944246140689144285857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10331925661520918859047809 7748944246140689144285857)
      ·
        refine ⟨5811708184605516858214393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7748944246140689144285857 5811708184605516858214393)
        ·
          refine ⟨4358781138454137643660795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5811708184605516858214393 4358781138454137643660795)
          ·
            refine ⟨6538171707681206465491193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4358781138454137643660795 6538171707681206465491193)
            ·
              refine ⟨4903628780760904849118395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6538171707681206465491193 4903628780760904849118395)
              ·
                refine ⟨7355443171141357273677593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903628780760904849118395 7355443171141357273677593)
                ·
                  refine ⟨5516582378356017955258195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7355443171141357273677593 5516582378356017955258195)
                  ·
                    refine ⟨8274873567534026932887293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5516582378356017955258195 8274873567534026932887293)
                    ·
                      refine ⟨3103077587825260099832735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8274873567534026932887293 3103077587825260099832735)
                      ·
                        rfl

theorem cell23_6043222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_6043222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043222 prefixEnd_6043222 := by exact prefixLift 6043222
  have htrace : WordTrace (prefixWord ++ tailWord_6043222) baseStart_6043222 baseEnd_6043222 := by
    simpa [prefixWord, tailWord_6043222, baseEnd_6043222] using wordTrace_append hprefix tailTrace_6043222
  have hstable : (prefixWord ++ tailWord_6043222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043222).length < 2 ^ (prefixWord ++ tailWord_6043222).sum := by decide
  have hdescent : baseEnd_6043222 < baseStart_6043222 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043223 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 7]
def baseStart_6043223 : Nat := 118140960795 + 6043223 * 2 ^ 59
def prefixEnd_6043223 : Nat := 4983230072969 + 3 ^ 40 * 6043223 * 2
def baseEnd_6043223 : Nat := 3103078101305914595920229

theorem tailTrace_6043223 : CollatzResearch.WordTrace tailWord_6043223 prefixEnd_6043223 3103078101305914595920229 := by
  unfold tailWord_6043223
  simp only [CollatzResearch.WordTrace]
  refine ⟨220414450585442646163806323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146942967056961764109204215 220414450585442646163806323)
  ·
    refine ⟨330621675878163969245709485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220414450585442646163806323 330621675878163969245709485)
    ·
      refine ⟨123983128454311488467141057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330621675878163969245709485 123983128454311488467141057)
      ·
        refine ⟨92987346340733616350355793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123983128454311488467141057 92987346340733616350355793)
        ·
          refine ⟨69740509755550212262766845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92987346340733616350355793 69740509755550212262766845)
          ·
            refine ⟨26152691158331329598537567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 69740509755550212262766845 26152691158331329598537567)
            ·
              refine ⟨39229036737496994397806351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26152691158331329598537567 39229036737496994397806351)
              ·
                refine ⟨58843555106245491596709527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39229036737496994397806351 58843555106245491596709527)
                ·
                  refine ⟨88265332659368237395064291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58843555106245491596709527 88265332659368237395064291)
                  ·
                    refine ⟨132397998989052356092596437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88265332659368237395064291 132397998989052356092596437)
                    ·
                      refine ⟨3103078101305914595920229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132397998989052356092596437 3103078101305914595920229)
                      ·
                        rfl

theorem cell23_6043223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 1, 7].length) (baseStart_6043223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043223 prefixEnd_6043223 := by exact prefixLift 6043223
  have htrace : WordTrace (prefixWord ++ tailWord_6043223) baseStart_6043223 baseEnd_6043223 := by
    simpa [prefixWord, tailWord_6043223, baseEnd_6043223] using wordTrace_append hprefix tailTrace_6043223
  have hstable : (prefixWord ++ tailWord_6043223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043223).length < 2 ^ (prefixWord ++ tailWord_6043223).sum := by decide
  have hdescent : baseEnd_6043223 < baseStart_6043223 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043228 : List Nat := [2, 2, 4, 1, 2, 3, 2, 1, 2, 2, 2]
def baseStart_6043228 : Nat := 118140960795 + 6043228 * 2 ^ 59
def prefixEnd_6043228 : Nat := 4983230072969 + 3 ^ 40 * 6043228 * 2
def baseEnd_6043228 : Nat := 3103080668709187076357707

theorem tailTrace_6043228 : CollatzResearch.WordTrace tailWord_6043228 prefixEnd_6043228 3103080668709187076357707 := by
  unfold tailWord_6043228
  simp only [CollatzResearch.WordTrace]
  refine ⟨110207316475212266008869169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146943088633616354678492225 110207316475212266008869169)
  ·
    refine ⟨82655487356409199506651877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110207316475212266008869169 82655487356409199506651877)
    ·
      refine ⟨15497903879326724907497227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82655487356409199506651877 15497903879326724907497227)
      ·
        refine ⟨23246855818990087361245841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15497903879326724907497227 23246855818990087361245841)
        ·
          refine ⟨17435141864242565520934381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23246855818990087361245841 17435141864242565520934381)
          ·
            refine ⟨6538178199090962070350393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17435141864242565520934381 6538178199090962070350393)
            ·
              refine ⟨4903633649318221552762795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6538178199090962070350393 4903633649318221552762795)
              ·
                refine ⟨7355450473977332329144193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903633649318221552762795 7355450473977332329144193)
                ·
                  refine ⟨5516587855482999246858145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7355450473977332329144193 5516587855482999246858145)
                  ·
                    refine ⟨4137440891612249435143609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5516587855482999246858145 4137440891612249435143609)
                    ·
                      refine ⟨3103080668709187076357707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137440891612249435143609 3103080668709187076357707)
                      ·
                        rfl

theorem cell23_6043228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_6043228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043228 prefixEnd_6043228 := by exact prefixLift 6043228
  have htrace : WordTrace (prefixWord ++ tailWord_6043228) baseStart_6043228 baseEnd_6043228 := by
    simpa [prefixWord, tailWord_6043228, baseEnd_6043228] using wordTrace_append hprefix tailTrace_6043228
  have hstable : (prefixWord ++ tailWord_6043228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043228).length < 2 ^ (prefixWord ++ tailWord_6043228).sum := by decide
  have hdescent : baseEnd_6043228 < baseStart_6043228 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043263 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 4]
def baseStart_6043263 : Nat := 118140960795 + 6043263 * 2 ^ 59
def prefixEnd_6043263 : Nat := 4983230072969 + 3 ^ 40 * 6043263 * 2
def baseEnd_6043263 : Nat := 3103098640532094439420045

theorem tailTrace_6043263 : CollatzResearch.WordTrace tailWord_6043263 prefixEnd_6043263 3103098640532094439420045 := by
  unfold tailWord_6043263
  simp only [CollatzResearch.WordTrace]
  refine ⟨220415909505297732995262443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146943939670198488663508295 220415909505297732995262443)
  ·
    refine ⟨330623864257946599492893665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220415909505297732995262443 330623864257946599492893665)
    ·
      refine ⟨247967898193459949619670249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330623864257946599492893665 247967898193459949619670249)
      ·
        refine ⟨185975923645094962214752687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247967898193459949619670249 185975923645094962214752687)
        ·
          refine ⟨278963885467642443322129031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185975923645094962214752687 278963885467642443322129031)
          ·
            refine ⟨418445828201463664983193547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278963885467642443322129031 418445828201463664983193547)
            ·
              refine ⟨627668742302195497474790321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 418445828201463664983193547 627668742302195497474790321)
              ·
                refine ⟨470751556726646623106092741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 627668742302195497474790321 470751556726646623106092741)
                ·
                  refine ⟨88265916886246241832392389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 470751556726646623106092741 88265916886246241832392389)
                  ·
                    refine ⟨16549859416171170343573573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 88265916886246241832392389 16549859416171170343573573)
                    ·
                      refine ⟨3103098640532094439420045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16549859416171170343573573 3103098640532094439420045)
                      ·
                        rfl

theorem cell23_6043263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_6043263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043263 prefixEnd_6043263 := by exact prefixLift 6043263
  have htrace : WordTrace (prefixWord ++ tailWord_6043263) baseStart_6043263 baseEnd_6043263 := by
    simpa [prefixWord, tailWord_6043263, baseEnd_6043263] using wordTrace_append hprefix tailTrace_6043263
  have hstable : (prefixWord ++ tailWord_6043263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043263).length < 2 ^ (prefixWord ++ tailWord_6043263).sum := by decide
  have hdescent : baseEnd_6043263 < baseStart_6043263 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043273 : List Nat := [1, 2, 1, 1, 4, 1, 2, 3, 8]
def baseStart_6043273 : Nat := 118140960795 + 6043273 * 2 ^ 59
def prefixEnd_6043273 : Nat := 4983230072969 + 3 ^ 40 * 6043273 * 2
def baseEnd_6043273 : Nat := 344789308370959933366111

theorem tailTrace_6043273 : CollatzResearch.WordTrace tailWord_6043273 prefixEnd_6043273 344789308370959933366111 := by
  unfold tailWord_6043273
  simp only [CollatzResearch.WordTrace]
  refine ⟨220416274235261504703126473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146944182823507669802084315 220416274235261504703126473)
  ·
    refine ⟨165312205676446128527344855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220416274235261504703126473 165312205676446128527344855)
    ·
      refine ⟨247968308514669192791017283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165312205676446128527344855 247968308514669192791017283)
      ·
        refine ⟨371952462772003789186525925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247968308514669192791017283 371952462772003789186525925)
        ·
          refine ⟨69741086769750710472473611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 371952462772003789186525925 69741086769750710472473611)
          ·
            refine ⟨104611630154626065708710417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69741086769750710472473611 104611630154626065708710417)
            ·
              refine ⟨78458722615969549281532813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104611630154626065708710417 78458722615969549281532813)
              ·
                refine ⟨29422020980988580980574805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78458722615969549281532813 29422020980988580980574805)
                ·
                  refine ⟨344789308370959933366111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29422020980988580980574805 344789308370959933366111)
                  ·
                    rfl

theorem cell23_6043273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 3, 8].length) (baseStart_6043273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043273 prefixEnd_6043273 := by exact prefixLift 6043273
  have htrace : WordTrace (prefixWord ++ tailWord_6043273) baseStart_6043273 baseEnd_6043273 := by
    simpa [prefixWord, tailWord_6043273, baseEnd_6043273] using wordTrace_append hprefix tailTrace_6043273
  have hstable : (prefixWord ++ tailWord_6043273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043273).length < 2 ^ (prefixWord ++ tailWord_6043273).sum := by decide
  have hdescent : baseEnd_6043273 < baseStart_6043273 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043294 : List Nat := [4, 3, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_6043294 : Nat := 118140960795 + 6043294 * 2 ^ 59
def prefixEnd_6043294 : Nat := 4983230072969 + 3 ^ 40 * 6043294 * 2
def baseEnd_6043294 : Nat := 1034371519477461272710801

theorem tailTrace_6043294 : CollatzResearch.WordTrace tailWord_6043294 prefixEnd_6043294 1034371519477461272710801 := by
  unfold tailWord_6043294
  simp only [CollatzResearch.WordTrace]
  refine ⟨27552130021023178161205117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146944693445456950193093957 27552130021023178161205117)
  ·
    refine ⟨10332048757883691810451919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27552130021023178161205117 10332048757883691810451919)
    ·
      refine ⟨15498073136825537715677879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10332048757883691810451919 15498073136825537715677879)
      ·
        refine ⟨23247109705238306573516819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15498073136825537715677879 23247109705238306573516819)
        ·
          refine ⟨34870664557857459860275229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23247109705238306573516819 34870664557857459860275229)
          ·
            refine ⟨13076499209196547447603211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34870664557857459860275229 13076499209196547447603211)
            ·
              refine ⟨19614748813794821171404817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13076499209196547447603211 19614748813794821171404817)
              ·
                refine ⟨14711061610346115878553613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19614748813794821171404817 14711061610346115878553613)
                ·
                  refine ⟨5516648103879793454457605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14711061610346115878553613 5516648103879793454457605)
                  ·
                    refine ⟨1034371519477461272710801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5516648103879793454457605 1034371519477461272710801)
                    ·
                      rfl

theorem cell23_6043294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_6043294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043294 prefixEnd_6043294 := by exact prefixLift 6043294
  have htrace : WordTrace (prefixWord ++ tailWord_6043294) baseStart_6043294 baseEnd_6043294 := by
    simpa [prefixWord, tailWord_6043294, baseEnd_6043294] using wordTrace_append hprefix tailTrace_6043294
  have hstable : (prefixWord ++ tailWord_6043294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043294).length < 2 ^ (prefixWord ++ tailWord_6043294).sum := by decide
  have hdescent : baseEnd_6043294 < baseStart_6043294 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043327 : List Nat := [1, 1, 2, 2, 2, 3, 2, 1, 4, 3, 2]
def baseStart_6043327 : Nat := 118140960795 + 6043327 * 2 ^ 59
def prefixEnd_6043327 : Nat := 4983230072969 + 3 ^ 40 * 6043327 * 2
def baseEnd_6043327 : Nat := 3103131503293982189019751

theorem tailTrace_6043327 : CollatzResearch.WordTrace tailWord_6043327 prefixEnd_6043327 3103131503293982189019751 := by
  unfold tailWord_6043327
  simp only [CollatzResearch.WordTrace]
  refine ⟨220418243777065871925592235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146945495851377247950394823 220418243777065871925592235)
  ·
    refine ⟨330627365665598807888388353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220418243777065871925592235 330627365665598807888388353)
    ·
      refine ⟨247970524249199105916291265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330627365665598807888388353 247970524249199105916291265)
      ·
        refine ⟨185977893186899329437218449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247970524249199105916291265 185977893186899329437218449)
        ·
          refine ⟨139483419890174497077913837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185977893186899329437218449 139483419890174497077913837)
          ·
            refine ⟨52306282458815436404217689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 139483419890174497077913837 52306282458815436404217689)
            ·
              refine ⟨39229711844111577303163267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52306282458815436404217689 39229711844111577303163267)
              ·
                refine ⟨58844567766167365954744901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39229711844111577303163267 58844567766167365954744901)
                ·
                  refine ⟨11033356456156381116514669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 58844567766167365954744901 11033356456156381116514669)
                  ·
                    refine ⟨4137508671058642918693001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11033356456156381116514669 4137508671058642918693001)
                    ·
                      refine ⟨3103131503293982189019751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137508671058642918693001 3103131503293982189019751)
                      ·
                        rfl

theorem cell23_6043327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 1, 4, 3, 2].length) (baseStart_6043327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043327 prefixEnd_6043327 := by exact prefixLift 6043327
  have htrace : WordTrace (prefixWord ++ tailWord_6043327) baseStart_6043327 baseEnd_6043327 := by
    simpa [prefixWord, tailWord_6043327, baseEnd_6043327] using wordTrace_append hprefix tailTrace_6043327
  have hstable : (prefixWord ++ tailWord_6043327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043327).length < 2 ^ (prefixWord ++ tailWord_6043327).sum := by decide
  have hdescent : baseEnd_6043327 < baseStart_6043327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043341 : List Nat := [1, 6, 2, 1, 1, 2, 3, 1, 6]
def baseStart_6043341 : Nat := 118140960795 + 6043341 * 2 ^ 59
def prefixEnd_6043341 : Nat := 4983230072969 + 3 ^ 40 * 6043341 * 2
def baseEnd_6043341 : Nat := 344793188002571681582743

theorem tailTrace_6043341 : CollatzResearch.WordTrace tailWord_6043341 prefixEnd_6043341 344793188002571681582743 := by
  unfold tailWord_6043341
  simp only [CollatzResearch.WordTrace]
  refine ⟨220418754399015152316601877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146945836266010101544401251 220418754399015152316601877)
  ·
    refine ⟨10332129112453835264840713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 220418754399015152316601877 10332129112453835264840713)
    ·
      refine ⟨7749096834340376448630535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10332129112453835264840713 7749096834340376448630535)
      ·
        refine ⟨11623645251510564672945803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7749096834340376448630535 11623645251510564672945803)
        ·
          refine ⟨17435467877265847009418705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11623645251510564672945803 17435467877265847009418705)
          ·
            refine ⟨13076600907949385257064029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17435467877265847009418705 13076600907949385257064029)
            ·
              refine ⟨4903725340481019471399011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13076600907949385257064029 4903725340481019471399011)
              ·
                refine ⟨7355588010721529207098517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903725340481019471399011 7355588010721529207098517)
                ·
                  refine ⟨344793188002571681582743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7355588010721529207098517 344793188002571681582743)
                  ·
                    rfl

theorem cell23_6043341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_6043341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043341 prefixEnd_6043341 := by exact prefixLift 6043341
  have htrace : WordTrace (prefixWord ++ tailWord_6043341) baseStart_6043341 baseEnd_6043341 := by
    simpa [prefixWord, tailWord_6043341, baseEnd_6043341] using wordTrace_append hprefix tailTrace_6043341
  have hstable : (prefixWord ++ tailWord_6043341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043341).length < 2 ^ (prefixWord ++ tailWord_6043341).sum := by decide
  have hdescent : baseEnd_6043341 < baseStart_6043341 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043368 : List Nat := [2, 1, 4, 1, 3, 3, 1, 3, 1, 1, 3]
def baseStart_6043368 : Nat := 118140960795 + 6043368 * 2 ^ 59
def prefixEnd_6043368 : Nat := 4983230072969 + 3 ^ 40 * 6043368 * 2
def baseEnd_6043368 : Nat := 3103152556000816528607063

theorem tailTrace_6043368 : CollatzResearch.WordTrace tailWord_6043368 prefixEnd_6043368 3103152556000816528607063 := by
  unfold tailWord_6043368
  simp only [CollatzResearch.WordTrace]
  refine ⟨110209869584958667963917379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146946492779944890618556505 110209869584958667963917379)
  ·
    refine ⟨165314804377438001945876069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110209869584958667963917379 165314804377438001945876069)
    ·
      refine ⟨30996525820769625364851763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 165314804377438001945876069 30996525820769625364851763)
      ·
        refine ⟨46494788731154438047277645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30996525820769625364851763 46494788731154438047277645)
        ·
          refine ⟨17435545774182914267729117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46494788731154438047277645 17435545774182914267729117)
          ·
            refine ⟨6538329665318592850398419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17435545774182914267729117 6538329665318592850398419)
            ·
              refine ⟨9807494497977889275597629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6538329665318592850398419 9807494497977889275597629)
              ·
                refine ⟨3677810436741708478349111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9807494497977889275597629 3677810436741708478349111)
                ·
                  refine ⟨5516715655112562717523667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3677810436741708478349111 5516715655112562717523667)
                  ·
                    refine ⟨8275073482668844076285501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5516715655112562717523667 8275073482668844076285501)
                    ·
                      refine ⟨3103152556000816528607063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8275073482668844076285501 3103152556000816528607063)
                      ·
                        rfl

theorem cell23_6043368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 1, 3, 1, 1, 3].length) (baseStart_6043368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043368 prefixEnd_6043368 := by exact prefixLift 6043368
  have htrace : WordTrace (prefixWord ++ tailWord_6043368) baseStart_6043368 baseEnd_6043368 := by
    simpa [prefixWord, tailWord_6043368, baseEnd_6043368] using wordTrace_append hprefix tailTrace_6043368
  have hstable : (prefixWord ++ tailWord_6043368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043368).length < 2 ^ (prefixWord ++ tailWord_6043368).sum := by decide
  have hdescent : baseEnd_6043368 < baseStart_6043368 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043377 : List Nat := [1, 2, 2, 2, 2, 4, 2, 1, 1, 1, 5]
def baseStart_6043377 : Nat := 118140960795 + 6043377 * 2 ^ 59
def prefixEnd_6043377 : Nat := 4983230072969 + 3 ^ 40 * 6043377 * 2
def baseEnd_6043377 : Nat := 3103157177326706993394521

theorem tailTrace_6043377 : CollatzResearch.WordTrace tailWord_6043377 prefixEnd_6043377 3103157177326706993394521 := by
  unfold tailWord_6043377
  simp only [CollatzResearch.WordTrace]
  refine ⟨220420067426884730464912385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146946711617923153643274923 220420067426884730464912385)
  ·
    refine ⟨165315050570163547848684289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220420067426884730464912385 165315050570163547848684289)
    ·
      refine ⟨123986287927622660886513217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165315050570163547848684289 123986287927622660886513217)
      ·
        refine ⟨92989715945716995664884913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123986287927622660886513217 92989715945716995664884913)
        ·
          refine ⟨69742286959287746748663685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92989715945716995664884913 69742286959287746748663685)
          ·
            refine ⟨13076678804866452515374441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69742286959287746748663685 13076678804866452515374441)
            ·
              refine ⟨9807509103649839386530831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13076678804866452515374441 9807509103649839386530831)
              ·
                refine ⟨14711263655474759079796247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9807509103649839386530831 14711263655474759079796247)
                ·
                  refine ⟨22066895483212138619694371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14711263655474759079796247 22066895483212138619694371)
                  ·
                    refine ⟨33100343224818207929541557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22066895483212138619694371 33100343224818207929541557)
                    ·
                      refine ⟨3103157177326706993394521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33100343224818207929541557 3103157177326706993394521)
                      ·
                        rfl

theorem cell23_6043377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 1, 5].length) (baseStart_6043377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043377 prefixEnd_6043377 := by exact prefixLift 6043377
  have htrace : WordTrace (prefixWord ++ tailWord_6043377) baseStart_6043377 baseEnd_6043377 := by
    simpa [prefixWord, tailWord_6043377, baseEnd_6043377] using wordTrace_append hprefix tailTrace_6043377
  have hstable : (prefixWord ++ tailWord_6043377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043377).length < 2 ^ (prefixWord ++ tailWord_6043377).sum := by decide
  have hdescent : baseEnd_6043377 < baseStart_6043377 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043391 : List Nat := [1, 1, 2, 2, 1, 3, 2, 6, 1, 2, 2]
def baseStart_6043391 : Nat := 118140960795 + 6043391 * 2 ^ 59
def prefixEnd_6043391 : Nat := 4983230072969 + 3 ^ 40 * 6043391 * 2
def baseEnd_6043391 : Nat := 3103164366055869938619457

theorem tailTrace_6043391 : CollatzResearch.WordTrace tailWord_6043391 prefixEnd_6043391 3103164366055869938619457 := by
  unfold tailWord_6043391
  simp only [CollatzResearch.WordTrace]
  refine ⟨220420578048834010855922027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146947052032556007237281351 220420578048834010855922027)
  ·
    refine ⟨330630867073251016283883041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220420578048834010855922027 330630867073251016283883041)
    ·
      refine ⟨247973150304938262212912281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330630867073251016283883041 247973150304938262212912281)
      ·
        refine ⟨185979862728703696659684211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247973150304938262212912281 185979862728703696659684211)
        ·
          refine ⟨278969794093055544989526317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185979862728703696659684211 278969794093055544989526317)
          ·
            refine ⟨104613672784895829371072369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278969794093055544989526317 104613672784895829371072369)
            ·
              refine ⟨78460254588671872028304277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104613672784895829371072369 78460254588671872028304277)
              ·
                refine ⟨3677824433843994001326763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 78460254588671872028304277 3677824433843994001326763)
                ·
                  refine ⟨5516736650765991001990145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3677824433843994001326763 5516736650765991001990145)
                  ·
                    refine ⟨4137552488074493251492609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5516736650765991001990145 4137552488074493251492609)
                    ·
                      refine ⟨3103164366055869938619457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137552488074493251492609 3103164366055869938619457)
                      ·
                        rfl

theorem cell23_6043391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 6, 1, 2, 2].length) (baseStart_6043391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043391 prefixEnd_6043391 := by exact prefixLift 6043391
  have htrace : WordTrace (prefixWord ++ tailWord_6043391) baseStart_6043391 baseEnd_6043391 := by
    simpa [prefixWord, tailWord_6043391, baseEnd_6043391] using wordTrace_append hprefix tailTrace_6043391
  have hstable : (prefixWord ++ tailWord_6043391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043391).length < 2 ^ (prefixWord ++ tailWord_6043391).sum := by decide
  have hdescent : baseEnd_6043391 < baseStart_6043391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043394 : List Nat := [3, 4, 1, 1, 1, 1, 2, 2, 3, 2, 3]
def baseStart_6043394 : Nat := 118140960795 + 6043394 * 2 ^ 59
def prefixEnd_6043394 : Nat := 4983230072969 + 3 ^ 40 * 6043394 * 2
def baseEnd_6043394 : Nat := 3103165906497833426881943

theorem tailTrace_6043394 : CollatzResearch.WordTrace tailWord_6043394 prefixEnd_6043394 3103165906497833426881943 := by
  unfold tailWord_6043394
  simp only [CollatzResearch.WordTrace]
  refine ⟨55105171866955785592070309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146947124978548761578854157 55105171866955785592070309)
  ·
    refine ⟨10332219725054209798513183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 55105171866955785592070309 10332219725054209798513183)
    ·
      refine ⟨15498329587581314697769775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10332219725054209798513183 15498329587581314697769775)
      ·
        refine ⟨23247494381371972046654663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15498329587581314697769775 23247494381371972046654663)
        ·
          refine ⟨34871241572057958069981995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23247494381371972046654663 34871241572057958069981995)
          ·
            refine ⟨52306862358086937104972993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34871241572057958069981995 52306862358086937104972993)
            ·
              refine ⟨39230146768565202828729745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 52306862358086937104972993 39230146768565202828729745)
              ·
                refine ⟨29422610076423902121547309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39230146768565202828729745 29422610076423902121547309)
                ·
                  refine ⟨11033478778658963295580241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29422610076423902121547309 11033478778658963295580241)
                  ·
                    refine ⟨8275109083994222471685181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11033478778658963295580241 8275109083994222471685181)
                    ·
                      refine ⟨3103165906497833426881943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8275109083994222471685181 3103165906497833426881943)
                      ·
                        rfl

theorem cell23_6043394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_6043394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043394 prefixEnd_6043394 := by exact prefixLift 6043394
  have htrace : WordTrace (prefixWord ++ tailWord_6043394) baseStart_6043394 baseEnd_6043394 := by
    simpa [prefixWord, tailWord_6043394, baseEnd_6043394] using wordTrace_append hprefix tailTrace_6043394
  have hstable : (prefixWord ++ tailWord_6043394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043394).length < 2 ^ (prefixWord ++ tailWord_6043394).sum := by decide
  have hdescent : baseEnd_6043394 < baseStart_6043394 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043400 : List Nat := [2, 1, 3, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_6043400 : Nat := 118140960795 + 6043400 * 2 ^ 59
def prefixEnd_6043400 : Nat := 4983230072969 + 3 ^ 40 * 6043400 * 2
def baseEnd_6043400 : Nat := 3103168987381760403406915

theorem tailTrace_6043400 : CollatzResearch.WordTrace tailWord_6043400 prefixEnd_6043400 3103168987381760403406915 := by
  unfold tailWord_6043400
  simp only [CollatzResearch.WordTrace]
  refine ⟨110210453152900702696499827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146947270870534270261999769 110210453152900702696499827)
  ·
    refine ⟨165315679729351054044749741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110210453152900702696499827 165315679729351054044749741)
    ·
      refine ⟨61993379898506645266781153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165315679729351054044749741 61993379898506645266781153)
      ·
        refine ⟨46495034923879983950085865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61993379898506645266781153 46495034923879983950085865)
        ·
          refine ⟨34871276192909987962564399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46495034923879983950085865 34871276192909987962564399)
          ·
            refine ⟨52306914289364981943846599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34871276192909987962564399 52306914289364981943846599)
            ·
              refine ⟨78460371434047472915769899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52306914289364981943846599 78460371434047472915769899)
              ·
                refine ⟨117690557151071209373654849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78460371434047472915769899 117690557151071209373654849)
                ·
                  refine ⟨88267917863303407030241137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117690557151071209373654849 88267917863303407030241137)
                  ·
                    refine ⟨66200938397477555272680853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 88267917863303407030241137 66200938397477555272680853)
                    ·
                      refine ⟨3103168987381760403406915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66200938397477555272680853 3103168987381760403406915)
                      ·
                        rfl

theorem cell23_6043400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_6043400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043400 prefixEnd_6043400 := by exact prefixLift 6043400
  have htrace : WordTrace (prefixWord ++ tailWord_6043400) baseStart_6043400 baseEnd_6043400 := by
    simpa [prefixWord, tailWord_6043400, baseEnd_6043400] using wordTrace_append hprefix tailTrace_6043400
  have hstable : (prefixWord ++ tailWord_6043400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043400).length < 2 ^ (prefixWord ++ tailWord_6043400).sum := by decide
  have hdescent : baseEnd_6043400 < baseStart_6043400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043407 : List Nat := [1, 1, 2, 1, 1, 1, 4, 2, 6, 1, 3]
def baseStart_6043407 : Nat := 118140960795 + 6043407 * 2 ^ 59
def prefixEnd_6043407 : Nat := 4983230072969 + 3 ^ 40 * 6043407 * 2
def baseEnd_6043407 : Nat := 3103172581746341876019383

theorem tailTrace_6043407 : CollatzResearch.WordTrace tailWord_6043407 prefixEnd_6043407 3103172581746341876019383 := by
  unfold tailWord_6043407
  simp only [CollatzResearch.WordTrace]
  refine ⟨220421161616776045588504475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146947441077850697059002983 220421161616776045588504475)
  ·
    refine ⟨330631742425164068382756713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220421161616776045588504475 330631742425164068382756713)
    ·
      refine ⟨247973806818873051287067535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330631742425164068382756713 247973806818873051287067535)
      ·
        refine ⟨371960710228309576930601303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247973806818873051287067535 371960710228309576930601303)
        ·
          refine ⟨557941065342464365395901955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 371960710228309576930601303 557941065342464365395901955)
          ·
            refine ⟨836911598013696548093852933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 557941065342464365395901955 836911598013696548093852933)
            ·
              refine ⟨156920924627568102767597425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 836911598013696548093852933 156920924627568102767597425)
              ·
                refine ⟨117690693470676077075698069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 156920924627568102767597425 117690693470676077075698069)
                ·
                  refine ⟨5516751256437941112923347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 117690693470676077075698069 5516751256437941112923347)
                  ·
                    refine ⟨8275126884656911669385021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5516751256437941112923347 8275126884656911669385021)
                    ·
                      refine ⟨3103172581746341876019383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8275126884656911669385021 3103172581746341876019383)
                      ·
                        rfl

theorem cell23_6043407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 6, 1, 3].length) (baseStart_6043407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043407 prefixEnd_6043407 := by exact prefixLift 6043407
  have htrace : WordTrace (prefixWord ++ tailWord_6043407) baseStart_6043407 baseEnd_6043407 := by
    simpa [prefixWord, tailWord_6043407, baseEnd_6043407] using wordTrace_append hprefix tailTrace_6043407
  have hstable : (prefixWord ++ tailWord_6043407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043407).length < 2 ^ (prefixWord ++ tailWord_6043407).sum := by decide
  have hdescent : baseEnd_6043407 < baseStart_6043407 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043441 : List Nat := [1, 2, 2, 3, 2, 3, 2, 2, 2, 1, 3]
def baseStart_6043441 : Nat := 118140960795 + 6043441 * 2 ^ 59
def prefixEnd_6043441 : Nat := 4983230072969 + 3 ^ 40 * 6043441 * 2
def baseEnd_6043441 : Nat := 3103190040088594742994227

theorem tailTrace_6043441 : CollatzResearch.WordTrace tailWord_6043441 prefixEnd_6043441 3103190040088594742994227 := by
  unfold tailWord_6043441
  simp only [CollatzResearch.WordTrace]
  refine ⟨220422401698652869395242177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146948267799101912930161451 220422401698652869395242177)
  ·
    refine ⟨165316801273989652046431633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220422401698652869395242177 165316801273989652046431633)
    ·
      refine ⟨123987600955492239034823725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165316801273989652046431633 123987600955492239034823725)
      ·
        refine ⟨46495350358309589638058897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 123987600955492239034823725 46495350358309589638058897)
        ·
          refine ⟨34871512768732192228544173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 46495350358309589638058897 34871512768732192228544173)
          ·
            refine ⟨13076817288274572085704065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34871512768732192228544173 13076817288274572085704065)
            ·
              refine ⟨9807612966205929064278049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13076817288274572085704065 9807612966205929064278049)
              ·
                refine ⟨7355709724654446798208537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9807612966205929064278049 7355709724654446798208537)
                ·
                  refine ⟨5516782293490835098656403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7355709724654446798208537 5516782293490835098656403)
                  ·
                    refine ⟨8275173440236252647984605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5516782293490835098656403 8275173440236252647984605)
                    ·
                      refine ⟨3103190040088594742994227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8275173440236252647984605 3103190040088594742994227)
                      ·
                        rfl

theorem cell23_6043441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 2, 2, 2, 1, 3].length) (baseStart_6043441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043441 prefixEnd_6043441 := by exact prefixLift 6043441
  have htrace : WordTrace (prefixWord ++ tailWord_6043441) baseStart_6043441 baseEnd_6043441 := by
    simpa [prefixWord, tailWord_6043441, baseEnd_6043441] using wordTrace_append hprefix tailTrace_6043441
  have hstable : (prefixWord ++ tailWord_6043441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043441).length < 2 ^ (prefixWord ++ tailWord_6043441).sum := by decide
  have hdescent : baseEnd_6043441 < baseStart_6043441 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043464 : List Nat := [2, 1, 3, 1, 1, 4, 1, 3, 1, 4, 2]
def baseStart_6043464 : Nat := 118140960795 + 6043464 * 2 ^ 59
def prefixEnd_6043464 : Nat := 4983230072969 + 3 ^ 40 * 6043464 * 2
def baseEnd_6043464 : Nat := 3103201850143648153006621

theorem tailTrace_6043464 : CollatzResearch.WordTrace tailWord_6043464 prefixEnd_6043464 3103201850143648153006621 := by
  unfold tailWord_6043464
  simp only [CollatzResearch.WordTrace]
  refine ⟨110211620288784772161664723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146948827051713029548886297 110211620288784772161664723)
  ·
    refine ⟨165317430433177158242497085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110211620288784772161664723 165317430433177158242497085)
    ·
      refine ⟨61994036412441434340936407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165317430433177158242497085 61994036412441434340936407)
      ·
        refine ⟨92991054618662151511404611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61994036412441434340936407 92991054618662151511404611)
        ·
          refine ⟨139486581927993227267106917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92991054618662151511404611 139486581927993227267106917)
          ·
            refine ⟨26153734111498730112582547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 139486581927993227267106917 26153734111498730112582547)
            ·
              refine ⟨39230601167248095168873821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26153734111498730112582547 39230601167248095168873821)
              ·
                refine ⟨14711475437718035688327683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39230601167248095168873821 14711475437718035688327683)
                ·
                  refine ⟨22067213156577053532491525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14711475437718035688327683 22067213156577053532491525)
                  ·
                    refine ⟨4137602466858197537342161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22067213156577053532491525 4137602466858197537342161)
                    ·
                      refine ⟨3103201850143648153006621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137602466858197537342161 3103201850143648153006621)
                      ·
                        rfl

theorem cell23_6043464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_6043464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043464 prefixEnd_6043464 := by exact prefixLift 6043464
  have htrace : WordTrace (prefixWord ++ tailWord_6043464) baseStart_6043464 baseEnd_6043464 := by
    simpa [prefixWord, tailWord_6043464, baseEnd_6043464] using wordTrace_append hprefix tailTrace_6043464
  have hstable : (prefixWord ++ tailWord_6043464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043464).length < 2 ^ (prefixWord ++ tailWord_6043464).sum := by decide
  have hdescent : baseEnd_6043464 < baseStart_6043464 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043480 : List Nat := [2, 1, 2, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_6043480 : Nat := 118140960795 + 6043480 * 2 ^ 59
def prefixEnd_6043480 : Nat := 4983230072969 + 3 ^ 40 * 6043480 * 2
def baseEnd_6043480 : Nat := 3103210065834120090406547

theorem tailTrace_6043480 : CollatzResearch.WordTrace tailWord_6043480 prefixEnd_6043480 3103210065834120090406547 := by
  unfold tailWord_6043480
  simp only [CollatzResearch.WordTrace]
  refine ⟨110211912072755789527955947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146949216097007719370607929 110211912072755789527955947)
  ·
    refine ⟨165317868109133684291933921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110211912072755789527955947 165317868109133684291933921)
    ·
      refine ⟨123988401081850263218950441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165317868109133684291933921 123988401081850263218950441)
      ·
        refine ⟨92991300811387697414212831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 123988401081850263218950441 92991300811387697414212831)
        ·
          refine ⟨139486951217081546121319247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 92991300811387697414212831 139486951217081546121319247)
          ·
            refine ⟨209230426825622319181978871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139486951217081546121319247 209230426825622319181978871)
            ·
              refine ⟨313845640238433478772968307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209230426825622319181978871 313845640238433478772968307)
              ·
                refine ⟨470768460357650218159452461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313845640238433478772968307 470768460357650218159452461)
                ·
                  refine ⟨176538172634118831809794673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 470768460357650218159452461 176538172634118831809794673)
                  ·
                    refine ⟨132403629475589123857346005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 176538172634118831809794673 132403629475589123857346005)
                    ·
                      refine ⟨3103210065834120090406547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132403629475589123857346005 3103210065834120090406547)
                      ·
                        rfl

theorem cell23_6043480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_6043480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043480 prefixEnd_6043480 := by exact prefixLift 6043480
  have htrace : WordTrace (prefixWord ++ tailWord_6043480) baseStart_6043480 baseEnd_6043480 := by
    simpa [prefixWord, tailWord_6043480, baseEnd_6043480] using wordTrace_append hprefix tailTrace_6043480
  have hstable : (prefixWord ++ tailWord_6043480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043480).length < 2 ^ (prefixWord ++ tailWord_6043480).sum := by decide
  have hdescent : baseEnd_6043480 < baseStart_6043480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043524 : List Nat := [2, 3, 2, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_6043524 : Nat := 118140960795 + 6043524 * 2 ^ 59
def prefixEnd_6043524 : Nat := 4983230072969 + 3 ^ 40 * 6043524 * 2
def baseEnd_6043524 : Nat := 3103232658982917918256345

theorem tailTrace_6043524 : CollatzResearch.WordTrace tailWord_6043524 prefixEnd_6043524 3103232658982917918256345 := by
  unfold tailWord_6043524
  simp only [CollatzResearch.WordTrace]
  refine ⟨110212714478676087285256813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146950285971568116380342417 110212714478676087285256813)
  ·
    refine ⟨41329767929503532731971305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110212714478676087285256813 41329767929503532731971305)
    ·
      refine ⟨30997325947127649548978479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41329767929503532731971305 30997325947127649548978479)
      ·
        refine ⟨46495988920691474323467719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30997325947127649548978479 46495988920691474323467719)
        ·
          refine ⟨69743983381037211485201579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46495988920691474323467719 69743983381037211485201579)
          ·
            refine ⟨104615975071555817227802369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69743983381037211485201579 104615975071555817227802369)
            ·
              refine ⟨78461981303666862920851777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104615975071555817227802369 78461981303666862920851777)
              ·
                refine ⟨58846485977750147190638833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78461981303666862920851777 58846485977750147190638833)
                ·
                  refine ⟨44134864483312610392979125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58846485977750147190638833 44134864483312610392979125)
                  ·
                    refine ⟨4137643545310557224341793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 44134864483312610392979125 4137643545310557224341793)
                    ·
                      refine ⟨3103232658982917918256345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137643545310557224341793 3103232658982917918256345)
                      ·
                        rfl

theorem cell23_6043524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_6043524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043524 prefixEnd_6043524 := by exact prefixLift 6043524
  have htrace : WordTrace (prefixWord ++ tailWord_6043524) baseStart_6043524 baseEnd_6043524 := by
    simpa [prefixWord, tailWord_6043524, baseEnd_6043524] using wordTrace_append hprefix tailTrace_6043524
  have hstable : (prefixWord ++ tailWord_6043524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043524).length < 2 ^ (prefixWord ++ tailWord_6043524).sum := by decide
  have hdescent : baseEnd_6043524 < baseStart_6043524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043537 : List Nat := [1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 4]
def baseStart_6043537 : Nat := 118140960795 + 6043537 * 2 ^ 59
def prefixEnd_6043537 : Nat := 4983230072969 + 3 ^ 40 * 6043537 * 2
def baseEnd_6043537 : Nat := 3103239334231426367393785

theorem tailTrace_6043537 : CollatzResearch.WordTrace tailWord_6043537 prefixEnd_6043537 3103239334231426367393785 := by
  unfold tailWord_6043537
  simp only [CollatzResearch.WordTrace]
  refine ⟨220425903106305077790736865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146950602070870051860491243 220425903106305077790736865)
  ·
    refine ⟨165319427329728808343052649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220425903106305077790736865 165319427329728808343052649)
    ·
      refine ⟨123989570497296606257289487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165319427329728808343052649 123989570497296606257289487)
      ·
        refine ⟨185984355745944909385934231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123989570497296606257289487 185984355745944909385934231)
        ·
          refine ⟨278976533618917364078901347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185984355745944909385934231 278976533618917364078901347)
          ·
            refine ⟨418464800428376046118352021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 278976533618917364078901347 418464800428376046118352021)
            ·
              refine ⟨19615537520080127161797751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 418464800428376046118352021 19615537520080127161797751)
              ·
                refine ⟨29423306280120190742696627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19615537520080127161797751 29423306280120190742696627)
                ·
                  refine ⟨44134959420180286114044941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 29423306280120190742696627 44134959420180286114044941)
                  ·
                    refine ⟨16550609782567607292766853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44134959420180286114044941 16550609782567607292766853)
                    ·
                      refine ⟨3103239334231426367393785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16550609782567607292766853 3103239334231426367393785)
                      ·
                        rfl

theorem cell23_6043537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 4].length) (baseStart_6043537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043537 prefixEnd_6043537 := by exact prefixLift 6043537
  have htrace : WordTrace (prefixWord ++ tailWord_6043537) baseStart_6043537 baseEnd_6043537 := by
    simpa [prefixWord, tailWord_6043537, baseEnd_6043537] using wordTrace_append hprefix tailTrace_6043537
  have hstable : (prefixWord ++ tailWord_6043537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043537).length < 2 ^ (prefixWord ++ tailWord_6043537).sum := by decide
  have hdescent : baseEnd_6043537 < baseStart_6043537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043538 : List Nat := [3, 2, 3, 2, 1, 3, 1, 3, 5]
def baseStart_6043538 : Nat := 118140960795 + 6043538 * 2 ^ 59
def prefixEnd_6043538 : Nat := 4983230072969 + 3 ^ 40 * 6043538 * 2
def baseEnd_6043538 : Nat := 344804427523564540386809

theorem tailTrace_6043538 : CollatzResearch.WordTrace tailWord_6043538 prefixEnd_6043538 344804427523564540386809 := by
  unfold tailWord_6043538
  simp only [CollatzResearch.WordTrace]
  refine ⟨55106484894825363740380817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146950626386200969974348845 55106484894825363740380817)
  ·
    refine ⟨41329863671119022805285613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55106484894825363740380817 41329863671119022805285613)
    ·
      refine ⟨15498698876669633551982105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41329863671119022805285613 15498698876669633551982105)
      ·
        refine ⟨11624024157502225163986579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15498698876669633551982105 11624024157502225163986579)
        ·
          refine ⟨17436036236253337745979869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11624024157502225163986579 17436036236253337745979869)
          ·
            refine ⟨6538513588595001654742451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17436036236253337745979869 6538513588595001654742451)
            ·
              refine ⟨9807770382892502482113677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6538513588595001654742451 9807770382892502482113677)
              ·
                refine ⟨3677913893584688430792629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9807770382892502482113677 3677913893584688430792629)
                ·
                  refine ⟨344804427523564540386809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3677913893584688430792629 344804427523564540386809)
                  ·
                    rfl

theorem cell23_6043538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 3, 5].length) (baseStart_6043538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043538 prefixEnd_6043538 := by exact prefixLift 6043538
  have htrace : WordTrace (prefixWord ++ tailWord_6043538) baseStart_6043538 baseEnd_6043538 := by
    simpa [prefixWord, tailWord_6043538, baseEnd_6043538] using wordTrace_append hprefix tailTrace_6043538
  have hstable : (prefixWord ++ tailWord_6043538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043538).length < 2 ^ (prefixWord ++ tailWord_6043538).sum := by decide
  have hdescent : baseEnd_6043538 < baseStart_6043538 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043566 : List Nat := [4, 1, 5, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6043566 : Nat := 118140960795 + 6043566 * 2 ^ 59
def prefixEnd_6043566 : Nat := 4983230072969 + 3 ^ 40 * 6043566 * 2
def baseEnd_6043566 : Nat := 3103254225170406753931153

theorem tailTrace_6043566 : CollatzResearch.WordTrace tailWord_6043566 prefixEnd_6043566 3103254225170406753931153 := by
  unfold tailWord_6043566
  simp only [CollatzResearch.WordTrace]
  refine ⟨27553370102900001967942819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146951307215466677162361701 27553370102900001967942819)
  ·
    refine ⟨41330055154350002951914229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27553370102900001967942819 41330055154350002951914229)
    ·
      refine ⟨3874692670720312776741959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 41330055154350002951914229 3874692670720312776741959)
      ·
        refine ⟨5812039006080469165112939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3874692670720312776741959 5812039006080469165112939)
        ·
          refine ⟨8718058509120703747669409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5812039006080469165112939 8718058509120703747669409)
          ·
            refine ⟨6538543881840527810752057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8718058509120703747669409 6538543881840527810752057)
            ·
              refine ⟨4903907911380395858064043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6538543881840527810752057 4903907911380395858064043)
              ·
                refine ⟨7355861867070593787096065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4903907911380395858064043 7355861867070593787096065)
                ·
                  refine ⟨5516896400302945340322049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7355861867070593787096065 5516896400302945340322049)
                  ·
                    refine ⟨4137672300227209005241537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5516896400302945340322049 4137672300227209005241537)
                    ·
                      refine ⟨3103254225170406753931153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137672300227209005241537 3103254225170406753931153)
                      ·
                        rfl

theorem cell23_6043566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6043566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043566 prefixEnd_6043566 := by exact prefixLift 6043566
  have htrace : WordTrace (prefixWord ++ tailWord_6043566) baseStart_6043566 baseEnd_6043566 := by
    simpa [prefixWord, tailWord_6043566, baseEnd_6043566] using wordTrace_append hprefix tailTrace_6043566
  have hstable : (prefixWord ++ tailWord_6043566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043566).length < 2 ^ (prefixWord ++ tailWord_6043566).sum := by decide
  have hdescent : baseEnd_6043566 < baseStart_6043566 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043615 : List Nat := [1, 1, 2, 3, 4, 3, 2, 2, 1, 4]
def baseStart_6043615 : Nat := 118140960795 + 6043615 * 2 ^ 59
def prefixEnd_6043615 : Nat := 4983230072969 + 3 ^ 40 * 6043615 * 2
def baseEnd_6043615 : Nat := 1034426461907492354072809

theorem tailTrace_6043615 : CollatzResearch.WordTrace tailWord_6043615 prefixEnd_6043615 1034426461907492354072809 := by
  unfold tailWord_6043615
  simp only [CollatzResearch.WordTrace]
  refine ⟨220428748000022497112076299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146952498666681664741384199 220428748000022497112076299)
  ·
    refine ⟨330643122000033745668114449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220428748000022497112076299 330643122000033745668114449)
    ·
      refine ⟨247982341500025309251085837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330643122000033745668114449 247982341500025309251085837)
      ·
        refine ⟨92993378062509490969157189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 247982341500025309251085837 92993378062509490969157189)
        ·
          refine ⟨17436258386720529556716973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 92993378062509490969157189 17436258386720529556716973)
          ·
            refine ⟨6538596895020198583768865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17436258386720529556716973 6538596895020198583768865)
            ·
              refine ⟨4903947671265148937826649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6538596895020198583768865 4903947671265148937826649)
              ·
                refine ⟨3677960753448861703369987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4903947671265148937826649 3677960753448861703369987)
                ·
                  refine ⟨5516941130173292555054981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3677960753448861703369987 5516941130173292555054981)
                  ·
                    refine ⟨1034426461907492354072809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5516941130173292555054981 1034426461907492354072809)
                    ·
                      rfl

theorem cell23_6043615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 2, 1, 4].length) (baseStart_6043615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043615 prefixEnd_6043615 := by exact prefixLift 6043615
  have htrace : WordTrace (prefixWord ++ tailWord_6043615) baseStart_6043615 baseEnd_6043615 := by
    simpa [prefixWord, tailWord_6043615, baseEnd_6043615] using wordTrace_append hprefix tailTrace_6043615
  have hstable : (prefixWord ++ tailWord_6043615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043615).length < 2 ^ (prefixWord ++ tailWord_6043615).sum := by decide
  have hdescent : baseEnd_6043615 < baseStart_6043615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043644 : List Nat := [2, 2, 2, 1, 2, 2, 1, 3, 3, 1, 4]
def baseStart_6043644 : Nat := 118140960795 + 6043644 * 2 ^ 59
def prefixEnd_6043644 : Nat := 4983230072969 + 3 ^ 40 * 6043644 * 2
def baseEnd_6043644 : Nat := 3103294276661457448755793

theorem tailTrace_6043644 : CollatzResearch.WordTrace tailWord_6043644 prefixEnd_6043644 3103294276661457448755793 := by
  unfold tailWord_6043644
  simp only [CollatzResearch.WordTrace]
  refine ⟨110214902858458717532440993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146953203811278290043254657 110214902858458717532440993)
  ·
    refine ⟨82661177143844038149330745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110214902858458717532440993 82661177143844038149330745)
    ·
      refine ⟨61995882857883028611998059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 82661177143844038149330745 61995882857883028611998059)
      ·
        refine ⟨92993824286824542917997089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61995882857883028611998059 92993824286824542917997089)
        ·
          refine ⟨69745368215118407188497817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92993824286824542917997089 69745368215118407188497817)
          ·
            refine ⟨52309026161338805391373363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69745368215118407188497817 52309026161338805391373363)
            ·
              refine ⟨78463539242008208087060045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52309026161338805391373363 78463539242008208087060045)
              ·
                refine ⟨29423827215753078032647517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 78463539242008208087060045 29423827215753078032647517)
                ·
                  refine ⟨11033935205907404262242819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 29423827215753078032647517 11033935205907404262242819)
                  ·
                    refine ⟨16550902808861106393364229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11033935205907404262242819 16550902808861106393364229)
                    ·
                      refine ⟨3103294276661457448755793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16550902808861106393364229 3103294276661457448755793)
                      ·
                        rfl

theorem cell23_6043644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_6043644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043644 prefixEnd_6043644 := by exact prefixLift 6043644
  have htrace : WordTrace (prefixWord ++ tailWord_6043644) baseStart_6043644 baseEnd_6043644 := by
    simpa [prefixWord, tailWord_6043644, baseEnd_6043644] using wordTrace_append hprefix tailTrace_6043644
  have hstable : (prefixWord ++ tailWord_6043644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043644).length < 2 ^ (prefixWord ++ tailWord_6043644).sum := by decide
  have hdescent : baseEnd_6043644 < baseStart_6043644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043655 : List Nat := [1, 1, 4, 3, 1, 3, 2, 3, 1, 1, 3]
def baseStart_6043655 : Nat := 118140960795 + 6043655 * 2 ^ 59
def prefixEnd_6043655 : Nat := 4983230072969 + 3 ^ 40 * 6043655 * 2
def baseEnd_6043655 : Nat := 3103299924948656905718243

theorem tailTrace_6043655 : CollatzResearch.WordTrace tailWord_6043655 prefixEnd_6043655 3103299924948656905718243 := by
  unfold tailWord_6043655
  simp only [CollatzResearch.WordTrace]
  refine ⟨220430206919877583943532419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146953471279918389295688279 220430206919877583943532419)
  ·
    refine ⟨330645310379816375915298629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220430206919877583943532419 330645310379816375915298629)
    ·
      refine ⟨61995995696215570484118493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 330645310379816375915298629 61995995696215570484118493)
      ·
        refine ⟨23248498386080838931544435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61995995696215570484118493 23248498386080838931544435)
        ·
          refine ⟨34872747579121258397316653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23248498386080838931544435 34872747579121258397316653)
          ·
            refine ⟨13077280342170471898993745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34872747579121258397316653 13077280342170471898993745)
            ·
              refine ⟨9807960256627853924245309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13077280342170471898993745 9807960256627853924245309)
              ·
                refine ⟨3677985096235445221591991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9807960256627853924245309 3677985096235445221591991)
                ·
                  refine ⟨5516977644353167832387987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3677985096235445221591991 5516977644353167832387987)
                  ·
                    refine ⟨8275466466529751748581981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5516977644353167832387987 8275466466529751748581981)
                    ·
                      refine ⟨3103299924948656905718243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8275466466529751748581981 3103299924948656905718243)
                      ·
                        rfl

theorem cell23_6043655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_6043655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043655 prefixEnd_6043655 := by exact prefixLift 6043655
  have htrace : WordTrace (prefixWord ++ tailWord_6043655) baseStart_6043655 baseEnd_6043655 := by
    simpa [prefixWord, tailWord_6043655, baseEnd_6043655] using wordTrace_append hprefix tailTrace_6043655
  have hstable : (prefixWord ++ tailWord_6043655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043655).length < 2 ^ (prefixWord ++ tailWord_6043655).sum := by decide
  have hdescent : baseEnd_6043655 < baseStart_6043655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043657 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 6]
def baseStart_6043657 : Nat := 118140960795 + 6043657 * 2 ^ 59
def prefixEnd_6043657 : Nat := 4983230072969 + 3 ^ 40 * 6043657 * 2
def baseEnd_6043657 : Nat := 3103300951909965897893233

theorem tailTrace_6043657 : CollatzResearch.WordTrace tailWord_6043657 prefixEnd_6043657 3103300951909965897893233 := by
  unfold tailWord_6043657
  simp only [CollatzResearch.WordTrace]
  refine ⟨220430279865870338285105225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146953519910580225523403483 220430279865870338285105225)
  ·
    refine ⟨165322709899402753713828919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220430279865870338285105225 165322709899402753713828919)
    ·
      refine ⟨247984064849104130570743379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165322709899402753713828919 247984064849104130570743379)
      ·
        refine ⟨371976097273656195856115069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247984064849104130570743379 371976097273656195856115069)
        ·
          refine ⟨139491036477621073446043151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371976097273656195856115069 139491036477621073446043151)
          ·
            refine ⟨209236554716431610169064727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139491036477621073446043151 209236554716431610169064727)
            ·
              refine ⟨313854832074647415253597091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 209236554716431610169064727 313854832074647415253597091)
              ·
                refine ⟨470782248111971122880395637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 313854832074647415253597091 470782248111971122880395637)
                ·
                  refine ⟨44135835760497292770037091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 470782248111971122880395637 44135835760497292770037091)
                  ·
                    refine ⟨66203753640745939155055637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 44135835760497292770037091 66203753640745939155055637)
                    ·
                      refine ⟨3103300951909965897893233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 66203753640745939155055637 3103300951909965897893233)
                      ·
                        rfl

theorem cell23_6043657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 5, 1, 6].length) (baseStart_6043657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043657 prefixEnd_6043657 := by exact prefixLift 6043657
  have htrace : WordTrace (prefixWord ++ tailWord_6043657) baseStart_6043657 baseEnd_6043657 := by
    simpa [prefixWord, tailWord_6043657, baseEnd_6043657] using wordTrace_append hprefix tailTrace_6043657
  have hstable : (prefixWord ++ tailWord_6043657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043657).length < 2 ^ (prefixWord ++ tailWord_6043657).sum := by decide
  have hdescent : baseEnd_6043657 < baseStart_6043657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043681 : List Nat := [1, 2, 3, 2, 4, 1, 1, 2, 1, 1, 5]
def baseStart_6043681 : Nat := 118140960795 + 6043681 * 2 ^ 59
def prefixEnd_6043681 : Nat := 4983230072969 + 3 ^ 40 * 6043681 * 2
def baseEnd_6043681 : Nat := 3103313275445673803993123

theorem tailTrace_6043681 : CollatzResearch.WordTrace tailWord_6043681 prefixEnd_6043681 3103313275445673803993123 := by
  unfold tailWord_6043681
  simp only [CollatzResearch.WordTrace]
  refine ⟨220431155217783390383978897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146954103478522260255985931 220431155217783390383978897)
  ·
    refine ⟨165323366413337542787984173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220431155217783390383978897 165323366413337542787984173)
    ·
      refine ⟨61996262405001578545494065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165323366413337542787984173 61996262405001578545494065)
      ·
        refine ⟨46497196803751183909120549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61996262405001578545494065 46497196803751183909120549)
        ·
          refine ⟨8718224400703346982960103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 46497196803751183909120549 8718224400703346982960103)
          ·
            refine ⟨13077336601055020474440155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8718224400703346982960103 13077336601055020474440155)
            ·
              refine ⟨19616004901582530711660233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13077336601055020474440155 19616004901582530711660233)
              ·
                refine ⟨14712003676186898033745175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19616004901582530711660233 14712003676186898033745175)
                ·
                  refine ⟨22068005514280347050617763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14712003676186898033745175 22068005514280347050617763)
                  ·
                    refine ⟨33102008271420520575926645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22068005514280347050617763 33102008271420520575926645)
                    ·
                      refine ⟨3103313275445673803993123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33102008271420520575926645 3103313275445673803993123)
                      ·
                        rfl

theorem cell23_6043681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_6043681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043681 prefixEnd_6043681 := by exact prefixLift 6043681
  have htrace : WordTrace (prefixWord ++ tailWord_6043681) baseStart_6043681 baseEnd_6043681 := by
    simpa [prefixWord, tailWord_6043681, baseEnd_6043681] using wordTrace_append hprefix tailTrace_6043681
  have hstable : (prefixWord ++ tailWord_6043681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043681).length < 2 ^ (prefixWord ++ tailWord_6043681).sum := by decide
  have hdescent : baseEnd_6043681 < baseStart_6043681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043698 : List Nat := [3, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3]
def baseStart_6043698 : Nat := 118140960795 + 6043698 * 2 ^ 59
def prefixEnd_6043698 : Nat := 4983230072969 + 3 ^ 40 * 6043698 * 2
def baseEnd_6043698 : Nat := 3103322004616800237480545

theorem tailTrace_6043698 : CollatzResearch.WordTrace tailWord_6043698 prefixEnd_6043698 3103322004616800237480545 := by
  unfold tailWord_6043698
  simp only [CollatzResearch.WordTrace]
  refine ⟨55107943814680450571836937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146954516839147868191565165 55107943814680450571836937)
  ·
    refine ⟨41330957861010337928877703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 55107943814680450571836937 41330957861010337928877703)
    ·
      refine ⟨61996436791515506893316555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41330957861010337928877703 61996436791515506893316555)
      ·
        refine ⟨92994655187273260339974833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61996436791515506893316555 92994655187273260339974833)
        ·
          refine ⟨69745991390454945254981125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 92994655187273260339974833 69745991390454945254981125)
          ·
            refine ⟨13077373385710302235308961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 69745991390454945254981125 13077373385710302235308961)
            ·
              refine ⟨9808030039282726676481721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13077373385710302235308961 9808030039282726676481721)
              ·
                refine ⟨7356022529462045007361291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9808030039282726676481721 7356022529462045007361291)
                ·
                  refine ⟨11034033794193067511041937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7356022529462045007361291 11034033794193067511041937)
                  ·
                    refine ⟨8275525345644800633281453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11034033794193067511041937 8275525345644800633281453)
                    ·
                      refine ⟨3103322004616800237480545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8275525345644800633281453 3103322004616800237480545)
                      ·
                        rfl

theorem cell23_6043698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_6043698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043698 prefixEnd_6043698 := by exact prefixLift 6043698
  have htrace : WordTrace (prefixWord ++ tailWord_6043698) baseStart_6043698 baseEnd_6043698 := by
    simpa [prefixWord, tailWord_6043698, baseEnd_6043698] using wordTrace_append hprefix tailTrace_6043698
  have hstable : (prefixWord ++ tailWord_6043698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043698).length < 2 ^ (prefixWord ++ tailWord_6043698).sum := by decide
  have hdescent : baseEnd_6043698 < baseStart_6043698 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043711 : List Nat := [1, 1, 2, 2, 3, 1, 3, 2, 4, 1, 3]
def baseStart_6043711 : Nat := 118140960795 + 6043711 * 2 ^ 59
def prefixEnd_6043711 : Nat := 4983230072969 + 3 ^ 40 * 6043711 * 2
def baseEnd_6043711 : Nat := 3103328679865308686617985

theorem tailTrace_6043711 : CollatzResearch.WordTrace tailWord_6043711 prefixEnd_6043711 3103328679865308686617985 := by
  unfold tailWord_6043711
  simp only [CollatzResearch.WordTrace]
  refine ⟨220432249407674705507570987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146954832938449803671713991 220432249407674705507570987)
  ·
    refine ⟨330648374111512058261356481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220432249407674705507570987 330648374111512058261356481)
    ·
      refine ⟨247986280583634043696017361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330648374111512058261356481 247986280583634043696017361)
      ·
        refine ⟨185989710437725532772013021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247986280583634043696017361 185989710437725532772013021)
        ·
          refine ⟨69746141414147074789504883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 185989710437725532772013021 69746141414147074789504883)
          ·
            refine ⟨104619212121220612184257325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69746141414147074789504883 104619212121220612184257325)
            ·
              refine ⟨39232204545457729569096497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 104619212121220612184257325 39232204545457729569096497)
              ·
                refine ⟨29424153409093297176822373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 39232204545457729569096497 29424153409093297176822373)
                ·
                  refine ⟨5517028764204993220654195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 29424153409093297176822373 5517028764204993220654195)
                  ·
                    refine ⟨8275543146307489830981293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5517028764204993220654195 8275543146307489830981293)
                    ·
                      refine ⟨3103328679865308686617985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8275543146307489830981293 3103328679865308686617985)
                      ·
                        rfl

theorem cell23_6043711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 2, 4, 1, 3].length) (baseStart_6043711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043711 prefixEnd_6043711 := by exact prefixLift 6043711
  have htrace : WordTrace (prefixWord ++ tailWord_6043711) baseStart_6043711 baseEnd_6043711 := by
    simpa [prefixWord, tailWord_6043711, baseEnd_6043711] using wordTrace_append hprefix tailTrace_6043711
  have hstable : (prefixWord ++ tailWord_6043711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043711).length < 2 ^ (prefixWord ++ tailWord_6043711).sum := by decide
  have hdescent : baseEnd_6043711 < baseStart_6043711 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043712 : List Nat := [2, 1, 1, 2, 2, 6, 1, 3, 1, 2, 2]
def baseStart_6043712 : Nat := 118140960795 + 6043712 * 2 ^ 59
def prefixEnd_6043712 : Nat := 4983230072969 + 3 ^ 40 * 6043712 * 2
def baseEnd_6043712 : Nat := 3103329193345963182705481

theorem tailTrace_6043712 : CollatzResearch.WordTrace tailWord_6043712 prefixEnd_6043712 3103329193345963182705481 := by
  unfold tailWord_6043712
  simp only [CollatzResearch.WordTrace]
  refine ⟨110216142940335541339178695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146954857253780721785571593 110216142940335541339178695)
  ·
    refine ⟨165324214410503312008768043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110216142940335541339178695 165324214410503312008768043)
    ·
      refine ⟨247986321615754968013152065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165324214410503312008768043 247986321615754968013152065)
      ·
        refine ⟨185989741211816226009864049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 247986321615754968013152065 185989741211816226009864049)
        ·
          refine ⟨139492305908862169507398037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 185989741211816226009864049 139492305908862169507398037)
          ·
            refine ⟨6538701839477914195659283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 139492305908862169507398037 6538701839477914195659283)
            ·
              refine ⟨9808052759216871293488925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6538701839477914195659283 9808052759216871293488925)
              ·
                refine ⟨3678019784706326735058347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9808052759216871293488925 3678019784706326735058347)
                ·
                  refine ⟨5517029677059490102587521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678019784706326735058347 5517029677059490102587521)
                  ·
                    refine ⟨4137772257794617576940641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5517029677059490102587521 4137772257794617576940641)
                    ·
                      refine ⟨3103329193345963182705481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137772257794617576940641 3103329193345963182705481)
                      ·
                        rfl

theorem cell23_6043712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 3, 1, 2, 2].length) (baseStart_6043712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043712 prefixEnd_6043712 := by exact prefixLift 6043712
  have htrace : WordTrace (prefixWord ++ tailWord_6043712) baseStart_6043712 baseEnd_6043712 := by
    simpa [prefixWord, tailWord_6043712, baseEnd_6043712] using wordTrace_append hprefix tailTrace_6043712
  have hstable : (prefixWord ++ tailWord_6043712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043712).length < 2 ^ (prefixWord ++ tailWord_6043712).sum := by decide
  have hdescent : baseEnd_6043712 < baseStart_6043712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043785 : List Nat := [1, 2, 1, 1, 4, 2, 4, 2, 2, 2, 2]
def baseStart_6043785 : Nat := 118140960795 + 6043785 * 2 ^ 59
def prefixEnd_6043785 : Nat := 4983230072969 + 3 ^ 40 * 6043785 * 2
def baseEnd_6043785 : Nat := 3103366677433741397092645

theorem tailTrace_6043785 : CollatzResearch.WordTrace tailWord_6043785 prefixEnd_6043785 3103366677433741397092645 := by
  unfold tailWord_6043785
  simp only [CollatzResearch.WordTrace]
  refine ⟨220434948409406616145764809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146956632272937744097176539 220434948409406616145764809)
  ·
    refine ⟨165326211307054962109323607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220434948409406616145764809 165326211307054962109323607)
    ·
      refine ⟨247989316960582443163985411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165326211307054962109323607 247989316960582443163985411)
      ·
        refine ⟨371983975440873664745978117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247989316960582443163985411 371983975440873664745978117)
        ·
          refine ⟨69746995395163812139870897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 371983975440873664745978117 69746995395163812139870897)
          ·
            refine ⟨52310246546372859104903173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 69746995395163812139870897 52310246546372859104903173)
            ·
              refine ⟨9808171227444911082169345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 52310246546372859104903173 9808171227444911082169345)
              ·
                refine ⟨7356128420583683311627009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9808171227444911082169345 7356128420583683311627009)
                ·
                  refine ⟨5517096315437762483720257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7356128420583683311627009 5517096315437762483720257)
                  ·
                    refine ⟨4137822236578321862790193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5517096315437762483720257 4137822236578321862790193)
                    ·
                      refine ⟨3103366677433741397092645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137822236578321862790193 3103366677433741397092645)
                      ·
                        rfl

theorem cell23_6043785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 2, 2, 2, 2].length) (baseStart_6043785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043785 prefixEnd_6043785 := by exact prefixLift 6043785
  have htrace : WordTrace (prefixWord ++ tailWord_6043785) baseStart_6043785 baseEnd_6043785 := by
    simpa [prefixWord, tailWord_6043785, baseEnd_6043785] using wordTrace_append hprefix tailTrace_6043785
  have hstable : (prefixWord ++ tailWord_6043785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043785).length < 2 ^ (prefixWord ++ tailWord_6043785).sum := by decide
  have hdescent : baseEnd_6043785 < baseStart_6043785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043825 : List Nat := [1, 2, 2, 5, 2, 1, 2, 3, 5]
def baseStart_6043825 : Nat := 118140960795 + 6043825 * 2 ^ 59
def prefixEnd_6043825 : Nat := 4983230072969 + 3 ^ 40 * 6043825 * 2
def baseEnd_6043825 : Nat := 344820801851102360065829

theorem tailTrace_6043825 : CollatzResearch.WordTrace tailWord_6043825 prefixEnd_6043825 344820801851102360065829 := by
  unfold tailWord_6043825
  simp only [CollatzResearch.WordTrace]
  refine ⟨220436407329261702977220929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146957604886174468651480619 220436407329261702977220929)
  ·
    refine ⟨165327305496946277232915697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220436407329261702977220929 165327305496946277232915697)
    ·
      refine ⟨123995479122709707924686773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165327305496946277232915697 123995479122709707924686773)
      ·
        refine ⟨11624576167754035117939385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 123995479122709707924686773 11624576167754035117939385)
        ·
          refine ⟨8718432125815526338454539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11624576167754035117939385 8718432125815526338454539)
          ·
            refine ⟨13077648188723289507681809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8718432125815526338454539 13077648188723289507681809)
            ·
              refine ⟨9808236141542467130761357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13077648188723289507681809 9808236141542467130761357)
              ·
                refine ⟨3678088553078425174035509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9808236141542467130761357 3678088553078425174035509)
                ·
                  refine ⟨344820801851102360065829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3678088553078425174035509 344820801851102360065829)
                  ·
                    rfl

theorem cell23_6043825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 3, 5].length) (baseStart_6043825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043825 prefixEnd_6043825 := by exact prefixLift 6043825
  have htrace : WordTrace (prefixWord ++ tailWord_6043825) baseStart_6043825 baseEnd_6043825 := by
    simpa [prefixWord, tailWord_6043825, baseEnd_6043825] using wordTrace_append hprefix tailTrace_6043825
  have hstable : (prefixWord ++ tailWord_6043825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043825).length < 2 ^ (prefixWord ++ tailWord_6043825).sum := by decide
  have hdescent : baseEnd_6043825 < baseStart_6043825 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043842 : List Nat := [3, 5, 1, 1, 1, 1, 2, 4, 5]
def baseStart_6043842 : Nat := 118140960795 + 6043842 * 2 ^ 59
def prefixEnd_6043842 : Nat := 4983230072969 + 3 ^ 40 * 6043842 * 2
def baseEnd_6043842 : Nat := 344821771759005297119987

theorem tailTrace_6043842 : CollatzResearch.WordTrace tailWord_6043842 prefixEnd_6043842 344821771759005297119987 := by
  unfold tailWord_6043842
  simp only [CollatzResearch.WordTrace]
  refine ⟨55109256842550028720147445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146958018246800076587059853 55109256842550028720147445)
  ·
    refine ⟨5166492828989065192513823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 55109256842550028720147445 5166492828989065192513823)
    ·
      refine ⟨7749739243483597788770735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5166492828989065192513823 7749739243483597788770735)
      ·
        refine ⟨11624608865225396683156103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7749739243483597788770735 11624608865225396683156103)
        ·
          refine ⟨17436913297838095024734155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11624608865225396683156103 17436913297838095024734155)
          ·
            refine ⟨26155369946757142537101233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17436913297838095024734155 26155369946757142537101233)
            ·
              refine ⟨19616527460067856902825925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26155369946757142537101233 19616527460067856902825925)
              ·
                refine ⟨3678098898762723169279861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19616527460067856902825925 3678098898762723169279861)
                ·
                  refine ⟨344821771759005297119987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3678098898762723169279861 344821771759005297119987)
                  ·
                    rfl

theorem cell23_6043842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_6043842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043842 prefixEnd_6043842 := by exact prefixLift 6043842
  have htrace : WordTrace (prefixWord ++ tailWord_6043842) baseStart_6043842 baseEnd_6043842 := by
    simpa [prefixWord, tailWord_6043842, baseEnd_6043842] using wordTrace_append hprefix tailTrace_6043842
  have hstable : (prefixWord ++ tailWord_6043842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043842).length < 2 ^ (prefixWord ++ tailWord_6043842).sum := by decide
  have hdescent : baseEnd_6043842 < baseStart_6043842 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043935 : List Nat := [1, 1, 2, 4, 3, 1, 1, 3, 2, 3, 2]
def baseStart_6043935 : Nat := 118140960795 + 6043935 * 2 ^ 59
def prefixEnd_6043935 : Nat := 4983230072969 + 3 ^ 40 * 6043935 * 2
def baseEnd_6043935 : Nat := 3103443699531915810216955

theorem tailTrace_6043935 : CollatzResearch.WordTrace tailWord_6043935 prefixEnd_6043935 3103443699531915810216955 := by
  unfold tailWord_6043935
  simp only [CollatzResearch.WordTrace]
  refine ⟨220440419358863191763725259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146960279572575461175816839 220440419358863191763725259)
  ·
    refine ⟨330660629038294787645587889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220440419358863191763725259 330660629038294787645587889)
    ·
      refine ⟨247995471778721090734190917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330660629038294787645587889 247995471778721090734190917)
      ·
        refine ⟨46499150958510204512660797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 247995471778721090734190917 46499150958510204512660797)
        ·
          refine ⟨17437181609441326692247799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46499150958510204512660797 17437181609441326692247799)
          ·
            refine ⟨26155772414161990038371699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17437181609441326692247799 26155772414161990038371699)
            ·
              refine ⟨39233658621242985057557549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26155772414161990038371699 39233658621242985057557549)
              ·
                refine ⟨14712621982966119396584081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 39233658621242985057557549 14712621982966119396584081)
                ·
                  refine ⟨11034466487224589547438061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14712621982966119396584081 11034466487224589547438061)
                  ·
                    refine ⟨4137924932709221080289273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11034466487224589547438061 4137924932709221080289273)
                    ·
                      refine ⟨3103443699531915810216955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4137924932709221080289273 3103443699531915810216955)
                      ·
                        rfl

theorem cell23_6043935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 3, 2, 3, 2].length) (baseStart_6043935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043935 prefixEnd_6043935 := by exact prefixLift 6043935
  have htrace : WordTrace (prefixWord ++ tailWord_6043935) baseStart_6043935 baseEnd_6043935 := by
    simpa [prefixWord, tailWord_6043935, baseEnd_6043935] using wordTrace_append hprefix tailTrace_6043935
  have hstable : (prefixWord ++ tailWord_6043935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043935).length < 2 ^ (prefixWord ++ tailWord_6043935).sum := by decide
  have hdescent : baseEnd_6043935 < baseStart_6043935 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043948 : List Nat := [2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 4]
def baseStart_6043948 : Nat := 118140960795 + 6043948 * 2 ^ 59
def prefixEnd_6043948 : Nat := 4983230072969 + 3 ^ 40 * 6043948 * 2
def baseEnd_6043948 : Nat := 3103450374780424259354395

theorem tailTrace_6043948 : CollatzResearch.WordTrace tailWord_6043948 prefixEnd_6043948 3103450374780424259354395 := by
  unfold tailWord_6043948
  simp only [CollatzResearch.WordTrace]
  refine ⟨110220446753908047491974249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146960595671877396655965665 110220446753908047491974249)
  ·
    refine ⟨82665335065431035618980687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110220446753908047491974249 82665335065431035618980687)
    ·
      refine ⟨123998002598146553428471031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82665335065431035618980687 123998002598146553428471031)
      ·
        refine ⟨185997003897219830142706547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 123998002598146553428471031 185997003897219830142706547)
        ·
          refine ⟨278995505845829745214059821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185997003897219830142706547 278995505845829745214059821)
          ·
            refine ⟨104623314692186154455272433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278995505845829745214059821 104623314692186154455272433)
            ·
              refine ⟨78467486019139615841454325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104623314692186154455272433 78467486019139615841454325)
              ·
                refine ⟨7356326814294338985136343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 78467486019139615841454325 7356326814294338985136343)
                ·
                  refine ⟨11034490221441508477704515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7356326814294338985136343 11034490221441508477704515)
                  ·
                    refine ⟨16551735332162262716556773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11034490221441508477704515 16551735332162262716556773)
                    ·
                      refine ⟨3103450374780424259354395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16551735332162262716556773 3103450374780424259354395)
                      ·
                        rfl

theorem cell23_6043948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 4].length) (baseStart_6043948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043948 prefixEnd_6043948 := by exact prefixLift 6043948
  have htrace : WordTrace (prefixWord ++ tailWord_6043948) baseStart_6043948 baseEnd_6043948 := by
    simpa [prefixWord, tailWord_6043948, baseEnd_6043948] using wordTrace_append hprefix tailTrace_6043948
  have hstable : (prefixWord ++ tailWord_6043948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043948).length < 2 ^ (prefixWord ++ tailWord_6043948).sum := by decide
  have hdescent : baseEnd_6043948 < baseStart_6043948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043971 : List Nat := [1, 1, 1, 3, 1, 3, 5, 8]
def baseStart_6043971 : Nat := 118140960795 + 6043971 * 2 ^ 59
def prefixEnd_6043971 : Nat := 4983230072969 + 3 ^ 40 * 6043971 * 2
def baseEnd_6043971 : Nat := 114943043882795469235807

theorem tailTrace_6043971 : CollatzResearch.WordTrace tailWord_6043971 prefixEnd_6043971 114943043882795469235807 := by
  unfold tailWord_6043971
  simp only [CollatzResearch.WordTrace]
  refine ⟨220441732386732769912035767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146961154924488513274690511 220441732386732769912035767)
  ·
    refine ⟨330662598580099154868053651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220441732386732769912035767 330662598580099154868053651)
    ·
      refine ⟨495993897870148732302080477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330662598580099154868053651 495993897870148732302080477)
      ·
        refine ⟨185997711701305774613280179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 495993897870148732302080477 185997711701305774613280179)
        ·
          refine ⟨278996567551958661919920269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 185997711701305774613280179 278996567551958661919920269)
          ·
            refine ⟨104623712831984498219970101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 278996567551958661919920269 104623712831984498219970101)
            ·
              refine ⟨9808473077998546708122197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 104623712831984498219970101 9808473077998546708122197)
              ·
                refine ⟨114943043882795469235807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9808473077998546708122197 114943043882795469235807)
                ·
                  rfl

theorem cell23_6043971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 5, 8].length) (baseStart_6043971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043971 prefixEnd_6043971 := by exact prefixLift 6043971
  have htrace : WordTrace (prefixWord ++ tailWord_6043971) baseStart_6043971 baseEnd_6043971 := by
    simpa [prefixWord, tailWord_6043971, baseEnd_6043971] using wordTrace_append hprefix tailTrace_6043971
  have hstable : (prefixWord ++ tailWord_6043971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043971).length < 2 ^ (prefixWord ++ tailWord_6043971).sum := by decide
  have hdescent : baseEnd_6043971 < baseStart_6043971 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6043996 : List Nat := [2, 2, 4, 3, 2, 1, 2, 1, 1, 5]
def baseStart_6043996 : Nat := 118140960795 + 6043996 * 2 ^ 59
def prefixEnd_6043996 : Nat := 4983230072969 + 3 ^ 40 * 6043996 * 2
def baseEnd_6043996 : Nat := 1034491673950613357184725

theorem tailTrace_6043996 : CollatzResearch.WordTrace tailWord_6043996 prefixEnd_6043996 1034491673950613357184725 := by
  unfold tailWord_6043996
  simp only [CollatzResearch.WordTrace]
  refine ⟨110221322105821099590847921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146961762807761466121130561 110221322105821099590847921)
  ·
    refine ⟨82665991579365824693135941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 110221322105821099590847921 82665991579365824693135941)
    ·
      refine ⟨15499873421131092129962989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 82665991579365824693135941 15499873421131092129962989)
      ·
        refine ⟨5812452532924159548736121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15499873421131092129962989 5812452532924159548736121)
        ·
          refine ⟨4359339399693119661552091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5812452532924159548736121 4359339399693119661552091)
          ·
            refine ⟨6539009099539679492328137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4359339399693119661552091 6539009099539679492328137)
            ·
              refine ⟨4904256824654759619246103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6539009099539679492328137 4904256824654759619246103)
              ·
                refine ⟨7356385236982139428869155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4904256824654759619246103 7356385236982139428869155)
                ·
                  refine ⟨11034577855473209143303733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7356385236982139428869155 11034577855473209143303733)
                  ·
                    refine ⟨1034491673950613357184725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11034577855473209143303733 1034491673950613357184725)
                    ·
                      rfl

theorem cell23_6043996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_6043996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6043996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6043996 prefixEnd_6043996 := by exact prefixLift 6043996
  have htrace : WordTrace (prefixWord ++ tailWord_6043996) baseStart_6043996 baseEnd_6043996 := by
    simpa [prefixWord, tailWord_6043996, baseEnd_6043996] using wordTrace_append hprefix tailTrace_6043996
  have hstable : (prefixWord ++ tailWord_6043996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6043996).length < 2 ^ (prefixWord ++ tailWord_6043996).sum := by decide
  have hdescent : baseEnd_6043996 < baseStart_6043996 := by decide
  rcases family_descends (prefixWord ++ tailWord_6043996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044002 : List Nat := [3, 3, 2, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_6044002 : Nat := 118140960795 + 6044002 * 2 ^ 59
def prefixEnd_6044002 : Nat := 4983230072969 + 3 ^ 40 * 6044002 * 2
def baseEnd_6044002 : Nat := 3103478102735767048079147

theorem tailTrace_6044002 : CollatzResearch.WordTrace tailWord_6044002 prefixEnd_6044002 3103478102735767048079147 := by
  unfold tailWord_6044002
  simp only [CollatzResearch.WordTrace]
  refine ⟨55110715762405115551603565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146961908699746974804276173 55110715762405115551603565)
  ·
    refine ⟨20666518410901918331851337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 55110715762405115551603565 20666518410901918331851337)
    ·
      refine ⟨15499888808176438748888503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20666518410901918331851337 15499888808176438748888503)
      ·
        refine ⟨23249833212264658123332755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15499888808176438748888503 23249833212264658123332755)
        ·
          refine ⟨34874749818396987184999133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23249833212264658123332755 34874749818396987184999133)
          ·
            refine ⟨13078031181898870194374675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34874749818396987184999133 13078031181898870194374675)
            ·
              refine ⟨19617046772848305291562013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13078031181898870194374675 19617046772848305291562013)
              ·
                refine ⟨7356392539818114484335755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19617046772848305291562013 7356392539818114484335755)
                ·
                  refine ⟨11034588809727171726503633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7356392539818114484335755 11034588809727171726503633)
                  ·
                    refine ⟨8275941607295378794877725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11034588809727171726503633 8275941607295378794877725)
                    ·
                      refine ⟨3103478102735767048079147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8275941607295378794877725 3103478102735767048079147)
                      ·
                        rfl

theorem cell23_6044002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_6044002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044002 prefixEnd_6044002 := by exact prefixLift 6044002
  have htrace : WordTrace (prefixWord ++ tailWord_6044002) baseStart_6044002 baseEnd_6044002 := by
    simpa [prefixWord, tailWord_6044002, baseEnd_6044002] using wordTrace_append hprefix tailTrace_6044002
  have hstable : (prefixWord ++ tailWord_6044002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044002).length < 2 ^ (prefixWord ++ tailWord_6044002).sum := by decide
  have hdescent : baseEnd_6044002 < baseStart_6044002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044011 : List Nat := [1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 5]
def baseStart_6044011 : Nat := 118140960795 + 6044011 * 2 ^ 59
def prefixEnd_6044011 : Nat := 4983230072969 + 3 ^ 40 * 6044011 * 2
def baseEnd_6044011 : Nat := 3103482724061657512866605

theorem tailTrace_6044011 : CollatzResearch.WordTrace tailWord_6044011 prefixEnd_6044011 3103482724061657512866605 := by
  unfold tailWord_6044011
  simp only [CollatzResearch.WordTrace]
  refine ⟨220443191306587856743491887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146962127537725237828994591 220443191306587856743491887)
  ·
    refine ⟨330664786959881785115237831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220443191306587856743491887 330664786959881785115237831)
    ·
      refine ⟨495997180439822677672856747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 330664786959881785115237831 495997180439822677672856747)
      ·
        refine ⟨743995770659734016509285121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 495997180439822677672856747 743995770659734016509285121)
        ·
          refine ⟨557996827994800512381963841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 743995770659734016509285121 557996827994800512381963841)
          ·
            refine ⟨418497620996100384286472881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 557996827994800512381963841 418497620996100384286472881)
            ·
              refine ⟨313873215747075288214854661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 418497620996100384286472881 313873215747075288214854661)
              ·
                refine ⟨58851227952576616540285249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 313873215747075288214854661 58851227952576616540285249)
                ·
                  refine ⟨44138420964432462405213937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 58851227952576616540285249 44138420964432462405213937)
                  ·
                    refine ⟨33103815723324346803910453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 44138420964432462405213937 33103815723324346803910453)
                    ·
                      refine ⟨3103482724061657512866605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33103815723324346803910453 3103482724061657512866605)
                      ·
                        rfl

theorem cell23_6044011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 2, 5].length) (baseStart_6044011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044011 prefixEnd_6044011 := by exact prefixLift 6044011
  have htrace : WordTrace (prefixWord ++ tailWord_6044011) baseStart_6044011 baseEnd_6044011 := by
    simpa [prefixWord, tailWord_6044011, baseEnd_6044011] using wordTrace_append hprefix tailTrace_6044011
  have hstable : (prefixWord ++ tailWord_6044011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044011).length < 2 ^ (prefixWord ++ tailWord_6044011).sum := by decide
  have hdescent : baseEnd_6044011 < baseStart_6044011 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044015 : List Nat := [1, 1, 2, 1, 3, 1, 2, 6, 2, 1, 3]
def baseStart_6044015 : Nat := 118140960795 + 6044015 * 2 ^ 59
def prefixEnd_6044015 : Nat := 4983230072969 + 3 ^ 40 * 6044015 * 2
def baseEnd_6044015 : Nat := 3103484777984275497216587

theorem tailTrace_6044015 : CollatzResearch.WordTrace tailWord_6044015 prefixEnd_6044015 3103484777984275497216587 := by
  unfold tailWord_6044015
  simp only [CollatzResearch.WordTrace]
  refine ⟨220443337198573365426637499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146962224799048910284424999 220443337198573365426637499)
  ·
    refine ⟨330665005797860048139956249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220443337198573365426637499 330665005797860048139956249)
    ·
      refine ⟨247998754348395036104967187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 330665005797860048139956249 247998754348395036104967187)
      ·
        refine ⟨371998131522592554157450781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 247998754348395036104967187 371998131522592554157450781)
        ·
          refine ⟨139499299320972207809044043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 371998131522592554157450781 139499299320972207809044043)
          ·
            refine ⟨209248948981458311713566065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 139499299320972207809044043 209248948981458311713566065)
            ·
              refine ⟨156936711736093733785174549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 209248948981458311713566065 156936711736093733785174549)
              ·
                refine ⟨7356408362629393771180057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 156936711736093733785174549 7356408362629393771180057)
                ·
                  refine ⟨5517306271972045328385043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7356408362629393771180057 5517306271972045328385043)
                  ·
                    refine ⟨8275959407958067992577565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5517306271972045328385043 8275959407958067992577565)
                    ·
                      refine ⟨3103484777984275497216587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8275959407958067992577565 3103484777984275497216587)
                      ·
                        rfl

theorem cell23_6044015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 6, 2, 1, 3].length) (baseStart_6044015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044015 prefixEnd_6044015 := by exact prefixLift 6044015
  have htrace : WordTrace (prefixWord ++ tailWord_6044015) baseStart_6044015 baseEnd_6044015 := by
    simpa [prefixWord, tailWord_6044015, baseEnd_6044015] using wordTrace_append hprefix tailTrace_6044015
  have hstable : (prefixWord ++ tailWord_6044015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044015).length < 2 ^ (prefixWord ++ tailWord_6044015).sum := by decide
  have hdescent : baseEnd_6044015 < baseStart_6044015 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044055 : List Nat := [1, 1, 3, 3, 1, 1, 2, 4, 1, 4, 2]
def baseStart_6044055 : Nat := 118140960795 + 6044055 * 2 ^ 59
def prefixEnd_6044055 : Nat := 4983230072969 + 3 ^ 40 * 6044055 * 2
def baseEnd_6044055 : Nat := 3103505317210455340716403

theorem tailTrace_6044055 : CollatzResearch.WordTrace tailWord_6044055 prefixEnd_6044055 3103505317210455340716403 := by
  unfold tailWord_6044055
  simp only [CollatzResearch.WordTrace]
  refine ⟨220444796118428452258093619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146963197412285634838729079 220444796118428452258093619)
  ·
    refine ⟨330667194177642678387140429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 220444796118428452258093619 330667194177642678387140429)
    ·
      refine ⟨124000197816616004395177661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 330667194177642678387140429 124000197816616004395177661)
      ·
        refine ⟨46500074181231001648191623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 124000197816616004395177661 46500074181231001648191623)
        ·
          refine ⟨69750111271846502472287435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46500074181231001648191623 69750111271846502472287435)
          ·
            refine ⟨104625166907769753708431153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69750111271846502472287435 104625166907769753708431153)
            ·
              refine ⟨78468875180827315281323365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104625166907769753708431153 78468875180827315281323365)
              ·
                refine ⟨14712914096405121615248131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78468875180827315281323365 14712914096405121615248131)
                ·
                  refine ⟨22069371144607682422872197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14712914096405121615248131 22069371144607682422872197)
                  ·
                    refine ⟨4138007089613940454288537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22069371144607682422872197 4138007089613940454288537)
                    ·
                      refine ⟨3103505317210455340716403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4138007089613940454288537 3103505317210455340716403)
                      ·
                        rfl

theorem cell23_6044055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 4, 1, 4, 2].length) (baseStart_6044055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044055 prefixEnd_6044055 := by exact prefixLift 6044055
  have htrace : WordTrace (prefixWord ++ tailWord_6044055) baseStart_6044055 baseEnd_6044055 := by
    simpa [prefixWord, tailWord_6044055, baseEnd_6044055] using wordTrace_append hprefix tailTrace_6044055
  have hstable : (prefixWord ++ tailWord_6044055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044055).length < 2 ^ (prefixWord ++ tailWord_6044055).sum := by decide
  have hdescent : baseEnd_6044055 < baseStart_6044055 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044058 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5]
def baseStart_6044058 : Nat := 118140960795 + 6044058 * 2 ^ 59
def prefixEnd_6044058 : Nat := 4983230072969 + 3 ^ 40 * 6044058 * 2
def baseEnd_6044058 : Nat := 3103506857652418828978889

theorem tailTrace_6044058 : CollatzResearch.WordTrace tailWord_6044058 prefixEnd_6044058 3103506857652418828978889 := by
  unfold tailWord_6044058
  simp only [CollatzResearch.WordTrace]
  refine ⟨55111226384354395942613207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 146963270358278389180301885 55111226384354395942613207)
  ·
    refine ⟨82666839576531593913919811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 55111226384354395942613207 82666839576531593913919811)
    ·
      refine ⟨124000259364797390870879717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82666839576531593913919811 124000259364797390870879717)
      ·
        refine ⟨23250048630899510788289947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 124000259364797390870879717 23250048630899510788289947)
        ·
          refine ⟨34875072946349266182434921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23250048630899510788289947 34875072946349266182434921)
          ·
            refine ⟨26156304709761949636826191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34875072946349266182434921 26156304709761949636826191)
            ·
              refine ⟨39234457064642924455239287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 26156304709761949636826191 39234457064642924455239287)
              ·
                refine ⟨58851685596964386682858931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 39234457064642924455239287 58851685596964386682858931)
                ·
                  refine ⟨88277528395446580024288397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58851685596964386682858931 88277528395446580024288397)
                  ·
                    refine ⟨33104073148292467509108149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 88277528395446580024288397 33104073148292467509108149)
                    ·
                      refine ⟨3103506857652418828978889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 33104073148292467509108149 3103506857652418828978889)
                      ·
                        rfl

theorem cell23_6044058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_6044058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044058 prefixEnd_6044058 := by exact prefixLift 6044058
  have htrace : WordTrace (prefixWord ++ tailWord_6044058) baseStart_6044058 baseEnd_6044058 := by
    simpa [prefixWord, tailWord_6044058, baseEnd_6044058] using wordTrace_append hprefix tailTrace_6044058
  have hstable : (prefixWord ++ tailWord_6044058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044058).length < 2 ^ (prefixWord ++ tailWord_6044058).sum := by decide
  have hdescent : baseEnd_6044058 < baseStart_6044058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044068 : List Nat := [2, 3, 1, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_6044068 : Nat := 118140960795 + 6044068 * 2 ^ 59
def prefixEnd_6044068 : Nat := 4983230072969 + 3 ^ 40 * 6044068 * 2
def baseEnd_6044068 : Nat := 3103511992458963789853843

theorem tailTrace_6044068 : CollatzResearch.WordTrace tailWord_6044068 prefixEnd_6044068 3103511992458963789853843 := by
  unfold tailWord_6044068
  simp only [CollatzResearch.WordTrace]
  refine ⟨110222635133690677739158429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146963513511587570318877905 110222635133690677739158429)
  ·
    refine ⟨41333488175134004152184411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 110222635133690677739158429 41333488175134004152184411)
    ·
      refine ⟨62000232262701006228276617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41333488175134004152184411 62000232262701006228276617)
      ·
        refine ⟨46500174197025754671207463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62000232262701006228276617 46500174197025754671207463)
        ·
          refine ⟨69750261295538632006811195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46500174197025754671207463 69750261295538632006811195)
          ·
            refine ⟨104625391943307948010216793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69750261295538632006811195 104625391943307948010216793)
            ·
              refine ⟨78469043957480961007662595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104625391943307948010216793 78469043957480961007662595)
              ·
                refine ⟨117703565936221441511493893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78469043957480961007662595 117703565936221441511493893)
                ·
                  refine ⟨22069418613041520283405105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 117703565936221441511493893 22069418613041520283405105)
                  ·
                    refine ⟨16552063959781140212553829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22069418613041520283405105 16552063959781140212553829)
                    ·
                      refine ⟨3103511992458963789853843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16552063959781140212553829 3103511992458963789853843)
                      ·
                        rfl

theorem cell23_6044068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_6044068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044068 prefixEnd_6044068 := by exact prefixLift 6044068
  have htrace : WordTrace (prefixWord ++ tailWord_6044068) baseStart_6044068 baseEnd_6044068 := by
    simpa [prefixWord, tailWord_6044068, baseEnd_6044068] using wordTrace_append hprefix tailTrace_6044068
  have hstable : (prefixWord ++ tailWord_6044068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044068).length < 2 ^ (prefixWord ++ tailWord_6044068).sum := by decide
  have hdescent : baseEnd_6044068 < baseStart_6044068 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044088 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 1, 5, 3]
def baseStart_6044088 : Nat := 118140960795 + 6044088 * 2 ^ 59
def prefixEnd_6044088 : Nat := 4983230072969 + 3 ^ 40 * 6044088 * 2
def baseEnd_6044088 : Nat := 3103522262072053711603751

theorem tailTrace_6044088 : CollatzResearch.WordTrace tailWord_6044088 prefixEnd_6044088 3103522262072053711603751 := by
  unfold tailWord_6044088
  simp only [CollatzResearch.WordTrace]
  refine ⟨110222999863654449447022459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146963999818205932596029945 110222999863654449447022459)
  ·
    refine ⟨165334499795481674170533689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110222999863654449447022459 165334499795481674170533689)
    ·
      refine ⟨124000874846611255627900267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 165334499795481674170533689 124000874846611255627900267)
      ·
        refine ⟨186001312269916883441850401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 124000874846611255627900267 186001312269916883441850401)
        ·
          refine ⟨139500984202437662581387801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 186001312269916883441850401 139500984202437662581387801)
          ·
            refine ⟨104625738151828246936040851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139500984202437662581387801 104625738151828246936040851)
            ·
              refine ⟨156938607227742370404061277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104625738151828246936040851 156938607227742370404061277)
              ·
                refine ⟨58851977710403388901522979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 156938607227742370404061277 58851977710403388901522979)
                ·
                  refine ⟨88277966565605083352284469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 58851977710403388901522979 88277966565605083352284469)
                  ·
                    refine ⟨8276059365525476564276669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 88277966565605083352284469 8276059365525476564276669)
                    ·
                      refine ⟨3103522262072053711603751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8276059365525476564276669 3103522262072053711603751)
                      ·
                        rfl

theorem cell23_6044088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_6044088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044088 prefixEnd_6044088 := by exact prefixLift 6044088
  have htrace : WordTrace (prefixWord ++ tailWord_6044088) baseStart_6044088 baseEnd_6044088 := by
    simpa [prefixWord, tailWord_6044088, baseEnd_6044088] using wordTrace_append hprefix tailTrace_6044088
  have hstable : (prefixWord ++ tailWord_6044088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044088).length < 2 ^ (prefixWord ++ tailWord_6044088).sum := by decide
  have hdescent : baseEnd_6044088 < baseStart_6044088 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044089 : List Nat := [1, 2, 1, 4, 3, 2, 1, 3, 2, 2, 2]
def baseStart_6044089 : Nat := 118140960795 + 6044089 * 2 ^ 59
def prefixEnd_6044089 : Nat := 4983230072969 + 3 ^ 40 * 6044089 * 2
def baseEnd_6044089 : Nat := 3103522775552708207691247

theorem tailTrace_6044089 : CollatzResearch.WordTrace tailWord_6044089 prefixEnd_6044089 3103522775552708207691247 := by
  unfold tailWord_6044089
  simp only [CollatzResearch.WordTrace]
  refine ⟨220446036200305276064831321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146964024133536850709887547 220446036200305276064831321)
  ·
    refine ⟨165334527150228957048623491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220446036200305276064831321 165334527150228957048623491)
    ·
      refine ⟨248001790725343435572935237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165334527150228957048623491 248001790725343435572935237)
      ·
        refine ⟨46500335761001894169925357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 248001790725343435572935237 46500335761001894169925357)
        ·
          refine ⟨17437625910375710313722009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46500335761001894169925357 17437625910375710313722009)
          ·
            refine ⟨13078219432781782735291507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17437625910375710313722009 13078219432781782735291507)
            ·
              refine ⟨19617329149172674102937261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13078219432781782735291507 19617329149172674102937261)
              ·
                refine ⟨7356498430939752788601473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19617329149172674102937261 7356498430939752788601473)
                ·
                  refine ⟨5517373823204814591451105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7356498430939752788601473 5517373823204814591451105)
                  ·
                    refine ⟨4138030367403610943588329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5517373823204814591451105 4138030367403610943588329)
                    ·
                      refine ⟨3103522775552708207691247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4138030367403610943588329 3103522775552708207691247)
                      ·
                        rfl

theorem cell23_6044089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_6044089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044089 prefixEnd_6044089 := by exact prefixLift 6044089
  have htrace : WordTrace (prefixWord ++ tailWord_6044089) baseStart_6044089 baseEnd_6044089 := by
    simpa [prefixWord, tailWord_6044089, baseEnd_6044089] using wordTrace_append hprefix tailTrace_6044089
  have hstable : (prefixWord ++ tailWord_6044089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044089).length < 2 ^ (prefixWord ++ tailWord_6044089).sum := by decide
  have hdescent : baseEnd_6044089 < baseStart_6044089 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044125 : List Nat := [1, 4, 3, 1, 1, 1, 1, 4, 2, 5]
def baseStart_6044125 : Nat := 118140960795 + 6044125 * 2 ^ 59
def prefixEnd_6044125 : Nat := 4983230072969 + 3 ^ 40 * 6044125 * 2
def baseEnd_6044125 : Nat := 1034513753618756688947027

theorem tailTrace_6044125 : CollatzResearch.WordTrace tailWord_6044125 prefixEnd_6044125 1034513753618756688947027 := by
  unfold tailWord_6044125
  simp only [CollatzResearch.WordTrace]
  refine ⟨220447349228174854213141829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146964899485449902808761219 220447349228174854213141829)
  ·
    refine ⟨41333877980282785164964093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220447349228174854213141829 41333877980282785164964093)
    ·
      refine ⟨15500204242606044436861535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 41333877980282785164964093 15500204242606044436861535)
      ·
        refine ⟨23250306363909066655292303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15500204242606044436861535 23250306363909066655292303)
        ·
          refine ⟨34875459545863599982938455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23250306363909066655292303 34875459545863599982938455)
          ·
            refine ⟨52313189318795399974407683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34875459545863599982938455 52313189318795399974407683)
            ·
              refine ⟨78469783978193099961611525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52313189318795399974407683 78469783978193099961611525)
              ·
                refine ⟨14713084495911206242802161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 78469783978193099961611525 14713084495911206242802161)
                ·
                  refine ⟨11034813371933404682101621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14713084495911206242802161 11034813371933404682101621)
                  ·
                    refine ⟨1034513753618756688947027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11034813371933404682101621 1034513753618756688947027)
                    ·
                      rfl

theorem cell23_6044125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_6044125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044125 prefixEnd_6044125 := by exact prefixLift 6044125
  have htrace : WordTrace (prefixWord ++ tailWord_6044125) baseStart_6044125 baseEnd_6044125 := by
    simpa [prefixWord, tailWord_6044125, baseEnd_6044125] using wordTrace_append hprefix tailTrace_6044125
  have hstable : (prefixWord ++ tailWord_6044125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044125).length < 2 ^ (prefixWord ++ tailWord_6044125).sum := by decide
  have hdescent : baseEnd_6044125 < baseStart_6044125 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044168 : List Nat := [2, 1, 3, 2, 1, 1, 1, 4, 8]
def baseStart_6044168 : Nat := 118140960795 + 6044168 * 2 ^ 59
def prefixEnd_6044168 : Nat := 4983230072969 + 3 ^ 40 * 6044168 * 2
def baseEnd_6044168 : Nat := 344840371169379266511487

theorem tailTrace_6044168 : CollatzResearch.WordTrace tailWord_6044168 prefixEnd_6044168 344840371169379266511487 := by
  unfold tailWord_6044168
  simp only [CollatzResearch.WordTrace]
  refine ⟨110224458783509536278478579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146965945044679381704638105 110224458783509536278478579)
  ·
    refine ⟨165336688175264304417717869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110224458783509536278478579 165336688175264304417717869)
    ·
      refine ⟨62001258065724114156644201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 165336688175264304417717869 62001258065724114156644201)
      ·
        refine ⟨46500943549293085617483151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 62001258065724114156644201 46500943549293085617483151)
        ·
          refine ⟨69751415323939628426224727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 46500943549293085617483151 69751415323939628426224727)
          ·
            refine ⟨104627122985909442639337091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 69751415323939628426224727 104627122985909442639337091)
            ·
              refine ⟨156940684478864163959005637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104627122985909442639337091 156940684478864163959005637)
              ·
                refine ⟨29426378339787030742313557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 156940684478864163959005637 29426378339787030742313557)
                ·
                  refine ⟨344840371169379266511487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 29426378339787030742313557 344840371169379266511487)
                  ·
                    rfl

theorem cell23_6044168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 4, 8].length) (baseStart_6044168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044168 prefixEnd_6044168 := by exact prefixLift 6044168
  have htrace : WordTrace (prefixWord ++ tailWord_6044168) baseStart_6044168 baseEnd_6044168 := by
    simpa [prefixWord, tailWord_6044168, baseEnd_6044168] using wordTrace_append hprefix tailTrace_6044168
  have hstable : (prefixWord ++ tailWord_6044168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044168).length < 2 ^ (prefixWord ++ tailWord_6044168).sum := by decide
  have hdescent : baseEnd_6044168 < baseStart_6044168 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044189 : List Nat := [1, 4, 2, 2, 1, 2, 2, 4, 1, 4]
def baseStart_6044189 : Nat := 118140960795 + 6044189 * 2 ^ 59
def prefixEnd_6044189 : Nat := 4983230072969 + 3 ^ 40 * 6044189 * 2
def baseEnd_6044189 : Nat := 1034524707872719272146929

theorem tailTrace_6044189 : CollatzResearch.WordTrace tailWord_6044189 prefixEnd_6044189 1034524707872719272146929 := by
  unfold tailWord_6044189
  simp only [CollatzResearch.WordTrace]
  refine ⟨220449683499942993143471621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146966455666628662095647747 220449683499942993143471621)
  ·
    refine ⟨41334315656239311214400929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 220449683499942993143471621 41334315656239311214400929)
    ·
      refine ⟨31000736742179483410800697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 41334315656239311214400929 31000736742179483410800697)
      ·
        refine ⟨23250552556634612558100523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31000736742179483410800697 23250552556634612558100523)
        ·
          refine ⟨34875828834951918837150785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23250552556634612558100523 34875828834951918837150785)
          ·
            refine ⟨26156871626213939127863089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34875828834951918837150785 26156871626213939127863089)
            ·
              refine ⟨19617653719660454345897317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 26156871626213939127863089 19617653719660454345897317)
              ·
                refine ⟨3678310072436335189855747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19617653719660454345897317 3678310072436335189855747)
                ·
                  refine ⟨5517465108654502784783621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3678310072436335189855747 5517465108654502784783621)
                  ·
                    refine ⟨1034524707872719272146929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5517465108654502784783621 1034524707872719272146929)
                    ·
                      rfl

theorem cell23_6044189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_6044189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044189 prefixEnd_6044189 := by exact prefixLift 6044189
  have htrace : WordTrace (prefixWord ++ tailWord_6044189) baseStart_6044189 baseEnd_6044189 := by
    simpa [prefixWord, tailWord_6044189, baseEnd_6044189] using wordTrace_append hprefix tailTrace_6044189
  have hstable : (prefixWord ++ tailWord_6044189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044189).length < 2 ^ (prefixWord ++ tailWord_6044189).sum := by decide
  have hdescent : baseEnd_6044189 < baseStart_6044189 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044208 : List Nat := [2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 7]
def baseStart_6044208 : Nat := 118140960795 + 6044208 * 2 ^ 59
def prefixEnd_6044208 : Nat := 4983230072969 + 3 ^ 40 * 6044208 * 2
def baseEnd_6044208 : Nat := 3103583879750593242103199

theorem tailTrace_6044208 : CollatzResearch.WordTrace tailWord_6044208 prefixEnd_6044208 3103583879750593242103199 := by
  unfold tailWord_6044208
  simp only [CollatzResearch.WordTrace]
  refine ⟨110225188243437079694206639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 146966917657916106258942185 110225188243437079694206639)
  ·
    refine ⟨165337782365155619541309959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 110225188243437079694206639 165337782365155619541309959)
    ·
      refine ⟨248006673547733429311964939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165337782365155619541309959 248006673547733429311964939)
      ·
        refine ⟨372010010321600143967947409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248006673547733429311964939 372010010321600143967947409)
        ·
          refine ⟨279007507741200107975960557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 372010010321600143967947409 279007507741200107975960557)
          ·
            refine ⟨104627815402950040490985209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 279007507741200107975960557 104627815402950040490985209)
            ·
              refine ⟨78470861552212530368238907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 104627815402950040490985209 78470861552212530368238907)
              ·
                refine ⟨117706292328318795552358361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 78470861552212530368238907 117706292328318795552358361)
                ·
                  refine ⟨88279719246239096664268771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 117706292328318795552358361 88279719246239096664268771)
                  ·
                    refine ⟨132419578869358644996403157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 88279719246239096664268771 132419578869358644996403157)
                    ·
                      refine ⟨3103583879750593242103199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 132419578869358644996403157 3103583879750593242103199)
                      ·
                        rfl

theorem cell23_6044208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_6044208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044208 prefixEnd_6044208 := by exact prefixLift 6044208
  have htrace : WordTrace (prefixWord ++ tailWord_6044208) baseStart_6044208 baseEnd_6044208 := by
    simpa [prefixWord, tailWord_6044208, baseEnd_6044208] using wordTrace_append hprefix tailTrace_6044208
  have hstable : (prefixWord ++ tailWord_6044208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044208).length < 2 ^ (prefixWord ++ tailWord_6044208).sum := by decide
  have hdescent : baseEnd_6044208 < baseStart_6044208 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044265 : List Nat := [1, 2, 1, 1, 1, 4, 1, 5, 1, 2, 4]
def baseStart_6044265 : Nat := 118140960795 + 6044265 * 2 ^ 59
def prefixEnd_6044265 : Nat := 4983230072969 + 3 ^ 40 * 6044265 * 2
def baseEnd_6044265 : Nat := 3103613148147899519090437

theorem tailTrace_6044265 : CollatzResearch.WordTrace tailWord_6044265 prefixEnd_6044265 3103613148147899519090437 := by
  unfold tailWord_6044265
  simp only [CollatzResearch.WordTrace]
  refine ⟨220452455447667658123238249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146968303631778438748825499 220452455447667658123238249)
  ·
    refine ⟨165339341585750743592428687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 220452455447667658123238249 165339341585750743592428687)
    ·
      refine ⟨248009012378626115388643031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 165339341585750743592428687 248009012378626115388643031)
      ·
        refine ⟨372013518567939173082964547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 248009012378626115388643031 372013518567939173082964547)
        ·
          refine ⟨558020277851908759624446821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 372013518567939173082964547 558020277851908759624446821)
          ·
            refine ⟨104628802097232892429583779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 558020277851908759624446821 104628802097232892429583779)
            ·
              refine ⟨156943203145849338644375669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104628802097232892429583779 156943203145849338644375669)
              ·
                refine ⟨14713425294923375497910219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 156943203145849338644375669 14713425294923375497910219)
                ·
                  refine ⟨22070137942385063246865329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14713425294923375497910219 22070137942385063246865329)
                  ·
                    refine ⟨16552603456788797435148997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22070137942385063246865329 16552603456788797435148997)
                    ·
                      refine ⟨3103613148147899519090437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16552603456788797435148997 3103613148147899519090437)
                      ·
                        rfl

theorem cell23_6044265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 5, 1, 2, 4].length) (baseStart_6044265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044265 prefixEnd_6044265 := by exact prefixLift 6044265
  have htrace : WordTrace (prefixWord ++ tailWord_6044265) baseStart_6044265 baseEnd_6044265 := by
    simpa [prefixWord, tailWord_6044265, baseEnd_6044265] using wordTrace_append hprefix tailTrace_6044265
  have hstable : (prefixWord ++ tailWord_6044265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044265).length < 2 ^ (prefixWord ++ tailWord_6044265).sum := by decide
  have hdescent : baseEnd_6044265 < baseStart_6044265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044269 : List Nat := [1, 5, 1, 1, 3, 1, 3, 2, 1, 1, 4]
def baseStart_6044269 : Nat := 118140960795 + 6044269 * 2 ^ 59
def prefixEnd_6044269 : Nat := 4983230072969 + 3 ^ 40 * 6044269 * 2
def baseEnd_6044269 : Nat := 3103615202070517503440419

theorem tailTrace_6044269 : CollatzResearch.WordTrace tailWord_6044269 prefixEnd_6044269 3103615202070517503440419 := by
  unfold tailWord_6044269
  simp only [CollatzResearch.WordTrace]
  refine ⟨220452601339653166806383861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146968400893102111204255907 220452601339653166806383861)
  ·
    refine ⟨20667431375592484388098487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 220452601339653166806383861 20667431375592484388098487)
    ·
      refine ⟨31001147063388726582147731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20667431375592484388098487 31001147063388726582147731)
      ·
        refine ⟨46501720595083089873221597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 31001147063388726582147731 46501720595083089873221597)
        ·
          refine ⟨17438145223156158702458099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 46501720595083089873221597 17438145223156158702458099)
          ·
            refine ⟨26157217834734238053687149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17438145223156158702458099 26157217834734238053687149)
            ·
              refine ⟨9808956688025339270132681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 26157217834734238053687149 9808956688025339270132681)
              ·
                refine ⟨7356717516019004452599511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9808956688025339270132681 7356717516019004452599511)
                ·
                  refine ⟨11035076274028506678899267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7356717516019004452599511 11035076274028506678899267)
                  ·
                    refine ⟨16552614411042760018348901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11035076274028506678899267 16552614411042760018348901)
                    ·
                      refine ⟨3103615202070517503440419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16552614411042760018348901 3103615202070517503440419)
                      ·
                        rfl

theorem cell23_6044269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_6044269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044269 prefixEnd_6044269 := by exact prefixLift 6044269
  have htrace : WordTrace (prefixWord ++ tailWord_6044269) baseStart_6044269 baseEnd_6044269 := by
    simpa [prefixWord, tailWord_6044269, baseEnd_6044269] using wordTrace_append hprefix tailTrace_6044269
  have hstable : (prefixWord ++ tailWord_6044269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044269).length < 2 ^ (prefixWord ++ tailWord_6044269).sum := by decide
  have hdescent : baseEnd_6044269 < baseStart_6044269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044302 : List Nat := [4, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3]
def baseStart_6044302 : Nat := 118140960795 + 6044302 * 2 ^ 59
def prefixEnd_6044302 : Nat := 4983230072969 + 3 ^ 40 * 6044302 * 2
def baseEnd_6044302 : Nat := 3103632146932115874327767

theorem tailTrace_6044302 : CollatzResearch.WordTrace tailWord_6044302 prefixEnd_6044302 3103632146932115874327767 := by
  unfold tailWord_6044302
  simp only [CollatzResearch.WordTrace]
  refine ⟨27556725618566701680291895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 146969203299022408961556773 27556725618566701680291895)
  ·
    refine ⟨41335088427850052520437843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27556725618566701680291895 41335088427850052520437843)
    ·
      refine ⟨62002632641775078780656765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 41335088427850052520437843 62002632641775078780656765)
      ·
        refine ⟨23250987240665654542746287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 62002632641775078780656765 23250987240665654542746287)
        ·
          refine ⟨34876480860998481814119431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23250987240665654542746287 34876480860998481814119431)
          ·
            refine ⟨52314721291497722721179147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34876480860998481814119431 52314721291497722721179147)
            ·
              refine ⟨78472081937246584081768721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 52314721291497722721179147 78472081937246584081768721)
              ·
                refine ⟨58854061452934938061326541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 78472081937246584081768721 58854061452934938061326541)
                ·
                  refine ⟨22070273044850601772997453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 58854061452934938061326541 22070273044850601772997453)
                  ·
                    refine ⟨8276352391818975664874045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22070273044850601772997453 8276352391818975664874045)
                    ·
                      refine ⟨3103632146932115874327767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8276352391818975664874045 3103632146932115874327767)
                      ·
                        rfl

theorem cell23_6044302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_6044302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044302 prefixEnd_6044302 := by exact prefixLift 6044302
  have htrace : WordTrace (prefixWord ++ tailWord_6044302) baseStart_6044302 baseEnd_6044302 := by
    simpa [prefixWord, tailWord_6044302, baseEnd_6044302] using wordTrace_append hprefix tailTrace_6044302
  have hstable : (prefixWord ++ tailWord_6044302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044302).length < 2 ^ (prefixWord ++ tailWord_6044302).sum := by decide
  have hdescent : baseEnd_6044302 < baseStart_6044302 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6044325 : List Nat := [1, 3, 1, 2, 1, 2, 1, 1, 4, 3, 4]
def baseStart_6044325 : Nat := 118140960795 + 6044325 * 2 ^ 59
def prefixEnd_6044325 : Nat := 4983230072969 + 3 ^ 40 * 6044325 * 2
def baseEnd_6044325 : Nat := 3103643956987169284340161

theorem tailTrace_6044325 : CollatzResearch.WordTrace tailWord_6044325 prefixEnd_6044325 3103643956987169284340161 := by
  unfold tailWord_6044325
  simp only [CollatzResearch.WordTrace]
  refine ⟨220454643827450288370422429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 146969762551633525580281619 220454643827450288370422429)
  ·
    refine ⟨82670491435293858138908411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 220454643827450288370422429 82670491435293858138908411)
    ·
      refine ⟨124005737152940787208362617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 82670491435293858138908411 124005737152940787208362617)
      ·
        refine ⟨93004302864705590406271963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 124005737152940787208362617 93004302864705590406271963)
        ·
          refine ⟨139506454297058385609407945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 93004302864705590406271963 139506454297058385609407945)
          ·
            refine ⟨104629840722793789207055959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 139506454297058385609407945 104629840722793789207055959)
            ·
              refine ⟨156944761084190683810583939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 104629840722793789207055959 156944761084190683810583939)
              ·
                refine ⟨235417141626286025715875909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 156944761084190683810583939 235417141626286025715875909)
                ·
                  refine ⟨44140714054928629821726733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 235417141626286025715875909 44140714054928629821726733)
                  ·
                    refine ⟨16552767770598236183147525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 44140714054928629821726733 16552767770598236183147525)
                    ·
                      refine ⟨3103643956987169284340161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16552767770598236183147525 3103643956987169284340161)
                      ·
                        rfl

theorem cell23_6044325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_6044325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6044325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6044325 prefixEnd_6044325 := by exact prefixLift 6044325
  have htrace : WordTrace (prefixWord ++ tailWord_6044325) baseStart_6044325 baseEnd_6044325 := by
    simpa [prefixWord, tailWord_6044325, baseEnd_6044325] using wordTrace_append hprefix tailTrace_6044325
  have hstable : (prefixWord ++ tailWord_6044325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6044325).length < 2 ^ (prefixWord ++ tailWord_6044325).sum := by decide
  have hdescent : baseEnd_6044325 < baseStart_6044325 := by decide
  rcases family_descends (prefixWord ++ tailWord_6044325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
