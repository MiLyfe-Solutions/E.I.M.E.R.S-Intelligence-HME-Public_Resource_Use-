import V185TrunkScan23Chunk0902

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5344642 : List Nat := [3, 4, 2, 1, 1, 2, 1, 2, 7]
def baseStart_5344642 : Nat := 118140960795 + 5344642 * 2 ^ 59
def prefixEnd_5344642 : Nat := 4983230072969 + 3 ^ 40 * 5344642 * 2
def baseEnd_5344642 : Nat := 304930030245264810810605

theorem tailTrace_5344642 : CollatzResearch.WordTrace tailWord_5344642 prefixEnd_5344642 304930030245264810810605 := by
  unfold tailWord_5344642
  simp only [CollatzResearch.WordTrace]
  refine ⟨48733777075820575256903045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129956738868854867351741453 48733777075820575256903045)
  ·
    refine ⟨9137583201716357860669321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48733777075820575256903045 9137583201716357860669321)
    ·
      refine ⟨6853187401287268395501991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9137583201716357860669321 6853187401287268395501991)
      ·
        refine ⟨10279781101930902593252987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6853187401287268395501991 10279781101930902593252987)
        ·
          refine ⟨15419671652896353889879481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10279781101930902593252987 15419671652896353889879481)
          ·
            refine ⟨11564753739672265417409611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15419671652896353889879481 11564753739672265417409611)
            ·
              refine ⟨17347130609508398126114417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11564753739672265417409611 17347130609508398126114417)
              ·
                refine ⟨13010347957131298594585813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17347130609508398126114417 13010347957131298594585813)
                ·
                  refine ⟨304930030245264810810605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13010347957131298594585813 304930030245264810810605)
                  ·
                    rfl

theorem cell23_5344642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_5344642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344642 prefixEnd_5344642 := by exact prefixLift 5344642
  have htrace : WordTrace (prefixWord ++ tailWord_5344642) baseStart_5344642 baseEnd_5344642 := by
    simpa [prefixWord, tailWord_5344642, baseEnd_5344642] using wordTrace_append hprefix tailTrace_5344642
  have hstable : (prefixWord ++ tailWord_5344642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344642).length < 2 ^ (prefixWord ++ tailWord_5344642).sum := by decide
  have hdescent : baseEnd_5344642 < baseStart_5344642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344670 : List Nat := [4, 3, 1, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_5344670 : Nat := 118140960795 + 5344670 * 2 ^ 59
def prefixEnd_5344670 : Nat := 4983230072969 + 3 ^ 40 * 5344670 * 2
def baseEnd_5344670 : Nat := 2744384649665709187745317

theorem tailTrace_5344670 : CollatzResearch.WordTrace tailWord_5344670 prefixEnd_5344670 2744384649665709187745317 := by
  unfold tailWord_5344670
  simp only [CollatzResearch.WordTrace]
  refine ⟨24367016193397607726203933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129957419698120574539754309 24367016193397607726203933)
  ·
    refine ⟨9137631072524102897326475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24367016193397607726203933 9137631072524102897326475)
    ·
      refine ⟨13706446608786154345989713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9137631072524102897326475 13706446608786154345989713)
      ·
        refine ⟨10279834956589615759492285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13706446608786154345989713 10279834956589615759492285)
        ·
          refine ⟨3854938108721105909809607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10279834956589615759492285 3854938108721105909809607)
          ·
            refine ⟨5782407163081658864714411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3854938108721105909809607 5782407163081658864714411)
            ·
              refine ⟨8673610744622488297071617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5782407163081658864714411 8673610744622488297071617)
              ·
                refine ⟨6505208058466866222803713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8673610744622488297071617 6505208058466866222803713)
                ·
                  refine ⟨4878906043850149667102785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6505208058466866222803713 4878906043850149667102785)
                  ·
                    refine ⟨3659179532887612250327089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4878906043850149667102785 3659179532887612250327089)
                    ·
                      refine ⟨2744384649665709187745317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659179532887612250327089 2744384649665709187745317)
                      ·
                        rfl

theorem cell23_5344670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_5344670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344670 prefixEnd_5344670 := by exact prefixLift 5344670
  have htrace : WordTrace (prefixWord ++ tailWord_5344670) baseStart_5344670 baseEnd_5344670 := by
    simpa [prefixWord, tailWord_5344670, baseEnd_5344670] using wordTrace_append hprefix tailTrace_5344670
  have hstable : (prefixWord ++ tailWord_5344670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344670).length < 2 ^ (prefixWord ++ tailWord_5344670).sum := by decide
  have hdescent : baseEnd_5344670 < baseStart_5344670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344675 : List Nat := [1, 1, 1, 4, 1, 3, 1, 1, 4, 4, 2]
def baseStart_5344675 : Nat := 118140960795 + 5344675 * 2 ^ 59
def prefixEnd_5344675 : Nat := 4983230072969 + 3 ^ 40 * 5344675 * 2
def baseEnd_5344675 : Nat := 2744387217068981668182793

theorem tailTrace_5344675 : CollatzResearch.WordTrace tailWord_5344675 prefixEnd_5344675 2744387217068981668182793 := by
  unfold tailWord_5344675
  simp only [CollatzResearch.WordTrace]
  refine ⟨194936311912162747663563479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129957541274775165109042319 194936311912162747663563479)
  ·
    refine ⟨292404467868244121495345219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194936311912162747663563479 292404467868244121495345219)
    ·
      refine ⟨438606701802366182243017829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292404467868244121495345219 438606701802366182243017829)
      ·
        refine ⟨82238756587943659170565843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 438606701802366182243017829 82238756587943659170565843)
        ·
          refine ⟨123358134881915488755848765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82238756587943659170565843 123358134881915488755848765)
          ·
            refine ⟨46259300580718308283443287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123358134881915488755848765 46259300580718308283443287)
            ·
              refine ⟨69388950871077462425164931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46259300580718308283443287 69388950871077462425164931)
              ·
                refine ⟨104083426306616193637747397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69388950871077462425164931 104083426306616193637747397)
                ·
                  refine ⟨19515642432490536307077637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104083426306616193637747397 19515642432490536307077637)
                  ·
                    refine ⟨3659182956091975557577057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19515642432490536307077637 3659182956091975557577057)
                    ·
                      refine ⟨2744387217068981668182793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659182956091975557577057 2744387217068981668182793)
                      ·
                        rfl

theorem cell23_5344675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 1, 4, 4, 2].length) (baseStart_5344675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344675 prefixEnd_5344675 := by exact prefixLift 5344675
  have htrace : WordTrace (prefixWord ++ tailWord_5344675) baseStart_5344675 baseEnd_5344675 := by
    simpa [prefixWord, tailWord_5344675, baseEnd_5344675] using wordTrace_append hprefix tailTrace_5344675
  have hstable : (prefixWord ++ tailWord_5344675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344675).length < 2 ^ (prefixWord ++ tailWord_5344675).sum := by decide
  have hdescent : baseEnd_5344675 < baseStart_5344675 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344768 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 5]
def baseStart_5344768 : Nat := 118140960795 + 5344768 * 2 ^ 59
def prefixEnd_5344768 : Nat := 4983230072969 + 3 ^ 40 * 5344768 * 2
def baseEnd_5344768 : Nat := 2744434970769849804319865

theorem tailTrace_5344768 : CollatzResearch.WordTrace tailWord_5344768 prefixEnd_5344768 2744434970769849804319865 := by
  unfold tailWord_5344768
  simp only [CollatzResearch.WordTrace]
  refine ⟨97469851950412912273349479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129959802600550549697799305 97469851950412912273349479)
  ·
    refine ⟨146204777925619368410024219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97469851950412912273349479 146204777925619368410024219)
    ·
      refine ⟨219307166888429052615036329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146204777925619368410024219 219307166888429052615036329)
      ·
        refine ⟨164480375166321789461277247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219307166888429052615036329 164480375166321789461277247)
        ·
          refine ⟨246720562749482684191915871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164480375166321789461277247 246720562749482684191915871)
          ·
            refine ⟨370080844124224026287873807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246720562749482684191915871 370080844124224026287873807)
            ·
              refine ⟨555121266186336039431810711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370080844124224026287873807 555121266186336039431810711)
              ·
                refine ⟨832681899279504059147716067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 555121266186336039431810711 832681899279504059147716067)
                ·
                  refine ⟨1249022848919256088721574101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 832681899279504059147716067 1249022848919256088721574101)
                  ·
                    refine ⟨29273973021545064579411893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1249022848919256088721574101 29273973021545064579411893)
                    ·
                      refine ⟨2744434970769849804319865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29273973021545064579411893 2744434970769849804319865)
                      ·
                        rfl

theorem cell23_5344768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_5344768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344768 prefixEnd_5344768 := by exact prefixLift 5344768
  have htrace : WordTrace (prefixWord ++ tailWord_5344768) baseStart_5344768 baseEnd_5344768 := by
    simpa [prefixWord, tailWord_5344768, baseEnd_5344768] using wordTrace_append hprefix tailTrace_5344768
  have hstable : (prefixWord ++ tailWord_5344768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344768).length < 2 ^ (prefixWord ++ tailWord_5344768).sum := by decide
  have hdescent : baseEnd_5344768 < baseStart_5344768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344775 : List Nat := [1, 1, 4, 3, 2, 1, 1, 1, 3, 6]
def baseStart_5344775 : Nat := 118140960795 + 5344775 * 2 ^ 59
def prefixEnd_5344775 : Nat := 4983230072969 + 3 ^ 40 * 5344775 * 2
def baseEnd_5344775 : Nat := 914812855044810425644111

theorem tailTrace_5344775 : CollatzResearch.WordTrace tailWord_5344775 prefixEnd_5344775 914812855044810425644111 := by
  unfold tailWord_5344775
  simp only [CollatzResearch.WordTrace]
  refine ⟨194939959211800464742203779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129959972807866976494802519 194939959211800464742203779)
  ·
    refine ⟨292409938817700697113305669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194939959211800464742203779 292409938817700697113305669)
    ·
      refine ⟨54826863528318880708744813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292409938817700697113305669 54826863528318880708744813)
      ·
        refine ⟨20560073823119580265779305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54826863528318880708744813 20560073823119580265779305)
        ·
          refine ⟨15420055367339685199334479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20560073823119580265779305 15420055367339685199334479)
          ·
            refine ⟨23130083051009527799001719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15420055367339685199334479 23130083051009527799001719)
            ·
              refine ⟨34695124576514291698502579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23130083051009527799001719 34695124576514291698502579)
              ·
                refine ⟨52042686864771437547753869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34695124576514291698502579 52042686864771437547753869)
                ·
                  refine ⟨19516007574289289080407701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52042686864771437547753869 19516007574289289080407701)
                  ·
                    refine ⟨914812855044810425644111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19516007574289289080407701 914812855044810425644111)
                    ·
                      rfl

theorem cell23_5344775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 1, 3, 6].length) (baseStart_5344775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344775 prefixEnd_5344775 := by exact prefixLift 5344775
  have htrace : WordTrace (prefixWord ++ tailWord_5344775) baseStart_5344775 baseEnd_5344775 := by
    simpa [prefixWord, tailWord_5344775, baseEnd_5344775] using wordTrace_append hprefix tailTrace_5344775
  have hstable : (prefixWord ++ tailWord_5344775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344775).length < 2 ^ (prefixWord ++ tailWord_5344775).sum := by decide
  have hdescent : baseEnd_5344775 < baseStart_5344775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344779 : List Nat := [1, 1, 1, 1, 8, 1, 3, 1, 1, 5]
def baseStart_5344779 : Nat := 118140960795 + 5344779 * 2 ^ 59
def prefixEnd_5344779 : Nat := 4983230072969 + 3 ^ 40 * 5344779 * 2
def baseEnd_5344779 : Nat := 914813539685683087094105

theorem tailTrace_5344779 : CollatzResearch.WordTrace tailWord_5344779 prefixEnd_5344779 914813539685683087094105 := by
  unfold tailWord_5344779
  simp only [CollatzResearch.WordTrace]
  refine ⟨194940105103785973425349391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129960070069190648950232927 194940105103785973425349391)
  ·
    refine ⟨292410157655678960138024087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194940105103785973425349391 292410157655678960138024087)
    ·
      refine ⟨438615236483518440207036131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292410157655678960138024087 438615236483518440207036131)
      ·
        refine ⟨657922854725277660310554197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438615236483518440207036131 657922854725277660310554197)
        ·
          refine ⟨7710033453811847581764307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 657922854725277660310554197 7710033453811847581764307)
          ·
            refine ⟨11565050180717771372646461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7710033453811847581764307 11565050180717771372646461)
            ·
              refine ⟨4336893817769164264742423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11565050180717771372646461 4336893817769164264742423)
              ·
                refine ⟨6505340726653746397113635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4336893817769164264742423 6505340726653746397113635)
                ·
                  refine ⟨9758011089980619595670453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6505340726653746397113635 9758011089980619595670453)
                  ·
                    refine ⟨914813539685683087094105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9758011089980619595670453 914813539685683087094105)
                    ·
                      rfl

theorem cell23_5344779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 3, 1, 1, 5].length) (baseStart_5344779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344779 prefixEnd_5344779 := by exact prefixLift 5344779
  have htrace : WordTrace (prefixWord ++ tailWord_5344779) baseStart_5344779 baseEnd_5344779 := by
    simpa [prefixWord, tailWord_5344779, baseEnd_5344779] using wordTrace_append hprefix tailTrace_5344779
  have hstable : (prefixWord ++ tailWord_5344779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344779).length < 2 ^ (prefixWord ++ tailWord_5344779).sum := by decide
  have hdescent : baseEnd_5344779 < baseStart_5344779 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344802 : List Nat := [3, 3, 1, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_5344802 : Nat := 118140960795 + 5344802 * 2 ^ 59
def prefixEnd_5344802 : Nat := 4983230072969 + 3 ^ 40 * 5344802 * 2
def baseEnd_5344802 : Nat := 2744452429112102671294709

theorem tailTrace_5344802 : CollatzResearch.WordTrace tailWord_5344802 prefixEnd_5344802 2744452429112102671294709 := by
  unfold tailWord_5344802
  simp only [CollatzResearch.WordTrace]
  refine ⟨48735235995675662088359165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129960629321801765568957773 48735235995675662088359165)
  ·
    refine ⟨18275713498378373283134687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48735235995675662088359165 18275713498378373283134687)
    ·
      refine ⟨27413570247567559924702031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18275713498378373283134687 27413570247567559924702031)
      ·
        refine ⟨41120355371351339887053047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27413570247567559924702031 41120355371351339887053047)
        ·
          refine ⟨61680533057027009830579571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41120355371351339887053047 61680533057027009830579571)
          ·
            refine ⟨92520799585540514745869357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61680533057027009830579571 92520799585540514745869357)
            ·
              refine ⟨34695299844577693029701009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92520799585540514745869357 34695299844577693029701009)
              ·
                refine ⟨26021474883433269772275757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34695299844577693029701009 26021474883433269772275757)
                ·
                  refine ⟨9758053081287476164603409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26021474883433269772275757 9758053081287476164603409)
                  ·
                    refine ⟨7318539810965607123452557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9758053081287476164603409 7318539810965607123452557)
                    ·
                      refine ⟨2744452429112102671294709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7318539810965607123452557 2744452429112102671294709)
                      ·
                        rfl

theorem cell23_5344802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_5344802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344802 prefixEnd_5344802 := by exact prefixLift 5344802
  have htrace : WordTrace (prefixWord ++ tailWord_5344802) baseStart_5344802 baseEnd_5344802 := by
    simpa [prefixWord, tailWord_5344802, baseEnd_5344802] using wordTrace_append hprefix tailTrace_5344802
  have hstable : (prefixWord ++ tailWord_5344802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344802).length < 2 ^ (prefixWord ++ tailWord_5344802).sum := by decide
  have hdescent : baseEnd_5344802 < baseStart_5344802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344832 : List Nat := [2, 1, 1, 2, 2, 2, 1, 4, 4, 1, 3]
def baseStart_5344832 : Nat := 118140960795 + 5344832 * 2 ^ 59
def prefixEnd_5344832 : Nat := 4983230072969 + 3 ^ 40 * 5344832 * 2
def baseEnd_5344832 : Nat := 2744467833531737553919571

theorem tailTrace_5344832 : CollatzResearch.WordTrace tailWord_5344832 prefixEnd_5344832 2744467833531737553919571 := by
  unfold tailWord_5344832
  simp only [CollatzResearch.WordTrace]
  refine ⟨97471019086296981738514375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129961358781729308984685833 97471019086296981738514375)
  ·
    refine ⟨146206528629445472607771563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97471019086296981738514375 146206528629445472607771563)
    ·
      refine ⟨219309792944168208911657345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146206528629445472607771563 219309792944168208911657345)
      ·
        refine ⟨164482344708126156683743009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219309792944168208911657345 164482344708126156683743009)
        ·
          refine ⟨123361758531094617512807257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164482344708126156683743009 123361758531094617512807257)
          ·
            refine ⟨92521318898320963134605443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123361758531094617512807257 92521318898320963134605443)
            ·
              refine ⟨138781978347481444701908165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92521318898320963134605443 138781978347481444701908165)
              ·
                refine ⟨26021620940152770881607781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138781978347481444701908165 26021620940152770881607781)
                ·
                  refine ⟨4879053926278644540301459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26021620940152770881607781 4879053926278644540301459)
                  ·
                    refine ⟨7318580889417966810452189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4879053926278644540301459 7318580889417966810452189)
                    ·
                      refine ⟨2744467833531737553919571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7318580889417966810452189 2744467833531737553919571)
                      ·
                        rfl

theorem cell23_5344832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_5344832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344832 prefixEnd_5344832 := by exact prefixLift 5344832
  have htrace : WordTrace (prefixWord ++ tailWord_5344832) baseStart_5344832 baseEnd_5344832 := by
    simpa [prefixWord, tailWord_5344832, baseEnd_5344832] using wordTrace_append hprefix tailTrace_5344832
  have hstable : (prefixWord ++ tailWord_5344832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344832).length < 2 ^ (prefixWord ++ tailWord_5344832).sum := by decide
  have hdescent : baseEnd_5344832 < baseStart_5344832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344833 : List Nat := [1, 2, 5, 1, 1, 1, 4, 3, 1, 2, 2]
def baseStart_5344833 : Nat := 118140960795 + 5344833 * 2 ^ 59
def prefixEnd_5344833 : Nat := 4983230072969 + 3 ^ 40 * 5344833 * 2
def baseEnd_5344833 : Nat := 2744468347012392050007067

theorem tailTrace_5344833 : CollatzResearch.WordTrace tailWord_5344833 prefixEnd_5344833 2744468347012392050007067 := by
  unfold tailWord_5344833
  simp only [CollatzResearch.WordTrace]
  refine ⟨194942074645590340647815153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129961383097060227098543435 194942074645590340647815153)
  ·
    refine ⟨146206555984192755485861365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194942074645590340647815153 146206555984192755485861365)
    ·
      refine ⟨13706864623518070826799503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146206555984192755485861365 13706864623518070826799503)
      ·
        refine ⟨20560296935277106240199255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13706864623518070826799503 20560296935277106240199255)
        ·
          refine ⟨30840445402915659360298883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20560296935277106240199255 30840445402915659360298883)
          ·
            refine ⟨46260668104373489040448325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30840445402915659360298883 46260668104373489040448325)
            ·
              refine ⟨8673875269570029195084061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46260668104373489040448325 8673875269570029195084061)
              ·
                refine ⟨3252703226088760948156523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8673875269570029195084061 3252703226088760948156523)
                ·
                  refine ⟨4879054839133141422234785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3252703226088760948156523 4879054839133141422234785)
                  ·
                    refine ⟨3659291129349856066676089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4879054839133141422234785 3659291129349856066676089)
                    ·
                      refine ⟨2744468347012392050007067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659291129349856066676089 2744468347012392050007067)
                      ·
                        rfl

theorem cell23_5344833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_5344833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344833 prefixEnd_5344833 := by exact prefixLift 5344833
  have htrace : WordTrace (prefixWord ++ tailWord_5344833) baseStart_5344833 baseEnd_5344833 := by
    simpa [prefixWord, tailWord_5344833, baseEnd_5344833] using wordTrace_append hprefix tailTrace_5344833
  have hstable : (prefixWord ++ tailWord_5344833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344833).length < 2 ^ (prefixWord ++ tailWord_5344833).sum := by decide
  have hdescent : baseEnd_5344833 < baseStart_5344833 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344865 : List Nat := [1, 2, 3, 1, 1, 3, 1, 3, 2, 6]
def baseStart_5344865 : Nat := 118140960795 + 5344865 * 2 ^ 59
def prefixEnd_5344865 : Nat := 4983230072969 + 3 ^ 40 * 5344865 * 2
def baseEnd_5344865 : Nat := 914828259464445308268973

theorem tailTrace_5344865 : CollatzResearch.WordTrace tailWord_5344865 prefixEnd_5344865 914828259464445308268973 := by
  unfold tailWord_5344865
  simp only [CollatzResearch.WordTrace]
  refine ⟨194943241781474410112980049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129962161187649606741986699 194943241781474410112980049)
  ·
    refine ⟨146207431336105807584735037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194943241781474410112980049 146207431336105807584735037)
    ·
      refine ⟨54827786751039677844275639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146207431336105807584735037 54827786751039677844275639)
      ·
        refine ⟨82241680126559516766413459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54827786751039677844275639 82241680126559516766413459)
        ·
          refine ⟨123362520189839275149620189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82241680126559516766413459 123362520189839275149620189)
          ·
            refine ⟨46260945071189728181107571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123362520189839275149620189 46260945071189728181107571)
            ·
              refine ⟨69391417606784592271661357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46260945071189728181107571 69391417606784592271661357)
              ·
                refine ⟨26021781602544222101873009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69391417606784592271661357 26021781602544222101873009)
                ·
                  refine ⟨19516336201908166576404757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26021781602544222101873009 19516336201908166576404757)
                  ·
                    refine ⟨914828259464445308268973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19516336201908166576404757 914828259464445308268973)
                    ·
                      rfl

theorem cell23_5344865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_5344865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344865 prefixEnd_5344865 := by exact prefixLift 5344865
  have htrace : WordTrace (prefixWord ++ tailWord_5344865) baseStart_5344865 baseEnd_5344865 := by
    simpa [prefixWord, tailWord_5344865, baseEnd_5344865] using wordTrace_append hprefix tailTrace_5344865
  have hstable : (prefixWord ++ tailWord_5344865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344865).length < 2 ^ (prefixWord ++ tailWord_5344865).sum := by decide
  have hdescent : baseEnd_5344865 < baseStart_5344865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344875 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 3]
def baseStart_5344875 : Nat := 118140960795 + 5344875 * 2 ^ 59
def prefixEnd_5344875 : Nat := 4983230072969 + 3 ^ 40 * 5344875 * 2
def baseEnd_5344875 : Nat := 2744489913199880885681873

theorem tailTrace_5344875 : CollatzResearch.WordTrace tailWord_5344875 prefixEnd_5344875 2744489913199880885681873 := by
  unfold tailWord_5344875
  simp only [CollatzResearch.WordTrace]
  refine ⟨194943606511438181820844079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129962404340958787880562719 194943606511438181820844079)
  ·
    refine ⟨292415409767157272731266119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194943606511438181820844079 292415409767157272731266119)
    ·
      refine ⟨438623114650735909096899179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292415409767157272731266119 438623114650735909096899179)
      ·
        refine ⟨657934671976103863645348769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438623114650735909096899179 657934671976103863645348769)
        ·
          refine ⟨493451003982077897734011577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 657934671976103863645348769 493451003982077897734011577)
          ·
            refine ⟨370088252986558423300508683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493451003982077897734011577 370088252986558423300508683)
            ·
              refine ⟨555132379479837634950763025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370088252986558423300508683 555132379479837634950763025)
              ·
                refine ⟨416349284609878226213072269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555132379479837634950763025 416349284609878226213072269)
                ·
                  refine ⟨156130981728704334829902101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 416349284609878226213072269 156130981728704334829902101)
                  ·
                    refine ⟨7318639768533015695151661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 156130981728704334829902101 7318639768533015695151661)
                    ·
                      refine ⟨2744489913199880885681873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7318639768533015695151661 2744489913199880885681873)
                      ·
                        rfl

theorem cell23_5344875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 6, 3].length) (baseStart_5344875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344875 prefixEnd_5344875 := by exact prefixLift 5344875
  have htrace : WordTrace (prefixWord ++ tailWord_5344875) baseStart_5344875 baseEnd_5344875 := by
    simpa [prefixWord, tailWord_5344875, baseEnd_5344875] using wordTrace_append hprefix tailTrace_5344875
  have hstable : (prefixWord ++ tailWord_5344875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344875).length < 2 ^ (prefixWord ++ tailWord_5344875).sum := by decide
  have hdescent : baseEnd_5344875 < baseStart_5344875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344889 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 6, 2, 2]
def baseStart_5344889 : Nat := 118140960795 + 5344889 * 2 ^ 59
def prefixEnd_5344889 : Nat := 4983230072969 + 3 ^ 40 * 5344889 * 2
def baseEnd_5344889 : Nat := 2744497101929043830906809

theorem tailTrace_5344889 : CollatzResearch.WordTrace tailWord_5344889 prefixEnd_5344889 2744497101929043830906809 := by
  unfold tailWord_5344889
  simp only [CollatzResearch.WordTrace]
  refine ⟨194944117133387462211853721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129962744755591641474569147 194944117133387462211853721)
  ·
    refine ⟨146208087850040596658890291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194944117133387462211853721 146208087850040596658890291)
    ·
      refine ⟨219312131775060894988335437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146208087850040596658890291 219312131775060894988335437)
      ·
        refine ⟨82242049415647835620625789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219312131775060894988335437 82242049415647835620625789)
        ·
          refine ⟨30840768530867938357734671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82242049415647835620625789 30840768530867938357734671)
          ·
            refine ⟨46261152796301907536602007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30840768530867938357734671 46261152796301907536602007)
            ·
              refine ⟨69391729194452861304903011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46261152796301907536602007 69391729194452861304903011)
              ·
                refine ⟨104087593791679291957354517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69391729194452861304903011 104087593791679291957354517)
                ·
                  refine ⟨4879105958984966810500993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104087593791679291957354517 4879105958984966810500993)
                  ·
                    refine ⟨3659329469238725107875745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4879105958984966810500993 3659329469238725107875745)
                    ·
                      refine ⟨2744497101929043830906809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659329469238725107875745 2744497101929043830906809)
                      ·
                        rfl

theorem cell23_5344889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_5344889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344889 prefixEnd_5344889 := by exact prefixLift 5344889
  have htrace : WordTrace (prefixWord ++ tailWord_5344889) baseStart_5344889 baseEnd_5344889 := by
    simpa [prefixWord, tailWord_5344889, baseEnd_5344889] using wordTrace_append hprefix tailTrace_5344889
  have hstable : (prefixWord ++ tailWord_5344889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344889).length < 2 ^ (prefixWord ++ tailWord_5344889).sum := by decide
  have hdescent : baseEnd_5344889 < baseStart_5344889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344906 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 4, 2, 2]
def baseStart_5344906 : Nat := 118140960795 + 5344906 * 2 ^ 59
def prefixEnd_5344906 : Nat := 4983230072969 + 3 ^ 40 * 5344906 * 2
def baseEnd_5344906 : Nat := 2744505831100170264394231

theorem tailTrace_5344906 : CollatzResearch.WordTrace tailWord_5344906 prefixEnd_5344906 2744505831100170264394231 := by
  unfold tailWord_5344906
  simp only [CollatzResearch.WordTrace]
  refine ⟨48736184293581468528805643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129963158116217249410148381 48736184293581468528805643)
  ·
    refine ⟨73104276440372202793208465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48736184293581468528805643 73104276440372202793208465)
    ·
      refine ⟨54828207330279152094906349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73104276440372202793208465 54828207330279152094906349)
      ·
        refine ⟨20560577748854682035589881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54828207330279152094906349 20560577748854682035589881)
        ·
          refine ⟨15420433311641011526692411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20560577748854682035589881 15420433311641011526692411)
          ·
            refine ⟨23130649967461517290038617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15420433311641011526692411 23130649967461517290038617)
            ·
              refine ⟨17347987475596137967528963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23130649967461517290038617 17347987475596137967528963)
              ·
                refine ⟨26021981213394206951293445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17347987475596137967528963 26021981213394206951293445)
                ·
                  refine ⟨4879121477511413803367521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26021981213394206951293445 4879121477511413803367521)
                  ·
                    refine ⟨3659341108133560352525641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4879121477511413803367521 3659341108133560352525641)
                    ·
                      refine ⟨2744505831100170264394231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659341108133560352525641 2744505831100170264394231)
                      ·
                        rfl

theorem cell23_5344906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_5344906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344906 prefixEnd_5344906 := by exact prefixLift 5344906
  have htrace : WordTrace (prefixWord ++ tailWord_5344906) baseStart_5344906 baseEnd_5344906 := by
    simpa [prefixWord, tailWord_5344906, baseEnd_5344906] using wordTrace_append hprefix tailTrace_5344906
  have hstable : (prefixWord ++ tailWord_5344906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344906).length < 2 ^ (prefixWord ++ tailWord_5344906).sum := by decide
  have hdescent : baseEnd_5344906 < baseStart_5344906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5344912 : List Nat := [2, 1, 1, 1, 1, 1, 3, 8, 5]
def baseStart_5344912 : Nat := 118140960795 + 5344912 * 2 ^ 59
def prefixEnd_5344912 : Nat := 4983230072969 + 3 ^ 40 * 5344912 * 2
def baseEnd_5344912 : Nat := 304945434664899693435467

theorem tailTrace_5344912 : CollatzResearch.WordTrace tailWord_5344912 prefixEnd_5344912 304945434664899693435467 := by
  unfold tailWord_5344912
  simp only [CollatzResearch.WordTrace]
  refine ⟨97472478006152068569970495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129963304008202758093293993 97472478006152068569970495)
  ·
    refine ⟨146208717009228102854955743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97472478006152068569970495 146208717009228102854955743)
    ·
      refine ⟨219313075513842154282433615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146208717009228102854955743 219313075513842154282433615)
      ·
        refine ⟨328969613270763231423650423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219313075513842154282433615 328969613270763231423650423)
        ·
          refine ⟨493454419906144847135475635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328969613270763231423650423 493454419906144847135475635)
          ·
            refine ⟨740181629859217270703213453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493454419906144847135475635 740181629859217270703213453)
            ·
              refine ⟨277568111197206476513705045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 740181629859217270703213453 277568111197206476513705045)
              ·
                refine ⟨3252751303092263396644981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 277568111197206476513705045 3252751303092263396644981)
                ·
                  refine ⟨304945434664899693435467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3252751303092263396644981 304945434664899693435467)
                  ·
                    rfl

theorem cell23_5344912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 8, 5].length) (baseStart_5344912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5344912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5344912 prefixEnd_5344912 := by exact prefixLift 5344912
  have htrace : WordTrace (prefixWord ++ tailWord_5344912) baseStart_5344912 baseEnd_5344912 := by
    simpa [prefixWord, tailWord_5344912, baseEnd_5344912] using wordTrace_append hprefix tailTrace_5344912
  have hstable : (prefixWord ++ tailWord_5344912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5344912).length < 2 ^ (prefixWord ++ tailWord_5344912).sum := by decide
  have hdescent : baseEnd_5344912 < baseStart_5344912 := by decide
  rcases family_descends (prefixWord ++ tailWord_5344912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345039 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 6, 3, 2]
def baseStart_5345039 : Nat := 118140960795 + 5345039 * 2 ^ 59
def prefixEnd_5345039 : Nat := 4983230072969 + 3 ^ 40 * 5345039 * 2
def baseEnd_5345039 : Nat := 2744574124027218244031119

theorem tailTrace_5345039 : CollatzResearch.WordTrace tailWord_5345039 prefixEnd_5345039 2744574124027218244031119 := by
  unfold tailWord_5345039
  simp only [CollatzResearch.WordTrace]
  refine ⟨194949588082844037829814171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129966392055229358553209447 194949588082844037829814171)
  ·
    refine ⟨292424382124266056744721257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194949588082844037829814171 292424382124266056744721257)
    ·
      refine ⟨219318286593199542558540943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292424382124266056744721257 219318286593199542558540943)
      ·
        refine ⟨328977429889799313837811415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219318286593199542558540943 328977429889799313837811415)
        ·
          refine ⟨493466144834698970756717123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328977429889799313837811415 493466144834698970756717123)
          ·
            refine ⟨740199217252048456135075685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493466144834698970756717123 740199217252048456135075685)
            ·
              refine ⟨138787353234759085525326691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 740199217252048456135075685 138787353234759085525326691)
              ·
                refine ⟨208181029852138628287990037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138787353234759085525326691 208181029852138628287990037)
                ·
                  refine ⟨9758485774318998200999533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 208181029852138628287990037 9758485774318998200999533)
                  ·
                    refine ⟨3659432165369624325374825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9758485774318998200999533 3659432165369624325374825)
                    ·
                      refine ⟨2744574124027218244031119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659432165369624325374825 2744574124027218244031119)
                      ·
                        rfl

theorem cell23_5345039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 6, 3, 2].length) (baseStart_5345039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345039 prefixEnd_5345039 := by exact prefixLift 5345039
  have htrace : WordTrace (prefixWord ++ tailWord_5345039) baseStart_5345039 baseEnd_5345039 := by
    simpa [prefixWord, tailWord_5345039, baseEnd_5345039] using wordTrace_append hprefix tailTrace_5345039
  have hstable : (prefixWord ++ tailWord_5345039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345039).length < 2 ^ (prefixWord ++ tailWord_5345039).sum := by decide
  have hdescent : baseEnd_5345039 < baseStart_5345039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345056 : List Nat := [2, 1, 1, 5, 1, 1, 2, 3, 2, 3, 2]
def baseStart_5345056 : Nat := 118140960795 + 5345056 * 2 ^ 59
def prefixEnd_5345056 : Nat := 4983230072969 + 3 ^ 40 * 5345056 * 2
def baseEnd_5345056 : Nat := 2744582853198344677518541

theorem tailTrace_5345056 : CollatzResearch.WordTrace tailWord_5345056 prefixEnd_5345056 2744582853198344677518541 := by
  unfold tailWord_5345056
  simp only [CollatzResearch.WordTrace]
  refine ⟨97475104061891224866591511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129966805415854966488788681 97475104061891224866591511)
  ·
    refine ⟨146212656092836837299887267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97475104061891224866591511 146212656092836837299887267)
    ·
      refine ⟨219318984139255255949830901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146212656092836837299887267 219318984139255255949830901)
      ·
        refine ⟨20561154763055180245296647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 219318984139255255949830901 20561154763055180245296647)
        ·
          refine ⟨30841732144582770367944971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20561154763055180245296647 30841732144582770367944971)
          ·
            refine ⟨46262598216874155551917457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30841732144582770367944971 46262598216874155551917457)
            ·
              refine ⟨34696948662655616663938093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46262598216874155551917457 34696948662655616663938093)
              ·
                refine ⟨13011355748495856248976785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34696948662655616663938093 13011355748495856248976785)
                ·
                  refine ⟨9758516811371892186732589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13011355748495856248976785 9758516811371892186732589)
                  ·
                    refine ⟨3659443804264459570024721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9758516811371892186732589 3659443804264459570024721)
                    ·
                      refine ⟨2744582853198344677518541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659443804264459570024721 2744582853198344677518541)
                      ·
                        rfl

theorem cell23_5345056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_5345056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345056 prefixEnd_5345056 := by exact prefixLift 5345056
  have htrace : WordTrace (prefixWord ++ tailWord_5345056) baseStart_5345056 baseEnd_5345056 := by
    simpa [prefixWord, tailWord_5345056, baseEnd_5345056] using wordTrace_append hprefix tailTrace_5345056
  have hstable : (prefixWord ++ tailWord_5345056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345056).length < 2 ^ (prefixWord ++ tailWord_5345056).sum := by decide
  have hdescent : baseEnd_5345056 < baseStart_5345056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345080 : List Nat := [2, 1, 2, 1, 3, 4, 3, 2, 1, 1, 3]
def baseStart_5345080 : Nat := 118140960795 + 5345080 * 2 ^ 59
def prefixEnd_5345080 : Nat := 4983230072969 + 3 ^ 40 * 5345080 * 2
def baseEnd_5345080 : Nat := 2744595176734052583618431

theorem tailTrace_5345080 : CollatzResearch.WordTrace tailWord_5345080 prefixEnd_5345080 2744595176734052583618431 := by
  unfold tailWord_5345080
  simp only [CollatzResearch.WordTrace]
  refine ⟨97475541737847750916028347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129967388983797001221371129 97475541737847750916028347)
  ·
    refine ⟨146213312606771626374042521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97475541737847750916028347 146213312606771626374042521)
    ·
      refine ⟨109659984455078719780531891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146213312606771626374042521 109659984455078719780531891)
      ·
        refine ⟨164489976682618079670797837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109659984455078719780531891 164489976682618079670797837)
        ·
          refine ⟨61683741255981779876549189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164489976682618079670797837 61683741255981779876549189)
          ·
            refine ⟨11565701485496583726852973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61683741255981779876549189 11565701485496583726852973)
            ·
              refine ⟨4337138057061218897569865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11565701485496583726852973 4337138057061218897569865)
              ·
                refine ⟨3252853542795914173177399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4337138057061218897569865 3252853542795914173177399)
                ·
                  refine ⟨4879280314193871259766099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3252853542795914173177399 4879280314193871259766099)
                  ·
                    refine ⟨7318920471290806889649149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4879280314193871259766099 7318920471290806889649149)
                    ·
                      refine ⟨2744595176734052583618431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7318920471290806889649149 2744595176734052583618431)
                      ·
                        rfl

theorem cell23_5345080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 3, 2, 1, 1, 3].length) (baseStart_5345080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345080 prefixEnd_5345080 := by exact prefixLift 5345080
  have htrace : WordTrace (prefixWord ++ tailWord_5345080) baseStart_5345080 baseEnd_5345080 := by
    simpa [prefixWord, tailWord_5345080, baseEnd_5345080] using wordTrace_append hprefix tailTrace_5345080
  have hstable : (prefixWord ++ tailWord_5345080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345080).length < 2 ^ (prefixWord ++ tailWord_5345080).sum := by decide
  have hdescent : baseEnd_5345080 < baseStart_5345080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345096 : List Nat := [2, 1, 3, 1, 1, 5, 1, 3, 2, 4]
def baseStart_5345096 : Nat := 118140960795 + 5345096 * 2 ^ 59
def prefixEnd_5345096 : Nat := 4983230072969 + 3 ^ 40 * 5345096 * 2
def baseEnd_5345096 : Nat := 914867797474841507006119

theorem tailTrace_5345096 : CollatzResearch.WordTrace tailWord_5345096 prefixEnd_5345096 914867797474841507006119 := by
  unfold tailWord_5345096
  simp only [CollatzResearch.WordTrace]
  refine ⟨97475833521818768282319571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129967778029091691043092761 97475833521818768282319571)
  ·
    refine ⟨146213750282728152423479357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97475833521818768282319571 146213750282728152423479357)
    ·
      refine ⟨54830156356023057158804759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146213750282728152423479357 54830156356023057158804759)
      ·
        refine ⟨82245234534034585738207139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54830156356023057158804759 82245234534034585738207139)
        ·
          refine ⟨123367851801051878607310709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82245234534034585738207139 123367851801051878607310709)
          ·
            refine ⟨11565736106348613619435379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123367851801051878607310709 11565736106348613619435379)
            ·
              refine ⟨17348604159522920429153069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11565736106348613619435379 17348604159522920429153069)
              ·
                refine ⟨6505726559821095160932401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17348604159522920429153069 6505726559821095160932401)
                ·
                  refine ⟨4879294919865821370699301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6505726559821095160932401 4879294919865821370699301)
                  ·
                    refine ⟨914867797474841507006119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4879294919865821370699301 914867797474841507006119)
                    ·
                      rfl

theorem cell23_5345096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_5345096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345096 prefixEnd_5345096 := by exact prefixLift 5345096
  have htrace : WordTrace (prefixWord ++ tailWord_5345096) baseStart_5345096 baseEnd_5345096 := by
    simpa [prefixWord, tailWord_5345096, baseEnd_5345096] using wordTrace_append hprefix tailTrace_5345096
  have hstable : (prefixWord ++ tailWord_5345096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345096).length < 2 ^ (prefixWord ++ tailWord_5345096).sum := by decide
  have hdescent : baseEnd_5345096 < baseStart_5345096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345106 : List Nat := [3, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_5345106 : Nat := 118140960795 + 5345106 * 2 ^ 59
def prefixEnd_5345106 : Nat := 4983230072969 + 3 ^ 40 * 5345106 * 2
def baseEnd_5345106 : Nat := 2744608527231069481893311

theorem tailTrace_5345106 : CollatzResearch.WordTrace tailWord_5345106 prefixEnd_5345106 2744608527231069481893311 := by
  unfold tailWord_5345106
  simp only [CollatzResearch.WordTrace]
  refine ⟨48738007943400327068125793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129968021182400872181668781 48738007943400327068125793)
  ·
    refine ⟨36553505957550245301094345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48738007943400327068125793 36553505957550245301094345)
    ·
      refine ⟨27415129468162683975820759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36553505957550245301094345 27415129468162683975820759)
      ·
        refine ⟨41122694202244025963731139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27415129468162683975820759 41122694202244025963731139)
        ·
          refine ⟨61684041303366038945596709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41122694202244025963731139 61684041303366038945596709)
          ·
            refine ⟨11565757744381132302299383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61684041303366038945596709 11565757744381132302299383)
            ·
              refine ⟨17348636616571698453449075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11565757744381132302299383 17348636616571698453449075)
              ·
                refine ⟨26022954924857547680173613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17348636616571698453449075 26022954924857547680173613)
                ·
                  refine ⟨9758608096821580380065105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26022954924857547680173613 9758608096821580380065105)
                  ·
                    refine ⟨7318956072616185285048829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9758608096821580380065105 7318956072616185285048829)
                    ·
                      refine ⟨2744608527231069481893311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7318956072616185285048829 2744608527231069481893311)
                      ·
                        rfl

theorem cell23_5345106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_5345106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345106 prefixEnd_5345106 := by exact prefixLift 5345106
  have htrace : WordTrace (prefixWord ++ tailWord_5345106) baseStart_5345106 baseEnd_5345106 := by
    simpa [prefixWord, tailWord_5345106, baseEnd_5345106] using wordTrace_append hprefix tailTrace_5345106
  have hstable : (prefixWord ++ tailWord_5345106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345106).length < 2 ^ (prefixWord ++ tailWord_5345106).sum := by decide
  have hdescent : baseEnd_5345106 < baseStart_5345106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345119 : List Nat := [1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 3]
def baseStart_5345119 : Nat := 118140960795 + 5345119 * 2 ^ 59
def prefixEnd_5345119 : Nat := 4983230072969 + 3 ^ 40 * 5345119 * 2
def baseEnd_5345119 : Nat := 2744615202479577931030751

theorem tailTrace_5345119 : CollatzResearch.WordTrace tailWord_5345119 prefixEnd_5345119 2744615202479577931030751 := by
  unfold tailWord_5345119
  simp only [CollatzResearch.WordTrace]
  refine ⟨194952505922554211492726411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129968337281702807661817607 194952505922554211492726411)
  ·
    refine ⟨292428758883831317239089617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194952505922554211492726411 292428758883831317239089617)
    ·
      refine ⟨219321569162873487929317213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292428758883831317239089617 219321569162873487929317213)
      ·
        refine ⟨82245588436077557973493955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219321569162873487929317213 82245588436077557973493955)
        ·
          refine ⟨123368382654116336960240933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82245588436077557973493955 123368382654116336960240933)
          ·
            refine ⟨23131571747646813180045175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123368382654116336960240933 23131571747646813180045175)
            ·
              refine ⟨34697357621470219770067763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23131571747646813180045175 34697357621470219770067763)
              ·
                refine ⟨52046036432205329655101645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34697357621470219770067763 52046036432205329655101645)
                ·
                  refine ⟨19517263662076998620663117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52046036432205329655101645 19517263662076998620663117)
                  ·
                    refine ⟨7318973873278874482748669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19517263662076998620663117 7318973873278874482748669)
                    ·
                      refine ⟨2744615202479577931030751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7318973873278874482748669 2744615202479577931030751)
                      ·
                        rfl

theorem cell23_5345119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_5345119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345119 prefixEnd_5345119 := by exact prefixLift 5345119
  have htrace : WordTrace (prefixWord ++ tailWord_5345119) baseStart_5345119 baseEnd_5345119 := by
    simpa [prefixWord, tailWord_5345119, baseEnd_5345119] using wordTrace_append hprefix tailTrace_5345119
  have hstable : (prefixWord ++ tailWord_5345119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345119).length < 2 ^ (prefixWord ++ tailWord_5345119).sum := by decide
  have hdescent : baseEnd_5345119 < baseStart_5345119 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345123 : List Nat := [1, 1, 1, 5, 5, 1, 1, 1, 1, 1, 5]
def baseStart_5345123 : Nat := 118140960795 + 5345123 * 2 ^ 59
def prefixEnd_5345123 : Nat := 4983230072969 + 3 ^ 40 * 5345123 * 2
def baseEnd_5345123 : Nat := 2744617256402195915380733

theorem tailTrace_5345123 : CollatzResearch.WordTrace tailWord_5345123 prefixEnd_5345123 2744617256402195915380733 := by
  unfold tailWord_5345123
  simp only [CollatzResearch.WordTrace]
  refine ⟨194952651814539720175872023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129968434543026480117248015 194952651814539720175872023)
  ·
    refine ⟨292428977721809580263808035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194952651814539720175872023 292428977721809580263808035)
    ·
      refine ⟨438643466582714370395712053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292428977721809580263808035 438643466582714370395712053)
      ·
        refine ⟨41122824992129472224598005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 438643466582714370395712053 41122824992129472224598005)
        ·
          refine ⟨3855264843012138021056063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41122824992129472224598005 3855264843012138021056063)
          ·
            refine ⟨5782897264518207031584095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855264843012138021056063 5782897264518207031584095)
            ·
              refine ⟨8674345896777310547376143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5782897264518207031584095 8674345896777310547376143)
              ·
                refine ⟨13011518845165965821064215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8674345896777310547376143 13011518845165965821064215)
                ·
                  refine ⟨19517278267748948731596323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13011518845165965821064215 19517278267748948731596323)
                  ·
                    refine ⟨29275917401623423097394485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19517278267748948731596323 29275917401623423097394485)
                    ·
                      refine ⟨2744617256402195915380733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29275917401623423097394485 2744617256402195915380733)
                      ·
                        rfl

theorem cell23_5345123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_5345123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345123 prefixEnd_5345123 := by exact prefixLift 5345123
  have htrace : WordTrace (prefixWord ++ tailWord_5345123) baseStart_5345123 baseEnd_5345123 := by
    simpa [prefixWord, tailWord_5345123, baseEnd_5345123] using wordTrace_append hprefix tailTrace_5345123
  have hstable : (prefixWord ++ tailWord_5345123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345123).length < 2 ^ (prefixWord ++ tailWord_5345123).sum := by decide
  have hdescent : baseEnd_5345123 < baseStart_5345123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345130 : List Nat := [3, 1, 3, 4, 1, 1, 2, 2, 2, 4]
def baseStart_5345130 : Nat := 118140960795 + 5345130 * 2 ^ 59
def prefixEnd_5345130 : Nat := 4983230072969 + 3 ^ 40 * 5345130 * 2
def baseEnd_5345130 : Nat := 914873616922259129331067

theorem tailTrace_5345130 : CollatzResearch.WordTrace tailWord_5345130 prefixEnd_5345130 914873616922259129331067 := by
  unfold tailWord_5345130
  simp only [CollatzResearch.WordTrace]
  refine ⟨48738226781378590092844211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129968604750342906914251229 48738226781378590092844211)
  ·
    refine ⟨73107340172067885139266317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48738226781378590092844211 73107340172067885139266317)
    ·
      refine ⟨27415252564525456927224869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73107340172067885139266317 27415252564525456927224869)
      ·
        refine ⟨5140359855848523173854663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27415252564525456927224869 5140359855848523173854663)
        ·
          refine ⟨7710539783772784760781995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5140359855848523173854663 7710539783772784760781995)
          ·
            refine ⟨11565809675659177141172993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7710539783772784760781995 11565809675659177141172993)
            ·
              refine ⟨8674357256744382855879745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11565809675659177141172993 8674357256744382855879745)
              ·
                refine ⟨6505767942558287141909809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8674357256744382855879745 6505767942558287141909809)
                ·
                  refine ⟨4879325956918715356432357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6505767942558287141909809 4879325956918715356432357)
                  ·
                    refine ⟨914873616922259129331067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4879325956918715356432357 914873616922259129331067)
                    ·
                      rfl

theorem cell23_5345130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_5345130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345130 prefixEnd_5345130 := by exact prefixLift 5345130
  have htrace : WordTrace (prefixWord ++ tailWord_5345130) baseStart_5345130 baseEnd_5345130 := by
    simpa [prefixWord, tailWord_5345130, baseEnd_5345130] using wordTrace_append hprefix tailTrace_5345130
  have hstable : (prefixWord ++ tailWord_5345130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345130).length < 2 ^ (prefixWord ++ tailWord_5345130).sum := by decide
  have hdescent : baseEnd_5345130 < baseStart_5345130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345146 : List Nat := [3, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2]
def baseStart_5345146 : Nat := 118140960795 + 5345146 * 2 ^ 59
def prefixEnd_5345146 : Nat := 4983230072969 + 3 ^ 40 * 5345146 * 2
def baseEnd_5345146 : Nat := 2744629066457249325393127

theorem tailTrace_5345146 : CollatzResearch.WordTrace tailWord_5345146 prefixEnd_5345146 2744629066457249325393127 := by
  unfold tailWord_5345146
  simp only [CollatzResearch.WordTrace]
  refine ⟨48738372673364098775989823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129968993795637596735972861 48738372673364098775989823)
  ·
    refine ⟨73107559010046148163984735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48738372673364098775989823 73107559010046148163984735)
    ·
      refine ⟨109661338515069222245977103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73107559010046148163984735 109661338515069222245977103)
      ·
        refine ⟨164492007772603833368965655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109661338515069222245977103 164492007772603833368965655)
        ·
          refine ⟨246738011658905750053448483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164492007772603833368965655 246738011658905750053448483)
          ·
            refine ⟨370107017488358625080172725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246738011658905750053448483 370107017488358625080172725)
            ·
              refine ⟨34697532889533621101266193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 370107017488358625080172725 34697532889533621101266193)
              ·
                refine ⟨26023149667150215825949645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34697532889533621101266193 26023149667150215825949645)
                ·
                  refine ⟨9758681125181330934731117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26023149667150215825949645 9758681125181330934731117)
                  ·
                    refine ⟨3659505421942999100524169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9758681125181330934731117 3659505421942999100524169)
                    ·
                      refine ⟨2744629066457249325393127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659505421942999100524169 2744629066457249325393127)
                      ·
                        rfl

theorem cell23_5345146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2].length) (baseStart_5345146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345146 prefixEnd_5345146 := by exact prefixLift 5345146
  have htrace : WordTrace (prefixWord ++ tailWord_5345146) baseStart_5345146 baseEnd_5345146 := by
    simpa [prefixWord, tailWord_5345146, baseEnd_5345146] using wordTrace_append hprefix tailTrace_5345146
  have hstable : (prefixWord ++ tailWord_5345146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345146).length < 2 ^ (prefixWord ++ tailWord_5345146).sum := by decide
  have hdescent : baseEnd_5345146 < baseStart_5345146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345180 : List Nat := [2, 2, 3, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_5345180 : Nat := 118140960795 + 5345180 * 2 ^ 59
def prefixEnd_5345180 : Nat := 4983230072969 + 3 ^ 40 * 5345180 * 2
def baseEnd_5345180 : Nat := 2744646524799502192367971

theorem tailTrace_5345180 : CollatzResearch.WordTrace tailWord_5345180 prefixEnd_5345180 2744646524799502192367971 := by
  unfold tailWord_5345180
  simp only [CollatzResearch.WordTrace]
  refine ⟨97477365387666609455348497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129969820516888812607131329 97477365387666609455348497)
  ·
    refine ⟨73108024040749957091511373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97477365387666609455348497 73108024040749957091511373)
    ·
      refine ⟨27415509015281233909316765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73108024040749957091511373 27415509015281233909316765)
      ·
        refine ⟨10280815880730462715993787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27415509015281233909316765 10280815880730462715993787)
        ·
          refine ⟨15421223821095694073990681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10280815880730462715993787 15421223821095694073990681)
          ·
            refine ⟨11565917865821770555493011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15421223821095694073990681 11565917865821770555493011)
            ·
              refine ⟨17348876798732655833239517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11565917865821770555493011 17348876798732655833239517)
              ·
                refine ⟨6505828799524745937464819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17348876798732655833239517 6505828799524745937464819)
                ·
                  refine ⟨9758743199287118906197229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6505828799524745937464819 9758743199287118906197229)
                  ·
                    refine ⟨3659528699732669589823961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9758743199287118906197229 3659528699732669589823961)
                    ·
                      refine ⟨2744646524799502192367971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659528699732669589823961 2744646524799502192367971)
                      ·
                        rfl

theorem cell23_5345180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_5345180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345180 prefixEnd_5345180 := by exact prefixLift 5345180
  have htrace : WordTrace (prefixWord ++ tailWord_5345180) baseStart_5345180 baseEnd_5345180 := by
    simpa [prefixWord, tailWord_5345180, baseEnd_5345180] using wordTrace_append hprefix tailTrace_5345180
  have hstable : (prefixWord ++ tailWord_5345180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345180).length < 2 ^ (prefixWord ++ tailWord_5345180).sum := by decide
  have hdescent : baseEnd_5345180 < baseStart_5345180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345193 : List Nat := [1, 2, 1, 1, 1, 1, 4, 6, 2, 2, 2]
def baseStart_5345193 : Nat := 118140960795 + 5345193 * 2 ^ 59
def prefixEnd_5345193 : Nat := 4983230072969 + 3 ^ 40 * 5345193 * 2
def baseEnd_5345193 : Nat := 2744653200048010641505411

theorem tailTrace_5345193 : CollatzResearch.WordTrace tailWord_5345193 prefixEnd_5345193 2744653200048010641505411 := by
  unfold tailWord_5345193
  simp only [CollatzResearch.WordTrace]
  refine ⟨194955204924286122130920233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129970136616190748087280155 194955204924286122130920233)
  ·
    refine ⟨146216403693214591598190175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194955204924286122130920233 146216403693214591598190175)
    ·
      refine ⟨219324605539821887397285263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146216403693214591598190175 219324605539821887397285263)
      ·
        refine ⟨328986908309732831095927895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219324605539821887397285263 328986908309732831095927895)
        ·
          refine ⟨493480362464599246643891843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328986908309732831095927895 493480362464599246643891843)
          ·
            refine ⟨740220543696898869965837765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493480362464599246643891843 740220543696898869965837765)
            ·
              refine ⟨138791351943168538118594581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 740220543696898869965837765 138791351943168538118594581)
              ·
                refine ⟨6505844622336025224309121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 138791351943168538118594581 6505844622336025224309121)
                ·
                  refine ⟨4879383466752018918231841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6505844622336025224309121 4879383466752018918231841)
                  ·
                    refine ⟨3659537600064014188673881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4879383466752018918231841 3659537600064014188673881)
                    ·
                      refine ⟨2744653200048010641505411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659537600064014188673881 2744653200048010641505411)
                      ·
                        rfl

theorem cell23_5345193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 2, 2, 2].length) (baseStart_5345193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345193 prefixEnd_5345193 := by exact prefixLift 5345193
  have htrace : WordTrace (prefixWord ++ tailWord_5345193) baseStart_5345193 baseEnd_5345193 := by
    simpa [prefixWord, tailWord_5345193, baseEnd_5345193] using wordTrace_append hprefix tailTrace_5345193
  have hstable : (prefixWord ++ tailWord_5345193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345193).length < 2 ^ (prefixWord ++ tailWord_5345193).sum := by decide
  have hdescent : baseEnd_5345193 < baseStart_5345193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345199 : List Nat := [1, 1, 2, 1, 2, 2, 6, 1, 7]
def baseStart_5345199 : Nat := 118140960795 + 5345199 * 2 ^ 59
def prefixEnd_5345199 : Nat := 4983230072969 + 3 ^ 40 * 5345199 * 2
def baseEnd_5345199 : Nat := 304961808992437513114487

theorem tailTrace_5345199 : CollatzResearch.WordTrace tailWord_5345199 prefixEnd_5345199 304961808992437513114487 := by
  unfold tailWord_5345199
  simp only [CollatzResearch.WordTrace]
  refine ⟨194955423762264385155638651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129970282508176256770425767 194955423762264385155638651)
  ·
    refine ⟨292433135643396577733457977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194955423762264385155638651 292433135643396577733457977)
    ·
      refine ⟨219324851732547433300093483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292433135643396577733457977 219324851732547433300093483)
      ·
        refine ⟨328987277598821149950140225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219324851732547433300093483 328987277598821149950140225)
        ·
          refine ⟨246740458199115862462605169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328987277598821149950140225 246740458199115862462605169)
          ·
            refine ⟨185055343649336896846953877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246740458199115862462605169 185055343649336896846953877)
            ·
              refine ⟨8674469233562667039700963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 185055343649336896846953877 8674469233562667039700963)
              ·
                refine ⟨13011703850344000559551445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8674469233562667039700963 13011703850344000559551445)
                ·
                  refine ⟨304961808992437513114487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13011703850344000559551445 304961808992437513114487)
                  ·
                    rfl

theorem cell23_5345199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 6, 1, 7].length) (baseStart_5345199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345199 prefixEnd_5345199 := by exact prefixLift 5345199
  have htrace : WordTrace (prefixWord ++ tailWord_5345199) baseStart_5345199 baseEnd_5345199 := by
    simpa [prefixWord, tailWord_5345199, baseEnd_5345199] using wordTrace_append hprefix tailTrace_5345199
  have hstable : (prefixWord ++ tailWord_5345199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345199).length < 2 ^ (prefixWord ++ tailWord_5345199).sum := by decide
  have hdescent : baseEnd_5345199 < baseStart_5345199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345204 : List Nat := [2, 5, 2, 1, 2, 1, 3, 1, 2, 1, 3]
def baseStart_5345204 : Nat := 118140960795 + 5345204 * 2 ^ 59
def prefixEnd_5345204 : Nat := 4983230072969 + 3 ^ 40 * 5345204 * 2
def baseEnd_5345204 : Nat := 2744658848335210098467861

theorem tailTrace_5345204 : CollatzResearch.WordTrace tailWord_5345204 prefixEnd_5345204 2744658848335210098467861 := by
  unfold tailWord_5345204
  simp only [CollatzResearch.WordTrace]
  refine ⟨97477803063623135504785333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129970404084830847339713777 97477803063623135504785333)
  ·
    refine ⟨9138544037214668953573625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 97477803063623135504785333 9138544037214668953573625)
    ·
      refine ⟨6853908027911001715180219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9138544037214668953573625 6853908027911001715180219)
      ·
        refine ⟨10280862041866502572770329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6853908027911001715180219 10280862041866502572770329)
        ·
          refine ⟨7710646531399876929577747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10280862041866502572770329 7710646531399876929577747)
          ·
            refine ⟨11565969797099815394366621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7710646531399876929577747 11565969797099815394366621)
            ·
              refine ⟨4337238673912430772887483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11565969797099815394366621 4337238673912430772887483)
              ·
                refine ⟨6505858010868646159331225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337238673912430772887483 6505858010868646159331225)
                ·
                  refine ⟨4879393508151484619498419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6505858010868646159331225 4879393508151484619498419)
                  ·
                    refine ⟨7319090262227226929247629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4879393508151484619498419 7319090262227226929247629)
                    ·
                      refine ⟨2744658848335210098467861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7319090262227226929247629 2744658848335210098467861)
                      ·
                        rfl

theorem cell23_5345204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_5345204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345204 prefixEnd_5345204 := by exact prefixLift 5345204
  have htrace : WordTrace (prefixWord ++ tailWord_5345204) baseStart_5345204 baseEnd_5345204 := by
    simpa [prefixWord, tailWord_5345204, baseEnd_5345204] using wordTrace_append hprefix tailTrace_5345204
  have hstable : (prefixWord ++ tailWord_5345204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345204).length < 2 ^ (prefixWord ++ tailWord_5345204).sum := by decide
  have hdescent : baseEnd_5345204 < baseStart_5345204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345239 : List Nat := [1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 5]
def baseStart_5345239 : Nat := 118140960795 + 5345239 * 2 ^ 59
def prefixEnd_5345239 : Nat := 4983230072969 + 3 ^ 40 * 5345239 * 2
def baseEnd_5345239 : Nat := 2744676820158117461530199

theorem tailTrace_5345239 : CollatzResearch.WordTrace tailWord_5345239 prefixEnd_5345239 2744676820158117461530199 := by
  unfold tailWord_5345239
  simp only [CollatzResearch.WordTrace]
  refine ⟨194956882682119471987094771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129971255121412981324729847 194956882682119471987094771)
  ·
    refine ⟨292435324023179207980642157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194956882682119471987094771 292435324023179207980642157)
    ·
      refine ⟨109663246508692202992740809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292435324023179207980642157 109663246508692202992740809)
      ·
        refine ⟨82247434881519152244555607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109663246508692202992740809 82247434881519152244555607)
        ·
          refine ⟨123371152322278728366833411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82247434881519152244555607 123371152322278728366833411)
          ·
            refine ⟨185056728483418092550250117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123371152322278728366833411 185056728483418092550250117)
            ·
              refine ⟨34698136590640892353171897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185056728483418092550250117 34698136590640892353171897)
              ·
                refine ⟨26023602442980669264878923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34698136590640892353171897 26023602442980669264878923)
                ·
                  refine ⟨39035403664471003897318385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26023602442980669264878923 39035403664471003897318385)
                  ·
                    refine ⟨29276552748353252922988789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39035403664471003897318385 29276552748353252922988789)
                    ·
                      refine ⟨2744676820158117461530199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29276552748353252922988789 2744676820158117461530199)
                      ·
                        rfl

theorem cell23_5345239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_5345239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345239 prefixEnd_5345239 := by exact prefixLift 5345239
  have htrace : WordTrace (prefixWord ++ tailWord_5345239) baseStart_5345239 baseEnd_5345239 := by
    simpa [prefixWord, tailWord_5345239, baseEnd_5345239] using wordTrace_append hprefix tailTrace_5345239
  have hstable : (prefixWord ++ tailWord_5345239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345239).length < 2 ^ (prefixWord ++ tailWord_5345239).sum := by decide
  have hdescent : baseEnd_5345239 < baseStart_5345239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345250 : List Nat := [3, 3, 3, 1, 2, 2, 1, 1, 7]
def baseStart_5345250 : Nat := 118140960795 + 5345250 * 2 ^ 59
def prefixEnd_5345250 : Nat := 4983230072969 + 3 ^ 40 * 5345250 * 2
def baseEnd_5345250 : Nat := 304964718716146324276961

theorem tailTrace_5345250 : CollatzResearch.WordTrace tailWord_5345250 prefixEnd_5345250 304964718716146324276961 := by
  unfold tailWord_5345250
  simp only [CollatzResearch.WordTrace]
  refine ⟨48739320971269905216436301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129971522590053080577163469 48739320971269905216436301)
  ·
    refine ⟨18277245364226214456163613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48739320971269905216436301 18277245364226214456163613)
    ·
      refine ⟨6853967011584830421061355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18277245364226214456163613 6853967011584830421061355)
      ·
        refine ⟨10280950517377245631592033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6853967011584830421061355 10280950517377245631592033)
        ·
          refine ⟨7710712888032934223694025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10280950517377245631592033 7710712888032934223694025)
          ·
            refine ⟨5783034666024700667770519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7710712888032934223694025 5783034666024700667770519)
            ·
              refine ⟨8674551999037051001655779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5783034666024700667770519 8674551999037051001655779)
              ·
                refine ⟨13011827998555576502483669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8674551999037051001655779 13011827998555576502483669)
                ·
                  refine ⟨304964718716146324276961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13011827998555576502483669 304964718716146324276961)
                  ·
                    rfl

theorem cell23_5345250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 1, 1, 7].length) (baseStart_5345250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345250 prefixEnd_5345250 := by exact prefixLift 5345250
  have htrace : WordTrace (prefixWord ++ tailWord_5345250) baseStart_5345250 baseEnd_5345250 := by
    simpa [prefixWord, tailWord_5345250, baseEnd_5345250] using wordTrace_append hprefix tailTrace_5345250
  have hstable : (prefixWord ++ tailWord_5345250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345250).length < 2 ^ (prefixWord ++ tailWord_5345250).sum := by decide
  have hdescent : baseEnd_5345250 < baseStart_5345250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345261 : List Nat := [1, 5, 1, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_5345261 : Nat := 118140960795 + 5345261 * 2 ^ 59
def prefixEnd_5345261 : Nat := 4983230072969 + 3 ^ 40 * 5345261 * 2
def baseEnd_5345261 : Nat := 2744688116732516375455099

theorem tailTrace_5345261 : CollatzResearch.WordTrace tailWord_5345261 prefixEnd_5345261 2744688116732516375455099 := by
  unfold tailWord_5345261
  simp only [CollatzResearch.WordTrace]
  refine ⟨194957685088039769744395637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129971790058693179829597091 194957685088039769744395637)
  ·
    refine ⟨18277282977003728413537091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 194957685088039769744395637 18277282977003728413537091)
    ·
      refine ⟨27415924465505592620305637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18277282977003728413537091 27415924465505592620305637)
      ·
        refine ⟨5140485837282298616307307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27415924465505592620305637 5140485837282298616307307)
        ·
          refine ⟨7710728755923447924460961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5140485837282298616307307 7710728755923447924460961)
          ·
            refine ⟨5783046566942585943345721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7710728755923447924460961 5783046566942585943345721)
            ·
              refine ⟨4337284925206939457509291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5783046566942585943345721 4337284925206939457509291)
              ·
                refine ⟨6505927387810409186263937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337284925206939457509291 6505927387810409186263937)
                ·
                  refine ⟨4879445540857806889697953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6505927387810409186263937 4879445540857806889697953)
                  ·
                    refine ⟨3659584155643355167273465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4879445540857806889697953 3659584155643355167273465)
                    ·
                      refine ⟨2744688116732516375455099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659584155643355167273465 2744688116732516375455099)
                      ·
                        rfl

theorem cell23_5345261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_5345261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345261 prefixEnd_5345261 := by exact prefixLift 5345261
  have htrace : WordTrace (prefixWord ++ tailWord_5345261) baseStart_5345261 baseEnd_5345261 := by
    simpa [prefixWord, tailWord_5345261, baseEnd_5345261] using wordTrace_append hprefix tailTrace_5345261
  have hstable : (prefixWord ++ tailWord_5345261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345261).length < 2 ^ (prefixWord ++ tailWord_5345261).sum := by decide
  have hdescent : baseEnd_5345261 < baseStart_5345261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345276 : List Nat := [2, 2, 2, 1, 2, 2, 2, 1, 5, 4]
def baseStart_5345276 : Nat := 118140960795 + 5345276 * 2 ^ 59
def prefixEnd_5345276 : Nat := 4983230072969 + 3 ^ 40 * 5345276 * 2
def baseEnd_5345276 : Nat := 914898606314111272255843

theorem tailTrace_5345276 : CollatzResearch.WordTrace tailWord_5345276 prefixEnd_5345276 914898606314111272255843 := by
  unfold tailWord_5345276
  simp only [CollatzResearch.WordTrace]
  refine ⟨97479116091492713653095841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129972154788656951537461121 97479116091492713653095841)
  ·
    refine ⟨73109337068619535239821881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97479116091492713653095841 73109337068619535239821881)
    ·
      refine ⟨54832002801464651429866411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73109337068619535239821881 54832002801464651429866411)
      ·
        refine ⟨82248004202196977144799617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54832002801464651429866411 82248004202196977144799617)
        ·
          refine ⟨61686003151647732858599713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82248004202196977144799617 61686003151647732858599713)
          ·
            refine ⟨46264502363735799643949785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61686003151647732858599713 46264502363735799643949785)
            ·
              refine ⟨34698376772801849732962339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46264502363735799643949785 34698376772801849732962339)
              ·
                refine ⟨52047565159202774599443509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34698376772801849732962339 52047565159202774599443509)
                ·
                  refine ⟨4879459233675260118697829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52047565159202774599443509 4879459233675260118697829)
                  ·
                    refine ⟨914898606314111272255843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4879459233675260118697829 914898606314111272255843)
                    ·
                      rfl

theorem cell23_5345276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_5345276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345276 prefixEnd_5345276 := by exact prefixLift 5345276
  have htrace : WordTrace (prefixWord ++ tailWord_5345276) baseStart_5345276 baseEnd_5345276 := by
    simpa [prefixWord, tailWord_5345276, baseEnd_5345276] using wordTrace_append hprefix tailTrace_5345276
  have hstable : (prefixWord ++ tailWord_5345276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345276).length < 2 ^ (prefixWord ++ tailWord_5345276).sum := by decide
  have hdescent : baseEnd_5345276 < baseStart_5345276 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345279 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 4]
def baseStart_5345279 : Nat := 118140960795 + 5345279 * 2 ^ 59
def prefixEnd_5345279 : Nat := 4983230072969 + 3 ^ 40 * 5345279 * 2
def baseEnd_5345279 : Nat := 2744697359384297305030015

theorem tailTrace_5345279 : CollatzResearch.WordTrace tailWord_5345279 prefixEnd_5345279 2744697359384297305030015 := by
  unfold tailWord_5345279
  simp only [CollatzResearch.WordTrace]
  refine ⟨194958341601974558818550891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129972227734649705879033927 194958341601974558818550891)
  ·
    refine ⟨292437512402961838227826337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194958341601974558818550891 292437512402961838227826337)
    ·
      refine ⟨219328134302221378670869753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292437512402961838227826337 219328134302221378670869753)
      ·
        refine ⟨164496100726666034003152315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219328134302221378670869753 164496100726666034003152315)
        ·
          refine ⟨246744151089999051004728473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164496100726666034003152315 246744151089999051004728473)
          ·
            refine ⟨185058113317499288253546355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246744151089999051004728473 185058113317499288253546355)
            ·
              refine ⟨277587169976248932380319533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185058113317499288253546355 277587169976248932380319533)
              ·
                refine ⟨104095188741093349642619825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277587169976248932380319533 104095188741093349642619825)
                ·
                  refine ⟨78071391555820012231964869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104095188741093349642619825 78071391555820012231964869)
                  ·
                    refine ⟨14638385916716252293493413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78071391555820012231964869 14638385916716252293493413)
                    ·
                      refine ⟨2744697359384297305030015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14638385916716252293493413 2744697359384297305030015)
                      ·
                        rfl

theorem cell23_5345279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 4, 4].length) (baseStart_5345279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345279 prefixEnd_5345279 := by exact prefixLift 5345279
  have htrace : WordTrace (prefixWord ++ tailWord_5345279) baseStart_5345279 baseEnd_5345279 := by
    simpa [prefixWord, tailWord_5345279, baseEnd_5345279] using wordTrace_append hprefix tailTrace_5345279
  have hstable : (prefixWord ++ tailWord_5345279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345279).length < 2 ^ (prefixWord ++ tailWord_5345279).sum := by decide
  have hdescent : baseEnd_5345279 < baseStart_5345279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345306 : List Nat := [3, 1, 1, 3, 1, 3, 1, 4, 6]
def baseStart_5345306 : Nat := 118140960795 + 5345306 * 2 ^ 59
def prefixEnd_5345306 : Nat := 4983230072969 + 3 ^ 40 * 5345306 * 2
def baseEnd_5345306 : Nat := 304967913706885411043599

theorem tailTrace_5345306 : CollatzResearch.WordTrace tailWord_5345306 prefixEnd_5345306 304967913706885411043599 := by
  unfold tailWord_5345306
  simp only [CollatzResearch.WordTrace]
  refine ⟨48739831593219185607445943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129972884248584494953189181 48739831593219185607445943)
  ·
    refine ⟨73109747389828778411168915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48739831593219185607445943 73109747389828778411168915)
    ·
      refine ⟨109664621084743167616753373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73109747389828778411168915 109664621084743167616753373)
      ·
        refine ⟨41124232906778687856282515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109664621084743167616753373 41124232906778687856282515)
        ·
          refine ⟨61686349360168031784423773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41124232906778687856282515 61686349360168031784423773)
          ·
            refine ⟨23132381010063011919158915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61686349360168031784423773 23132381010063011919158915)
            ·
              refine ⟨34698571515094517878738373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23132381010063011919158915 34698571515094517878738373)
              ·
                refine ⟨6505982159080222102263445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34698571515094517878738373 6505982159080222102263445)
                ·
                  refine ⟨304967913706885411043599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6505982159080222102263445 304967913706885411043599)
                  ·
                    rfl

theorem cell23_5345306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 6].length) (baseStart_5345306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345306 prefixEnd_5345306 := by exact prefixLift 5345306
  have htrace : WordTrace (prefixWord ++ tailWord_5345306) baseStart_5345306 baseEnd_5345306 := by
    simpa [prefixWord, tailWord_5345306, baseEnd_5345306] using wordTrace_append hprefix tailTrace_5345306
  have hstable : (prefixWord ++ tailWord_5345306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345306).length < 2 ^ (prefixWord ++ tailWord_5345306).sum := by decide
  have hdescent : baseEnd_5345306 < baseStart_5345306 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345333 : List Nat := [1, 3, 3, 1, 1, 1, 3, 1, 5, 1, 3]
def baseStart_5345333 : Nat := 118140960795 + 5345333 * 2 ^ 59
def prefixEnd_5345333 : Nat := 4983230072969 + 3 ^ 40 * 5345333 * 2
def baseEnd_5345333 : Nat := 2744725087339640093754767

theorem tailTrace_5345333 : CollatzResearch.WordTrace tailWord_5345333 prefixEnd_5345333 2744725087339640093754767 := by
  unfold tailWord_5345333
  simp only [CollatzResearch.WordTrace]
  refine ⟨194960311143778926041016653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129973540762519284027344435 194960311143778926041016653)
  ·
    refine ⟨73110116678917097265381245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194960311143778926041016653 73110116678917097265381245)
    ·
      refine ⟨27416293754593911474517967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73110116678917097265381245 27416293754593911474517967)
      ·
        refine ⟨41124440631890867211776951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27416293754593911474517967 41124440631890867211776951)
        ·
          refine ⟨61686660947836300817665427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41124440631890867211776951 61686660947836300817665427)
          ·
            refine ⟨92529991421754451226498141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61686660947836300817665427 92529991421754451226498141)
            ·
              refine ⟨34698746783157919209936803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92529991421754451226498141 34698746783157919209936803)
              ·
                refine ⟨52048120174736878814905205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34698746783157919209936803 52048120174736878814905205)
                ·
                  refine ⟨4879511266381582388897363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52048120174736878814905205 4879511266381582388897363)
                  ·
                    refine ⟨7319266899572373583346045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4879511266381582388897363 7319266899572373583346045)
                    ·
                      refine ⟨2744725087339640093754767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7319266899572373583346045 2744725087339640093754767)
                      ·
                        rfl

theorem cell23_5345333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 1, 5, 1, 3].length) (baseStart_5345333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345333 prefixEnd_5345333 := by exact prefixLift 5345333
  have htrace : WordTrace (prefixWord ++ tailWord_5345333) baseStart_5345333 baseEnd_5345333 := by
    simpa [prefixWord, tailWord_5345333, baseEnd_5345333] using wordTrace_append hprefix tailTrace_5345333
  have hstable : (prefixWord ++ tailWord_5345333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345333).length < 2 ^ (prefixWord ++ tailWord_5345333).sum := by decide
  have hdescent : baseEnd_5345333 < baseStart_5345333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345337 : List Nat := [1, 2, 1, 5, 4, 1, 1, 1, 2, 2, 3]
def baseStart_5345337 : Nat := 118140960795 + 5345337 * 2 ^ 59
def prefixEnd_5345337 : Nat := 4983230072969 + 3 ^ 40 * 5345337 * 2
def baseEnd_5345337 : Nat := 2744727141262258078104749

theorem tailTrace_5345337 : CollatzResearch.WordTrace tailWord_5345337 prefixEnd_5345337 2744727141262258078104749 := by
  unfold tailWord_5345337
  simp only [CollatzResearch.WordTrace]
  refine ⟨194960457035764434724162265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129973638023842956482774843 194960457035764434724162265)
  ·
    refine ⟨146220342776823326043121699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194960457035764434724162265 146220342776823326043121699)
    ·
      refine ⟨219330514165234989064682549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146220342776823326043121699 219330514165234989064682549)
      ·
        refine ⟨20562235702990780224813989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 219330514165234989064682549 20562235702990780224813989)
        ·
          refine ⟨3855419194310771292152623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20562235702990780224813989 3855419194310771292152623)
          ·
            refine ⟨5783128791466156938228935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855419194310771292152623 5783128791466156938228935)
            ·
              refine ⟨8674693187199235407343403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5783128791466156938228935 8674693187199235407343403)
              ·
                refine ⟨13012039780798853111015105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8674693187199235407343403 13012039780798853111015105)
                ·
                  refine ⟨9759029835599139833261329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13012039780798853111015105 9759029835599139833261329)
                  ·
                    refine ⟨7319272376699354874945997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9759029835599139833261329 7319272376699354874945997)
                    ·
                      refine ⟨2744727141262258078104749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7319272376699354874945997 2744727141262258078104749)
                      ·
                        rfl

theorem cell23_5345337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_5345337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345337 prefixEnd_5345337 := by exact prefixLift 5345337
  have htrace : WordTrace (prefixWord ++ tailWord_5345337) baseStart_5345337 baseEnd_5345337 := by
    simpa [prefixWord, tailWord_5345337, baseEnd_5345337] using wordTrace_append hprefix tailTrace_5345337
  have hstable : (prefixWord ++ tailWord_5345337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345337).length < 2 ^ (prefixWord ++ tailWord_5345337).sum := by decide
  have hdescent : baseEnd_5345337 < baseStart_5345337 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345374 : List Nat := [4, 4, 1, 1, 2, 1, 3, 1, 6]
def baseStart_5345374 : Nat := 118140960795 + 5345374 * 2 ^ 59
def prefixEnd_5345374 : Nat := 4983230072969 + 3 ^ 40 * 5345374 * 2
def baseEnd_5345374 : Nat := 304971793338497159260231

theorem tailTrace_5345374 : CollatzResearch.WordTrace tailWord_5345374 prefixEnd_5345374 304971793338497159260231 := by
  unfold tailWord_5345374
  simp only [CollatzResearch.WordTrace]
  refine ⟨24370225817078798755407397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129974537691086926695506117 24370225817078798755407397)
  ·
    refine ⟨4569417340702274766638887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24370225817078798755407397 4569417340702274766638887)
    ·
      refine ⟨6854126011053412149958331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4569417340702274766638887 6854126011053412149958331)
      ·
        refine ⟨10281189016580118224937497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6854126011053412149958331 10281189016580118224937497)
        ·
          refine ⟨7710891762435088668703123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10281189016580118224937497 7710891762435088668703123)
          ·
            refine ⟨11566337643652633003054685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7710891762435088668703123 11566337643652633003054685)
            ·
              refine ⟨4337376616369737376145507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11566337643652633003054685 4337376616369737376145507)
              ·
                refine ⟨6506064924554606064218261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337376616369737376145507 6506064924554606064218261)
                ·
                  refine ⟨304971793338497159260231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6506064924554606064218261 304971793338497159260231)
                  ·
                    rfl

theorem cell23_5345374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_5345374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345374 prefixEnd_5345374 := by exact prefixLift 5345374
  have htrace : WordTrace (prefixWord ++ tailWord_5345374) baseStart_5345374 baseEnd_5345374 := by
    simpa [prefixWord, tailWord_5345374, baseEnd_5345374] using wordTrace_append hprefix tailTrace_5345374
  have hstable : (prefixWord ++ tailWord_5345374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345374).length < 2 ^ (prefixWord ++ tailWord_5345374).sum := by decide
  have hdescent : baseEnd_5345374 < baseStart_5345374 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345376 : List Nat := [2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 5]
def baseStart_5345376 : Nat := 118140960795 + 5345376 * 2 ^ 59
def prefixEnd_5345376 : Nat := 4983230072969 + 3 ^ 40 * 5345376 * 2
def baseEnd_5345376 : Nat := 2744747167007783425517069

theorem tailTrace_5345376 : CollatzResearch.WordTrace tailWord_5345376 prefixEnd_5345376 2744747167007783425517069 := by
  unfold tailWord_5345376
  simp only [CollatzResearch.WordTrace]
  refine ⟨97480939741311572192415991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129974586321748762923221321 97480939741311572192415991)
  ·
    refine ⟨146221409611967358288623987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97480939741311572192415991 146221409611967358288623987)
    ·
      refine ⟨219332114417951037432935981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146221409611967358288623987 219332114417951037432935981)
      ·
        refine ⟨82249542906731639037350993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219332114417951037432935981 82249542906731639037350993)
        ·
          refine ⟨61687157180048729278013245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82249542906731639037350993 61687157180048729278013245)
          ·
            refine ⟨23132683942518273479254967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61687157180048729278013245 23132683942518273479254967)
            ·
              refine ⟨34699025913777410218882451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23132683942518273479254967 34699025913777410218882451)
              ·
                refine ⟨52048538870666115328323677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34699025913777410218882451 52048538870666115328323677)
                ·
                  refine ⟨19518202076499793248121379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52048538870666115328323677 19518202076499793248121379)
                  ·
                    refine ⟨29277303114749689872182069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19518202076499793248121379 29277303114749689872182069)
                    ·
                      refine ⟨2744747167007783425517069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29277303114749689872182069 2744747167007783425517069)
                      ·
                        rfl

theorem cell23_5345376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_5345376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345376 prefixEnd_5345376 := by exact prefixLift 5345376
  have htrace : WordTrace (prefixWord ++ tailWord_5345376) baseStart_5345376 baseEnd_5345376 := by
    simpa [prefixWord, tailWord_5345376, baseEnd_5345376] using wordTrace_append hprefix tailTrace_5345376
  have hstable : (prefixWord ++ tailWord_5345376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345376).length < 2 ^ (prefixWord ++ tailWord_5345376).sum := by decide
  have hdescent : baseEnd_5345376 < baseStart_5345376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345390 : List Nat := [4, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_5345390 : Nat := 118140960795 + 5345390 * 2 ^ 59
def prefixEnd_5345390 : Nat := 4983230072969 + 3 ^ 40 * 5345390 * 2
def baseEnd_5345390 : Nat := 2744754355736946370742005

theorem tailTrace_5345390 : CollatzResearch.WordTrace tailWord_5345390 prefixEnd_5345390 2744754355736946370742005 := by
  unfold tailWord_5345390
  simp only [CollatzResearch.WordTrace]
  refine ⟨24370298763071553096980203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129974926736381616517227749 24370298763071553096980203)
  ·
    refine ⟨36555448144607329645470305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24370298763071553096980203 36555448144607329645470305)
    ·
      refine ⟨27416586108455497234102729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36555448144607329645470305 27416586108455497234102729)
      ·
        refine ⟨20562439581341622925577047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27416586108455497234102729 20562439581341622925577047)
        ·
          refine ⟨30843659372012434388365571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20562439581341622925577047 30843659372012434388365571)
          ·
            refine ⟨46265489058018651582548357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30843659372012434388365571 46265489058018651582548357)
            ·
              refine ⟨8674779198378497171727817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46265489058018651582548357 8674779198378497171727817)
              ·
                refine ⟨6506084398783872878795863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8674779198378497171727817 6506084398783872878795863)
                ·
                  refine ⟨9759126598175809318193795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6506084398783872878795863 9759126598175809318193795)
                  ·
                    refine ⟨14638689897263713977290693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9759126598175809318193795 14638689897263713977290693)
                    ·
                      refine ⟨2744754355736946370742005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14638689897263713977290693 2744754355736946370742005)
                      ·
                        rfl

theorem cell23_5345390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_5345390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345390 prefixEnd_5345390 := by exact prefixLift 5345390
  have htrace : WordTrace (prefixWord ++ tailWord_5345390) baseStart_5345390 baseEnd_5345390 := by
    simpa [prefixWord, tailWord_5345390, baseEnd_5345390] using wordTrace_append hprefix tailTrace_5345390
  have hstable : (prefixWord ++ tailWord_5345390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345390).length < 2 ^ (prefixWord ++ tailWord_5345390).sum := by decide
  have hdescent : baseEnd_5345390 < baseStart_5345390 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345424 : List Nat := [2, 1, 1, 1, 1, 1, 9, 2, 1, 2, 2]
def baseStart_5345424 : Nat := 118140960795 + 5345424 * 2 ^ 59
def prefixEnd_5345424 : Nat := 4983230072969 + 3 ^ 40 * 5345424 * 2
def baseEnd_5345424 : Nat := 2744771814079199237716849

theorem tailTrace_5345424 : CollatzResearch.WordTrace tailWord_5345424 prefixEnd_5345424 2744771814079199237716849 := by
  unfold tailWord_5345424
  simp only [CollatzResearch.WordTrace]
  refine ⟨97481815093224624291289663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129975753457632832388386217 97481815093224624291289663)
  ·
    refine ⟨146222722639836936436934495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97481815093224624291289663 146222722639836936436934495)
    ·
      refine ⟨219334083959755404655401743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146222722639836936436934495 219334083959755404655401743)
      ·
        refine ⟨329001125939633106983102615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219334083959755404655401743 329001125939633106983102615)
        ·
          refine ⟨493501688909449660474653923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329001125939633106983102615 493501688909449660474653923)
          ·
            refine ⟨740252533364174490711980885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493501688909449660474653923 740252533364174490711980885)
            ·
              refine ⟨4337417187680709906515513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 740252533364174490711980885 4337417187680709906515513)
              ·
                refine ⟨3253062890760532429886635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4337417187680709906515513 3253062890760532429886635)
                ·
                  refine ⟨4879594336140798644829953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3253062890760532429886635 4879594336140798644829953)
                  ·
                    refine ⟨3659695752105598983622465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4879594336140798644829953 3659695752105598983622465)
                    ·
                      refine ⟨2744771814079199237716849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659695752105598983622465 2744771814079199237716849)
                      ·
                        rfl

theorem cell23_5345424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 1, 2, 2].length) (baseStart_5345424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345424 prefixEnd_5345424 := by exact prefixLift 5345424
  have htrace : WordTrace (prefixWord ++ tailWord_5345424) baseStart_5345424 baseEnd_5345424 := by
    simpa [prefixWord, tailWord_5345424, baseEnd_5345424] using wordTrace_append hprefix tailTrace_5345424
  have hstable : (prefixWord ++ tailWord_5345424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345424).length < 2 ^ (prefixWord ++ tailWord_5345424).sum := by decide
  have hdescent : baseEnd_5345424 < baseStart_5345424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345434 : List Nat := [3, 1, 1, 5, 2, 2, 2, 1, 2, 4]
def baseStart_5345434 : Nat := 118140960795 + 5345434 * 2 ^ 59
def prefixEnd_5345434 : Nat := 4983230072969 + 3 ^ 40 * 5345434 * 2
def baseEnd_5345434 : Nat := 914925649628581399530601

theorem tailTrace_5345434 : CollatzResearch.WordTrace tailWord_5345434 prefixEnd_5345434 914925649628581399530601 := by
  unfold tailWord_5345434
  simp only [CollatzResearch.WordTrace]
  refine ⟨48740998729103255072610839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129975996610942013526962237 48740998729103255072610839)
  ·
    refine ⟨73111498093654882608916259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48740998729103255072610839 73111498093654882608916259)
    ·
      refine ⟨109667247140482323913374389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73111498093654882608916259 109667247140482323913374389)
      ·
        refine ⟨10281304419420217866878849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109667247140482323913374389 10281304419420217866878849)
        ·
          refine ⟨7710978314565163400159137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10281304419420217866878849 7710978314565163400159137)
          ·
            refine ⟨5783233735923872550119353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7710978314565163400159137 5783233735923872550119353)
            ·
              refine ⟨4337425301942904412589515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5783233735923872550119353 4337425301942904412589515)
              ·
                refine ⟨6506137952914356618884273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337425301942904412589515 6506137952914356618884273)
                ·
                  refine ⟨4879603464685767464163205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6506137952914356618884273 4879603464685767464163205)
                  ·
                    refine ⟨914925649628581399530601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4879603464685767464163205 914925649628581399530601)
                    ·
                      rfl

theorem cell23_5345434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 2, 2, 1, 2, 4].length) (baseStart_5345434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345434 prefixEnd_5345434 := by exact prefixLift 5345434
  have htrace : WordTrace (prefixWord ++ tailWord_5345434) baseStart_5345434 baseEnd_5345434 := by
    simpa [prefixWord, tailWord_5345434, baseEnd_5345434] using wordTrace_append hprefix tailTrace_5345434
  have hstable : (prefixWord ++ tailWord_5345434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345434).length < 2 ^ (prefixWord ++ tailWord_5345434).sum := by decide
  have hdescent : baseEnd_5345434 < baseStart_5345434 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345444 : List Nat := [2, 3, 1, 2, 5, 1, 1, 2, 1, 2, 3]
def baseStart_5345444 : Nat := 118140960795 + 5345444 * 2 ^ 59
def prefixEnd_5345444 : Nat := 4983230072969 + 3 ^ 40 * 5345444 * 2
def baseEnd_5345444 : Nat := 2744782083692289159466757

theorem tailTrace_5345444 : CollatzResearch.WordTrace tailWord_5345444 prefixEnd_5345444 2744782083692289159466757 := by
  unfold tailWord_5345444
  simp only [CollatzResearch.WordTrace]
  refine ⟨97482179823188395999153693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129976239764251194665538257 97482179823188395999153693)
  ·
    refine ⟨36555817433695648499682635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97482179823188395999153693 36555817433695648499682635)
    ·
      refine ⟨54833726150543472749523953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36555817433695648499682635 54833726150543472749523953)
      ·
        refine ⟨41125294612907604562142965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54833726150543472749523953 41125294612907604562142965)
        ·
          refine ⟨3855496369960087927700903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41125294612907604562142965 3855496369960087927700903)
          ·
            refine ⟨5783244554940131891551355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855496369960087927700903 5783244554940131891551355)
            ·
              refine ⟨8674866832410197837327033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5783244554940131891551355 8674866832410197837327033)
              ·
                refine ⟨6506150124307648377995275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8674866832410197837327033 6506150124307648377995275)
                ·
                  refine ⟨9759225186461472566992913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6506150124307648377995275 9759225186461472566992913)
                  ·
                    refine ⟨7319418889846104425244685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9759225186461472566992913 7319418889846104425244685)
                    ·
                      refine ⟨2744782083692289159466757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7319418889846104425244685 2744782083692289159466757)
                      ·
                        rfl

theorem cell23_5345444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_5345444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345444 prefixEnd_5345444 := by exact prefixLift 5345444
  have htrace : WordTrace (prefixWord ++ tailWord_5345444) baseStart_5345444 baseEnd_5345444 := by
    simpa [prefixWord, tailWord_5345444, baseEnd_5345444] using wordTrace_append hprefix tailTrace_5345444
  have hstable : (prefixWord ++ tailWord_5345444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345444).length < 2 ^ (prefixWord ++ tailWord_5345444).sum := by decide
  have hdescent : baseEnd_5345444 < baseStart_5345444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345467 : List Nat := [1, 1, 1, 1, 1, 2, 9, 1, 1, 3, 2]
def baseStart_5345467 : Nat := 118140960795 + 5345467 * 2 ^ 59
def prefixEnd_5345467 : Nat := 4983230072969 + 3 ^ 40 * 5345467 * 2
def baseEnd_5345467 : Nat := 2744793893747342569479151

theorem tailTrace_5345467 : CollatzResearch.WordTrace tailWord_5345467 prefixEnd_5345467 2744793893747342569479151 := by
  unfold tailWord_5345467
  simp only [CollatzResearch.WordTrace]
  refine ⟨194965198525293466926394655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129976799016862311284263103 194965198525293466926394655)
  ·
    refine ⟨292447797787940200389591983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194965198525293466926394655 292447797787940200389591983)
    ·
      refine ⟨438671696681910300584387975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292447797787940200389591983 438671696681910300584387975)
      ·
        refine ⟨658007545022865450876581963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438671696681910300584387975 658007545022865450876581963)
        ·
          refine ⟨987011317534298176314872945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658007545022865450876581963 987011317534298176314872945)
          ·
            refine ⟨740258488150723632236154709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 987011317534298176314872945 740258488150723632236154709)
            ·
              refine ⟨4337452079008146282633719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 740258488150723632236154709 4337452079008146282633719)
              ·
                refine ⟨6506178118512219423950579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337452079008146282633719 6506178118512219423950579)
                ·
                  refine ⟨9759267177768329135925869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6506178118512219423950579 9759267177768329135925869)
                  ·
                    refine ⟨3659725191663123425972201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9759267177768329135925869 3659725191663123425972201)
                    ·
                      refine ⟨2744793893747342569479151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659725191663123425972201 2744793893747342569479151)
                      ·
                        rfl

theorem cell23_5345467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 9, 1, 1, 3, 2].length) (baseStart_5345467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345467 prefixEnd_5345467 := by exact prefixLift 5345467
  have htrace : WordTrace (prefixWord ++ tailWord_5345467) baseStart_5345467 baseEnd_5345467 := by
    simpa [prefixWord, tailWord_5345467, baseEnd_5345467] using wordTrace_append hprefix tailTrace_5345467
  have hstable : (prefixWord ++ tailWord_5345467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345467).length < 2 ^ (prefixWord ++ tailWord_5345467).sum := by decide
  have hdescent : baseEnd_5345467 < baseStart_5345467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345497 : List Nat := [1, 2, 1, 2, 3, 1, 4, 3, 2, 2, 2]
def baseStart_5345497 : Nat := 118140960795 + 5345497 * 2 ^ 59
def prefixEnd_5345497 : Nat := 4983230072969 + 3 ^ 40 * 5345497 * 2
def baseEnd_5345497 : Nat := 2744809298166977452104013

theorem tailTrace_5345497 : CollatzResearch.WordTrace tailWord_5345497 prefixEnd_5345497 2744809298166977452104013 := by
  unfold tailWord_5345497
  simp only [CollatzResearch.WordTrace]
  refine ⟨194966292715184782049986745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129977528476789854699991163 194966292715184782049986745)
  ·
    refine ⟨146224719536388586537490059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194966292715184782049986745 146224719536388586537490059)
    ·
      refine ⟨219337079304582879806235089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146224719536388586537490059 219337079304582879806235089)
      ·
        refine ⟨164502809478437159854676317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219337079304582879806235089 164502809478437159854676317)
        ·
          refine ⟨61688553554413934945503619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164502809478437159854676317 61688553554413934945503619)
          ·
            refine ⟨92532830331620902418255429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61688553554413934945503619 92532830331620902418255429)
            ·
              refine ⟨17349905687178919203422893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92532830331620902418255429 17349905687178919203422893)
              ·
                refine ⟨6506214632692094701283585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17349905687178919203422893 6506214632692094701283585)
                ·
                  refine ⟨4879660974519071025962689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6506214632692094701283585 4879660974519071025962689)
                  ·
                    refine ⟨3659745730889303269472017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4879660974519071025962689 3659745730889303269472017)
                    ·
                      refine ⟨2744809298166977452104013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659745730889303269472017 2744809298166977452104013)
                      ·
                        rfl

theorem cell23_5345497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 2, 2, 2].length) (baseStart_5345497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345497 prefixEnd_5345497 := by exact prefixLift 5345497
  have htrace : WordTrace (prefixWord ++ tailWord_5345497) baseStart_5345497 baseEnd_5345497 := by
    simpa [prefixWord, tailWord_5345497, baseEnd_5345497] using wordTrace_append hprefix tailTrace_5345497
  have hstable : (prefixWord ++ tailWord_5345497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345497).length < 2 ^ (prefixWord ++ tailWord_5345497).sum := by decide
  have hdescent : baseEnd_5345497 < baseStart_5345497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345533 : List Nat := [1, 4, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_5345533 : Nat := 118140960795 + 5345533 * 2 ^ 59
def prefixEnd_5345533 : Nat := 4983230072969 + 3 ^ 40 * 5345533 * 2
def baseEnd_5345533 : Nat := 914942594490179770417949

theorem tailTrace_5345533 : CollatzResearch.WordTrace tailWord_5345533 prefixEnd_5345533 914942594490179770417949 := by
  unfold tailWord_5345533
  simp only [CollatzResearch.WordTrace]
  refine ⟨194967605743054360198297253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129978403828702906798864835 194967605743054360198297253)
  ·
    refine ⟨36556426076822692537180735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194967605743054360198297253 36556426076822692537180735)
    ·
      refine ⟨54834639115234038805771103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36556426076822692537180735 54834639115234038805771103)
      ·
        refine ⟨82251958672851058208656655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54834639115234038805771103 82251958672851058208656655)
        ·
          refine ⟨123377938009276587312984983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82251958672851058208656655 123377938009276587312984983)
          ·
            refine ⟨185066907013914880969477475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123377938009276587312984983 185066907013914880969477475)
            ·
              refine ⟨277600360520872321454216213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185066907013914880969477475 277600360520872321454216213)
              ·
                refine ⟨13012516899415890068166385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 277600360520872321454216213 13012516899415890068166385)
                ·
                  refine ⟨9759387674561917551124789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13012516899415890068166385 9759387674561917551124789)
                  ·
                    refine ⟨914942594490179770417949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9759387674561917551124789 914942594490179770417949)
                    ·
                      rfl

theorem cell23_5345533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_5345533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345533 prefixEnd_5345533 := by exact prefixLift 5345533
  have htrace : WordTrace (prefixWord ++ tailWord_5345533) baseStart_5345533 baseEnd_5345533 := by
    simpa [prefixWord, tailWord_5345533, baseEnd_5345533] using wordTrace_append hprefix tailTrace_5345533
  have hstable : (prefixWord ++ tailWord_5345533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345533).length < 2 ^ (prefixWord ++ tailWord_5345533).sum := by decide
  have hdescent : baseEnd_5345533 < baseStart_5345533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345553 : List Nat := [1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 4]
def baseStart_5345553 : Nat := 118140960795 + 5345553 * 2 ^ 59
def prefixEnd_5345553 : Nat := 4983230072969 + 3 ^ 40 * 5345553 * 2
def baseEnd_5345553 : Nat := 2744838053083629233003755

theorem tailTrace_5345553 : CollatzResearch.WordTrace tailWord_5345553 prefixEnd_5345553 2744838053083629233003755 := by
  unfold tailWord_5345553
  simp only [CollatzResearch.WordTrace]
  refine ⟨194968335202981903614025313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129978890135321269076016875 194968335202981903614025313)
  ·
    refine ⟨146226251402236427710518985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194968335202981903614025313 146226251402236427710518985)
    ·
      refine ⟨109669688551677320782889239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146226251402236427710518985 109669688551677320782889239)
      ·
        refine ⟨164504532827515981174333859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109669688551677320782889239 164504532827515981174333859)
        ·
          refine ⟨246756799241273971761500789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164504532827515981174333859 246756799241273971761500789)
          ·
            refine ⟨23133449928869434852640699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 246756799241273971761500789 23133449928869434852640699)
            ·
              refine ⟨34700174893304152278961049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23133449928869434852640699 34700174893304152278961049)
              ·
                refine ⟨26025131169978114209220787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34700174893304152278961049 26025131169978114209220787)
                ·
                  refine ⟨39037696754967171313831181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26025131169978114209220787 39037696754967171313831181)
                  ·
                    refine ⟨14639136283112689242686693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39037696754967171313831181 14639136283112689242686693)
                    ·
                      refine ⟨2744838053083629233003755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14639136283112689242686693 2744838053083629233003755)
                      ·
                        rfl

theorem cell23_5345553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 4].length) (baseStart_5345553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345553 prefixEnd_5345553 := by exact prefixLift 5345553
  have htrace : WordTrace (prefixWord ++ tailWord_5345553) baseStart_5345553 baseEnd_5345553 := by
    simpa [prefixWord, tailWord_5345553, baseEnd_5345553] using wordTrace_append hprefix tailTrace_5345553
  have hstable : (prefixWord ++ tailWord_5345553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345553).length < 2 ^ (prefixWord ++ tailWord_5345553).sum := by decide
  have hdescent : baseEnd_5345553 < baseStart_5345553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345570 : List Nat := [3, 3, 1, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_5345570 : Nat := 118140960795 + 5345570 * 2 ^ 59
def prefixEnd_5345570 : Nat := 4983230072969 + 3 ^ 40 * 5345570 * 2
def baseEnd_5345570 : Nat := 2744846782254755666491177

theorem tailTrace_5345570 : CollatzResearch.WordTrace tailWord_5345570 prefixEnd_5345570 2744846782254755666491177 := by
  unfold tailWord_5345570
  simp only [CollatzResearch.WordTrace]
  refine ⟨48742238810980078879348541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129979303495946877011596109 48742238810980078879348541)
  ·
    refine ⟨18278339554117529579755703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48742238810980078879348541 18278339554117529579755703)
    ·
      refine ⟨27417509331176294369633555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18278339554117529579755703 27417509331176294369633555)
      ·
        refine ⟨41126263996764441554450333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27417509331176294369633555 41126263996764441554450333)
        ·
          refine ⟨15422348998786665582918875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41126263996764441554450333 15422348998786665582918875)
          ·
            refine ⟨23133523498179998374378313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15422348998786665582918875 23133523498179998374378313)
            ·
              refine ⟨17350142623634998780783735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23133523498179998374378313 17350142623634998780783735)
              ·
                refine ⟨26025213935452498171175603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17350142623634998780783735 26025213935452498171175603)
                ·
                  refine ⟨39037820903178747256763405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26025213935452498171175603 39037820903178747256763405)
                  ·
                    refine ⟨14639182838692030221286277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39037820903178747256763405 14639182838692030221286277)
                    ·
                      refine ⟨2744846782254755666491177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14639182838692030221286277 2744846782254755666491177)
                      ·
                        rfl

theorem cell23_5345570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_5345570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345570 prefixEnd_5345570 := by exact prefixLift 5345570
  have htrace : WordTrace (prefixWord ++ tailWord_5345570) baseStart_5345570 baseEnd_5345570 := by
    simpa [prefixWord, tailWord_5345570, baseEnd_5345570] using wordTrace_append hprefix tailTrace_5345570
  have hstable : (prefixWord ++ tailWord_5345570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345570).length < 2 ^ (prefixWord ++ tailWord_5345570).sum := by decide
  have hdescent : baseEnd_5345570 < baseStart_5345570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345704 : List Nat := [2, 1, 6, 1, 1, 2, 1, 1, 4, 4]
def baseStart_5345704 : Nat := 118140960795 + 5345704 * 2 ^ 59
def prefixEnd_5345704 : Nat := 4983230072969 + 3 ^ 40 * 5345704 * 2
def baseEnd_5345704 : Nat := 914971862887486047405187

theorem tailTrace_5345704 : CollatzResearch.WordTrace tailWord_5345704 prefixEnd_5345704 914971862887486047405187 := by
  unfold tailWord_5345704
  simp only [CollatzResearch.WordTrace]
  refine ⟨97486921312717428201386083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129982561750289904268514777 97486921312717428201386083)
  ·
    refine ⟨146230381969076142302079125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97486921312717428201386083 146230381969076142302079125)
    ·
      refine ⟨6854549154800444170409959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 146230381969076142302079125 6854549154800444170409959)
      ·
        refine ⟨10281823732200666255614939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6854549154800444170409959 10281823732200666255614939)
        ·
          refine ⟨15422735598300999383422409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10281823732200666255614939 15422735598300999383422409)
          ·
            refine ⟨11567051698725749537566807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15422735598300999383422409 11567051698725749537566807)
            ·
              refine ⟨17350577548088624306350211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11567051698725749537566807 17350577548088624306350211)
              ·
                refine ⟨26025866322132936459525317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17350577548088624306350211 26025866322132936459525317)
                ·
                  refine ⟨4879849935399925586160997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26025866322132936459525317 4879849935399925586160997)
                  ·
                    refine ⟨914971862887486047405187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4879849935399925586160997 914971862887486047405187)
                    ·
                      rfl

theorem cell23_5345704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_5345704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345704 prefixEnd_5345704 := by exact prefixLift 5345704
  have htrace : WordTrace (prefixWord ++ tailWord_5345704) baseStart_5345704 baseEnd_5345704 := by
    simpa [prefixWord, tailWord_5345704, baseEnd_5345704] using wordTrace_append hprefix tailTrace_5345704
  have hstable : (prefixWord ++ tailWord_5345704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345704).length < 2 ^ (prefixWord ++ tailWord_5345704).sum := by decide
  have hdescent : baseEnd_5345704 < baseStart_5345704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345724 : List Nat := [2, 2, 2, 4, 1, 3, 1, 1, 1, 2, 4]
def baseStart_5345724 : Nat := 118140960795 + 5345724 * 2 ^ 59
def prefixEnd_5345724 : Nat := 4983230072969 + 3 ^ 40 * 5345724 * 2
def baseEnd_5345724 : Nat := 2744925858275548063965469

theorem tailTrace_5345724 : CollatzResearch.WordTrace tailWord_5345724 prefixEnd_5345724 2744925858275548063965469 := by
  unfold tailWord_5345724
  simp only [CollatzResearch.WordTrace]
  refine ⟨97487286042681199909250113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129983048056908266545666817 97487286042681199909250113)
  ·
    refine ⟨73115464532010899931937585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97487286042681199909250113 73115464532010899931937585)
    ·
      refine ⟨54836598399008174948953189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73115464532010899931937585 54836598399008174948953189)
      ·
        refine ⟨10281862199814032802928723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54836598399008174948953189 10281862199814032802928723)
        ·
          refine ⟨15422793299721049204393085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10281862199814032802928723 15422793299721049204393085)
          ·
            refine ⟨5783547487395393451647407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15422793299721049204393085 5783547487395393451647407)
            ·
              refine ⟨8675321231093090177471111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5783547487395393451647407 8675321231093090177471111)
              ·
                refine ⟨13012981846639635266206667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8675321231093090177471111 13012981846639635266206667)
                ·
                  refine ⟨19519472769959452899310001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13012981846639635266206667 19519472769959452899310001)
                  ·
                    refine ⟨14639604577469589674482501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19519472769959452899310001 14639604577469589674482501)
                    ·
                      refine ⟨2744925858275548063965469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14639604577469589674482501 2744925858275548063965469)
                      ·
                        rfl

theorem cell23_5345724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_5345724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345724 prefixEnd_5345724 := by exact prefixLift 5345724
  have htrace : WordTrace (prefixWord ++ tailWord_5345724) baseStart_5345724 baseEnd_5345724 := by
    simpa [prefixWord, tailWord_5345724, baseEnd_5345724] using wordTrace_append hprefix tailTrace_5345724
  have hstable : (prefixWord ++ tailWord_5345724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345724).length < 2 ^ (prefixWord ++ tailWord_5345724).sum := by decide
  have hdescent : baseEnd_5345724 < baseStart_5345724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345737 : List Nat := [1, 2, 1, 1, 2, 1, 4, 3, 3, 3, 2]
def baseStart_5345737 : Nat := 118140960795 + 5345737 * 2 ^ 59
def prefixEnd_5345737 : Nat := 4983230072969 + 3 ^ 40 * 5345737 * 2
def baseEnd_5345737 : Nat := 2744932533524056513102909

theorem tailTrace_5345737 : CollatzResearch.WordTrace tailWord_5345737 prefixEnd_5345737 2744932533524056513102909 := by
  unfold tailWord_5345737
  simp only [CollatzResearch.WordTrace]
  refine ⟨194975046234315303038723465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129983364156210202025815643 194975046234315303038723465)
  ·
    refine ⟨146231284675736477279042599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194975046234315303038723465 146231284675736477279042599)
    ·
      refine ⟨219346927013604715918563899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146231284675736477279042599 219346927013604715918563899)
      ·
        refine ⟨329020390520407073877845849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219346927013604715918563899 329020390520407073877845849)
        ·
          refine ⟨246765292890305305408384387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329020390520407073877845849 246765292890305305408384387)
          ·
            refine ⟨370147939335457958112576581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246765292890305305408384387 370147939335457958112576581)
            ·
              refine ⟨69402738625398367146108109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 370147939335457958112576581 69402738625398367146108109)
              ·
                refine ⟨26026026984524387679790541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69402738625398367146108109 26026026984524387679790541)
                ·
                  refine ⟨9759760119196645379921453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26026026984524387679790541 9759760119196645379921453)
                  ·
                    refine ⟨3659910044698742017470545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9759760119196645379921453 3659910044698742017470545)
                    ·
                      refine ⟨2744932533524056513102909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659910044698742017470545 2744932533524056513102909)
                      ·
                        rfl

theorem cell23_5345737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 3, 3, 3, 2].length) (baseStart_5345737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345737 prefixEnd_5345737 := by exact prefixLift 5345737
  have htrace : WordTrace (prefixWord ++ tailWord_5345737) baseStart_5345737 baseEnd_5345737 := by
    simpa [prefixWord, tailWord_5345737, baseEnd_5345737] using wordTrace_append hprefix tailTrace_5345737
  have hstable : (prefixWord ++ tailWord_5345737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345737).length < 2 ^ (prefixWord ++ tailWord_5345737).sum := by decide
  have hdescent : baseEnd_5345737 < baseStart_5345737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345754 : List Nat := [3, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2]
def baseStart_5345754 : Nat := 118140960795 + 5345754 * 2 ^ 59
def prefixEnd_5345754 : Nat := 4983230072969 + 3 ^ 40 * 5345754 * 2
def baseEnd_5345754 : Nat := 2744941262695182946590331

theorem tailTrace_5345754 : CollatzResearch.WordTrace tailWord_5345754 prefixEnd_5345754 2744941262695182946590331 := by
  unfold tailWord_5345754
  simp only [CollatzResearch.WordTrace]
  refine ⟨48743916568813428735523079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129983777516835809961394877 48743916568813428735523079)
  ·
    refine ⟨73115874853220143103284619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48743916568813428735523079 73115874853220143103284619)
    ·
      refine ⟨109673812279830214654926929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73115874853220143103284619 109673812279830214654926929)
      ·
        refine ⟨82255359209872660991195197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109673812279830214654926929 82255359209872660991195197)
        ·
          refine ⟨30845759703702247871698199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82255359209872660991195197 30845759703702247871698199)
          ·
            refine ⟨46268639555553371807547299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30845759703702247871698199 46268639555553371807547299)
            ·
              refine ⟨69402959333330057711320949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46268639555553371807547299 69402959333330057711320949)
              ·
                refine ⟨6506527437499692910436339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 69402959333330057711320949 6506527437499692910436339)
                ·
                  refine ⟨9759791156249539365654509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6506527437499692910436339 9759791156249539365654509)
                  ·
                    refine ⟨3659921683593577262120441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9759791156249539365654509 3659921683593577262120441)
                    ·
                      refine ⟨2744941262695182946590331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659921683593577262120441 2744941262695182946590331)
                      ·
                        rfl

theorem cell23_5345754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2].length) (baseStart_5345754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345754 prefixEnd_5345754 := by exact prefixLift 5345754
  have htrace : WordTrace (prefixWord ++ tailWord_5345754) baseStart_5345754 baseEnd_5345754 := by
    simpa [prefixWord, tailWord_5345754, baseEnd_5345754] using wordTrace_append hprefix tailTrace_5345754
  have hstable : (prefixWord ++ tailWord_5345754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345754).length < 2 ^ (prefixWord ++ tailWord_5345754).sum := by decide
  have hdescent : baseEnd_5345754 < baseStart_5345754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345762 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5345762 : Nat := 118140960795 + 5345762 * 2 ^ 59
def prefixEnd_5345762 : Nat := 4983230072969 + 3 ^ 40 * 5345762 * 2
def baseEnd_5345762 : Nat := 2744945370540418915290295

theorem tailTrace_5345762 : CollatzResearch.WordTrace tailWord_5345762 prefixEnd_5345762 2744945370540418915290295 := by
  unfold tailWord_5345762
  simp only [CollatzResearch.WordTrace]
  refine ⟨48743989514806183077095885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129983972039483154872255693 48743989514806183077095885)
  ·
    refine ⟨18278996068052318653910957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48743989514806183077095885 18278996068052318653910957)
    ·
      refine ⟨6854623525519619495216609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18278996068052318653910957 6854623525519619495216609)
      ·
        refine ⟨5140967644139714621412457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6854623525519619495216609 5140967644139714621412457)
        ·
          refine ⟨3855725733104785966059343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5140967644139714621412457 3855725733104785966059343)
          ·
            refine ⟨5783588599657178949089015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855725733104785966059343 5783588599657178949089015)
            ·
              refine ⟨8675382899485768423633523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5783588599657178949089015 8675382899485768423633523)
              ·
                refine ⟨13013074349228652635450285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8675382899485768423633523 13013074349228652635450285)
                ·
                  refine ⟨4879902880960744738293857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13013074349228652635450285 4879902880960744738293857)
                  ·
                    refine ⟨3659927160720558553720393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4879902880960744738293857 3659927160720558553720393)
                    ·
                      refine ⟨2744945370540418915290295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3659927160720558553720393 2744945370540418915290295)
                      ·
                        rfl

theorem cell23_5345762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5345762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345762 prefixEnd_5345762 := by exact prefixLift 5345762
  have htrace : WordTrace (prefixWord ++ tailWord_5345762) baseStart_5345762 baseEnd_5345762 := by
    simpa [prefixWord, tailWord_5345762, baseEnd_5345762] using wordTrace_append hprefix tailTrace_5345762
  have hstable : (prefixWord ++ tailWord_5345762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345762).length < 2 ^ (prefixWord ++ tailWord_5345762).sum := by decide
  have hdescent : baseEnd_5345762 < baseStart_5345762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345831 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 2, 2, 4]
def baseStart_5345831 : Nat := 118140960795 + 5345831 * 2 ^ 59
def prefixEnd_5345831 : Nat := 4983230072969 + 3 ^ 40 * 5345831 * 2
def baseEnd_5345831 : Nat := 2744980800705579145327477

theorem tailTrace_5345831 : CollatzResearch.WordTrace tailWord_5345831 prefixEnd_5345831 2744980800705579145327477 := by
  unfold tailWord_5345831
  simp only [CollatzResearch.WordTrace]
  refine ⟨194978474695974757092645347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129985649797316504728430231 194978474695974757092645347)
  ·
    refine ⟨292467712043962135638968021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194978474695974757092645347 292467712043962135638968021)
    ·
      refine ⟨6854712001030362554038313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 292467712043962135638968021 6854712001030362554038313)
      ·
        refine ⟨5141034000772771915528735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6854712001030362554038313 5141034000772771915528735)
        ·
          refine ⟨7711551001159157873293103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5141034000772771915528735 7711551001159157873293103)
          ·
            refine ⟨11567326501738736809939655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7711551001159157873293103 11567326501738736809939655)
            ·
              refine ⟨17350989752608105214909483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11567326501738736809939655 17350989752608105214909483)
              ·
                refine ⟨26026484628912157822364225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17350989752608105214909483 26026484628912157822364225)
                ·
                  refine ⟨19519863471684118366773169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26026484628912157822364225 19519863471684118366773169)
                  ·
                    refine ⟨14639897603763088775079877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19519863471684118366773169 14639897603763088775079877)
                    ·
                      refine ⟨2744980800705579145327477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14639897603763088775079877 2744980800705579145327477)
                      ·
                        rfl

theorem cell23_5345831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_5345831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345831 prefixEnd_5345831 := by exact prefixLift 5345831
  have htrace : WordTrace (prefixWord ++ tailWord_5345831) baseStart_5345831 baseEnd_5345831 := by
    simpa [prefixWord, tailWord_5345831, baseEnd_5345831] using wordTrace_append hprefix tailTrace_5345831
  have hstable : (prefixWord ++ tailWord_5345831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345831).length < 2 ^ (prefixWord ++ tailWord_5345831).sum := by decide
  have hdescent : baseEnd_5345831 < baseStart_5345831 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345834 : List Nat := [3, 1, 4, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_5345834 : Nat := 118140960795 + 5345834 * 2 ^ 59
def prefixEnd_5345834 : Nat := 4983230072969 + 3 ^ 40 * 5345834 * 2
def baseEnd_5345834 : Nat := 2744982341147542633589963

theorem tailTrace_5345834 : CollatzResearch.WordTrace tailWord_5345834 prefixEnd_5345834 2744982341147542633589963 := by
  unfold tailWord_5345834
  simp only [CollatzResearch.WordTrace]
  refine ⟨48744646028740972151251139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129985722743309259070003037 48744646028740972151251139)
  ·
    refine ⟨73116969043111458226876709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48744646028740972151251139 73116969043111458226876709)
    ·
      refine ⟨13709431695583398417539383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73116969043111458226876709 13709431695583398417539383)
      ·
        refine ⟨20564147543375097626309075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13709431695583398417539383 20564147543375097626309075)
        ·
          refine ⟨30846221315062646439463613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20564147543375097626309075 30846221315062646439463613)
          ·
            refine ⟨11567332993148492414798855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30846221315062646439463613 11567332993148492414798855)
            ·
              refine ⟨17350999489722738622198283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11567332993148492414798855 17350999489722738622198283)
              ·
                refine ⟨26026499234584107933297425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17350999489722738622198283 26026499234584107933297425)
                ·
                  refine ⟨19519874425938080949973069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26026499234584107933297425 19519874425938080949973069)
                  ·
                    refine ⟨7319952909726780356239901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19519874425938080949973069 7319952909726780356239901)
                    ·
                      refine ⟨2744982341147542633589963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7319952909726780356239901 2744982341147542633589963)
                      ·
                        rfl

theorem cell23_5345834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_5345834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345834 prefixEnd_5345834 := by exact prefixLift 5345834
  have htrace : WordTrace (prefixWord ++ tailWord_5345834) baseStart_5345834 baseEnd_5345834 := by
    simpa [prefixWord, tailWord_5345834, baseEnd_5345834] using wordTrace_append hprefix tailTrace_5345834
  have hstable : (prefixWord ++ tailWord_5345834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345834).length < 2 ^ (prefixWord ++ tailWord_5345834).sum := by decide
  have hdescent : baseEnd_5345834 < baseStart_5345834 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345874 : List Nat := [3, 2, 2, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_5345874 : Nat := 118140960795 + 5345874 * 2 ^ 59
def prefixEnd_5345874 : Nat := 4983230072969 + 3 ^ 40 * 5345874 * 2
def baseEnd_5345874 : Nat := 2745002880373722477089779

theorem tailTrace_5345874 : CollatzResearch.WordTrace tailWord_5345874 prefixEnd_5345874 2745002880373722477089779 := by
  unfold tailWord_5345874
  simp only [CollatzResearch.WordTrace]
  refine ⟨48745010758704743859115169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129986695356545983624307117 48745010758704743859115169)
  ·
    refine ⟨36558758069028557894336377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48745010758704743859115169 36558758069028557894336377)
    ·
      refine ⟨27419068551771418420752283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36558758069028557894336377 27419068551771418420752283)
      ·
        refine ⟨41128602827657127631128425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27419068551771418420752283 41128602827657127631128425)
        ·
          refine ⟨30846452120742845723346319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41128602827657127631128425 30846452120742845723346319)
          ·
            refine ⟨46269678181114268585019479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30846452120742845723346319 46269678181114268585019479)
            ·
              refine ⟨69404517271671402877529219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46269678181114268585019479 69404517271671402877529219)
              ·
                refine ⟨104106775907507104316293829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69404517271671402877529219 104106775907507104316293829)
                ·
                  refine ⟨19520020482657582059305093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104106775907507104316293829 19520020482657582059305093)
                  ·
                    refine ⟨3660003840498296636119705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19520020482657582059305093 3660003840498296636119705)
                    ·
                      refine ⟨2745002880373722477089779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3660003840498296636119705 2745002880373722477089779)
                      ·
                        rfl

theorem cell23_5345874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_5345874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345874 prefixEnd_5345874 := by exact prefixLift 5345874
  have htrace : WordTrace (prefixWord ++ tailWord_5345874) baseStart_5345874 baseEnd_5345874 := by
    simpa [prefixWord, tailWord_5345874, baseEnd_5345874] using wordTrace_append hprefix tailTrace_5345874
  have hstable : (prefixWord ++ tailWord_5345874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345874).length < 2 ^ (prefixWord ++ tailWord_5345874).sum := by decide
  have hdescent : baseEnd_5345874 < baseStart_5345874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345957 : List Nat := [1, 3, 1, 2, 1, 2, 1, 5, 1, 6]
def baseStart_5345957 : Nat := 118140960795 + 5345957 * 2 ^ 59
def prefixEnd_5345957 : Nat := 4983230072969 + 3 ^ 40 * 5345957 * 2
def baseEnd_5345957 : Nat := 915015166422681884117299

theorem tailTrace_5345957 : CollatzResearch.WordTrace tailWord_5345957 prefixEnd_5345957 915015166422681884117299 := by
  unfold tailWord_5345957
  simp only [CollatzResearch.WordTrace]
  refine ⟨194983070293518280611732125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129988713529012187074488083 194983070293518280611732125)
  ·
    refine ⟨73118651360069355229399547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194983070293518280611732125 73118651360069355229399547)
    ·
      refine ⟨109677977040104032844099321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73118651360069355229399547 109677977040104032844099321)
      ·
        refine ⟨82258482780078024633074491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109677977040104032844099321 82258482780078024633074491)
        ·
          refine ⟨123387724170117036949611737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82258482780078024633074491 123387724170117036949611737)
          ·
            refine ⟨92540793127587777712208803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123387724170117036949611737 92540793127587777712208803)
            ·
              refine ⟨138811189691381666568313205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92540793127587777712208803 138811189691381666568313205)
              ·
                refine ⟨13013549033567031240779363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 138811189691381666568313205 13013549033567031240779363)
                ·
                  refine ⟨19520323550350546861169045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13013549033567031240779363 19520323550350546861169045)
                  ·
                    refine ⟨915015166422681884117299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19520323550350546861169045 915015166422681884117299)
                    ·
                      rfl

theorem cell23_5345957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 5, 1, 6].length) (baseStart_5345957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345957 prefixEnd_5345957 := by exact prefixLift 5345957
  have htrace : WordTrace (prefixWord ++ tailWord_5345957) baseStart_5345957 baseEnd_5345957 := by
    simpa [prefixWord, tailWord_5345957, baseEnd_5345957] using wordTrace_append hprefix tailTrace_5345957
  have hstable : (prefixWord ++ tailWord_5345957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345957).length < 2 ^ (prefixWord ++ tailWord_5345957).sum := by decide
  have hdescent : baseEnd_5345957 < baseStart_5345957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5345984 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 5]
def baseStart_5345984 : Nat := 118140960795 + 5345984 * 2 ^ 59
def prefixEnd_5345984 : Nat := 4983230072969 + 3 ^ 40 * 5345984 * 2
def baseEnd_5345984 : Nat := 2745059363245717046714273

theorem tailTrace_5345984 : CollatzResearch.WordTrace tailWord_5345984 prefixEnd_5345984 2745059363245717046714273 := by
  unfold tailWord_5345984
  simp only [CollatzResearch.WordTrace]
  refine ⟨97492027532210232111482503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129989370042946976148643337 97492027532210232111482503)
  ·
    refine ⟨146238041298315348167223755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97492027532210232111482503 146238041298315348167223755)
    ·
      refine ⟨219357061947473022250835633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146238041298315348167223755 219357061947473022250835633)
      ·
        refine ⟨164517796460604766688126725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219357061947473022250835633 164517796460604766688126725)
        ·
          refine ⟨30847086836363393754023761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164517796460604766688126725 30847086836363393754023761)
          ·
            refine ⟨23135315127272545315517821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30847086836363393754023761 23135315127272545315517821)
            ·
              refine ⟨8675743172727204493319183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23135315127272545315517821 8675743172727204493319183)
              ·
                refine ⟨13013614759090806739978775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8675743172727204493319183 13013614759090806739978775)
                ·
                  refine ⟨19520422138636210109968163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13013614759090806739978775 19520422138636210109968163)
                  ·
                    refine ⟨29280633207954315164952245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19520422138636210109968163 29280633207954315164952245)
                    ·
                      refine ⟨2745059363245717046714273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29280633207954315164952245 2745059363245717046714273)
                      ·
                        rfl

theorem cell23_5345984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_5345984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5345984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5345984 prefixEnd_5345984 := by exact prefixLift 5345984
  have htrace : WordTrace (prefixWord ++ tailWord_5345984) baseStart_5345984 baseEnd_5345984 := by
    simpa [prefixWord, tailWord_5345984, baseEnd_5345984] using wordTrace_append hprefix tailTrace_5345984
  have hstable : (prefixWord ++ tailWord_5345984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5345984).length < 2 ^ (prefixWord ++ tailWord_5345984).sum := by decide
  have hdescent : baseEnd_5345984 < baseStart_5345984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5345984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346027 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 5]
def baseStart_5346027 : Nat := 118140960795 + 5346027 * 2 ^ 59
def prefixEnd_5346027 : Nat := 4983230072969 + 3 ^ 40 * 5346027 * 2
def baseEnd_5346027 : Nat := 2745081442913860378476575

theorem tailTrace_5346027 : CollatzResearch.WordTrace tailWord_5346027 prefixEnd_5346027 2745081442913860378476575 := by
  unfold tailWord_5346027
  simp only [CollatzResearch.WordTrace]
  refine ⟨194985623403264682566780335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129990415602176455044520223 194985623403264682566780335)
  ·
    refine ⟨292478435104897023850170503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194985623403264682566780335 292478435104897023850170503)
    ·
      refine ⟨438717652657345535775255755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292478435104897023850170503 438717652657345535775255755)
      ·
        refine ⟨658076478986018303662883633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438717652657345535775255755 658076478986018303662883633)
        ·
          refine ⟨493557359239513727747162725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 658076478986018303662883633 493557359239513727747162725)
          ·
            refine ⟨92542004857408823952593011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 493557359239513727747162725 92542004857408823952593011)
            ·
              refine ⟨138813007286113235928889517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92542004857408823952593011 138813007286113235928889517)
              ·
                refine ⟨52054877732292463473333569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138813007286113235928889517 52054877732292463473333569)
                ·
                  refine ⟨39041158299219347605000177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52054877732292463473333569 39041158299219347605000177)
                  ·
                    refine ⟨29280868724414510703750133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39041158299219347605000177 29280868724414510703750133)
                    ·
                      refine ⟨2745081442913860378476575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29280868724414510703750133 2745081442913860378476575)
                      ·
                        rfl

theorem cell23_5346027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 5].length) (baseStart_5346027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346027 prefixEnd_5346027 := by exact prefixLift 5346027
  have htrace : WordTrace (prefixWord ++ tailWord_5346027) baseStart_5346027 baseEnd_5346027 := by
    simpa [prefixWord, tailWord_5346027, baseEnd_5346027] using wordTrace_append hprefix tailTrace_5346027
  have hstable : (prefixWord ++ tailWord_5346027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346027).length < 2 ^ (prefixWord ++ tailWord_5346027).sum := by decide
  have hdescent : baseEnd_5346027 < baseStart_5346027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346074 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5]
def baseStart_5346074 : Nat := 118140960795 + 5346074 * 2 ^ 59
def prefixEnd_5346074 : Nat := 4983230072969 + 3 ^ 40 * 5346074 * 2
def baseEnd_5346074 : Nat := 2745105576504621694588859

theorem tailTrace_5346074 : CollatzResearch.WordTrace tailWord_5346074 prefixEnd_5346074 2745105576504621694588859 := by
  unfold tailWord_5346074
  simp only [CollatzResearch.WordTrace]
  refine ⟨48746834408523602398435319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 129991558422729606395827517 48746834408523602398435319)
  ·
    refine ⟨73120251612785403597652979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48746834408523602398435319 73120251612785403597652979)
    ·
      refine ⟨109680377419178105396479469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73120251612785403597652979 109680377419178105396479469)
      ·
        refine ⟨41130141532191789523679801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109680377419178105396479469 41130141532191789523679801)
        ·
          refine ⟨30847606149143842142759851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41130141532191789523679801 30847606149143842142759851)
          ·
            refine ⟨46271409223715763214139777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30847606149143842142759851 46271409223715763214139777)
            ·
              refine ⟨34703556917786822410604833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46271409223715763214139777 34703556917786822410604833)
              ·
                refine ⟨26027667688340116807953625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34703556917786822410604833 26027667688340116807953625)
                ·
                  refine ⟨19520750766255087605965219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26027667688340116807953625 19520750766255087605965219)
                  ·
                    refine ⟨29281126149382631408947829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19520750766255087605965219 29281126149382631408947829)
                    ·
                      refine ⟨2745105576504621694588859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29281126149382631408947829 2745105576504621694588859)
                      ·
                        rfl

theorem cell23_5346074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_5346074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346074 prefixEnd_5346074 := by exact prefixLift 5346074
  have htrace : WordTrace (prefixWord ++ tailWord_5346074) baseStart_5346074 baseEnd_5346074 := by
    simpa [prefixWord, tailWord_5346074, baseEnd_5346074] using wordTrace_append hprefix tailTrace_5346074
  have hstable : (prefixWord ++ tailWord_5346074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346074).length < 2 ^ (prefixWord ++ tailWord_5346074).sum := by decide
  have hdescent : baseEnd_5346074 < baseStart_5346074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346088 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 6, 2, 2]
def baseStart_5346088 : Nat := 118140960795 + 5346088 * 2 ^ 59
def prefixEnd_5346088 : Nat := 4983230072969 + 3 ^ 40 * 5346088 * 2
def baseEnd_5346088 : Nat := 2745112765233784639813795

theorem tailTrace_5346088 : CollatzResearch.WordTrace tailWord_5346088 prefixEnd_5346088 2745112765233784639813795 := by
  unfold tailWord_5346088
  simp only [CollatzResearch.WordTrace]
  refine ⟨97493924128021844992375459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129991898837362459989833945 97493924128021844992375459)
  ·
    refine ⟨146240886192032767488563189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97493924128021844992375459 146240886192032767488563189)
    ·
      refine ⟨13710083080503071952052799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146240886192032767488563189 13710083080503071952052799)
      ·
        refine ⟨20565124620754607928079199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13710083080503071952052799 20565124620754607928079199)
        ·
          refine ⟨30847686931131911892118799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20565124620754607928079199 30847686931131911892118799)
          ·
            refine ⟨46271530396697867838178199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30847686931131911892118799 46271530396697867838178199)
            ·
              refine ⟨69407295595046801757267299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46271530396697867838178199 69407295595046801757267299)
              ·
                refine ⟨104110943392570202635900949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69407295595046801757267299 104110943392570202635900949)
                ·
                  refine ⟨4880200471526728248557857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104110943392570202635900949 4880200471526728248557857)
                  ·
                    refine ⟨3660150353645046186418393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4880200471526728248557857 3660150353645046186418393)
                    ·
                      refine ⟨2745112765233784639813795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3660150353645046186418393 2745112765233784639813795)
                      ·
                        rfl

theorem cell23_5346088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_5346088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346088 prefixEnd_5346088 := by exact prefixLift 5346088
  have htrace : WordTrace (prefixWord ++ tailWord_5346088) baseStart_5346088 baseEnd_5346088 := by
    simpa [prefixWord, tailWord_5346088, baseEnd_5346088] using wordTrace_append hprefix tailTrace_5346088
  have hstable : (prefixWord ++ tailWord_5346088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346088).length < 2 ^ (prefixWord ++ tailWord_5346088).sum := by decide
  have hdescent : baseEnd_5346088 < baseStart_5346088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346107 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 1, 13]
def baseStart_5346107 : Nat := 118140960795 + 5346107 * 2 ^ 59
def prefixEnd_5346107 : Nat := 4983230072969 + 3 ^ 40 * 5346107 * 2
def baseEnd_5346107 : Nat := 915040840455406688492069

theorem tailTrace_5346107 : CollatzResearch.WordTrace tailWord_5346107 prefixEnd_5346107 915040840455406688492069 := by
  unfold tailWord_5346107
  simp only [CollatzResearch.WordTrace]
  refine ⟨194988541242974856229692575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129992360828649904153128383 194988541242974856229692575)
  ·
    refine ⟨292482811864462284344538863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194988541242974856229692575 292482811864462284344538863)
    ·
      refine ⟨438724217796693426516808295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292482811864462284344538863 438724217796693426516808295)
      ·
        refine ⟨658086326695040139775212443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438724217796693426516808295 658086326695040139775212443)
        ·
          refine ⟨987129490042560209662818665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658086326695040139775212443 987129490042560209662818665)
          ·
            refine ⟨740347117531920157247113999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 987129490042560209662818665 740347117531920157247113999)
            ·
              refine ⟨1110520676297880235870670999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740347117531920157247113999 1110520676297880235870670999)
              ·
                refine ⟨1665781014446820353806006499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1110520676297880235870670999 1665781014446820353806006499)
                ·
                  refine ⟨2498671521670230530709009749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1665781014446820353806006499 2498671521670230530709009749)
                  ·
                    refine ⟨915040840455406688492069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 13 2498671521670230530709009749 915040840455406688492069)
                    ·
                      rfl

theorem cell23_5346107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 13].length) (baseStart_5346107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346107 prefixEnd_5346107 := by exact prefixLift 5346107
  have htrace : WordTrace (prefixWord ++ tailWord_5346107) baseStart_5346107 baseEnd_5346107 := by
    simpa [prefixWord, tailWord_5346107, baseEnd_5346107] using wordTrace_append hprefix tailTrace_5346107
  have hstable : (prefixWord ++ tailWord_5346107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346107).length < 2 ^ (prefixWord ++ tailWord_5346107).sum := by decide
  have hdescent : baseEnd_5346107 < baseStart_5346107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346111 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 7]
def baseStart_5346111 : Nat := 118140960795 + 5346111 * 2 ^ 59
def prefixEnd_5346111 : Nat := 4983230072969 + 3 ^ 40 * 5346111 * 2
def baseEnd_5346111 : Nat := 305013841698759783314021

theorem tailTrace_5346111 : CollatzResearch.WordTrace tailWord_5346111 prefixEnd_5346111 305013841698759783314021 := by
  unfold tailWord_5346111
  simp only [CollatzResearch.WordTrace]
  refine ⟨194988687134960364912838187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129992458089973576608558791 194988687134960364912838187)
  ·
    refine ⟨292483030702440547369257281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194988687134960364912838187 292483030702440547369257281)
    ·
      refine ⟨219362273026830410526942961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292483030702440547369257281 219362273026830410526942961)
      ·
        refine ⟨164521704770122807895207221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219362273026830410526942961 164521704770122807895207221)
        ·
          refine ⟨15423909822199013240175677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164521704770122807895207221 15423909822199013240175677)
          ·
            refine ⟨5783966183324629965065879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15423909822199013240175677 5783966183324629965065879)
            ·
              refine ⟨8675949274986944947598819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5783966183324629965065879 8675949274986944947598819)
              ·
                refine ⟨13013923912480417421398229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8675949274986944947598819 13013923912480417421398229)
                ·
                  refine ⟨305013841698759783314021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13013923912480417421398229 305013841698759783314021)
                  ·
                    rfl

theorem cell23_5346111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 7].length) (baseStart_5346111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346111 prefixEnd_5346111 := by exact prefixLift 5346111
  have htrace : WordTrace (prefixWord ++ tailWord_5346111) baseStart_5346111 baseEnd_5346111 := by
    simpa [prefixWord, tailWord_5346111, baseEnd_5346111] using wordTrace_append hprefix tailTrace_5346111
  have hstable : (prefixWord ++ tailWord_5346111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346111).length < 2 ^ (prefixWord ++ tailWord_5346111).sum := by decide
  have hdescent : baseEnd_5346111 < baseStart_5346111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346116 : List Nat := [2, 3, 4, 2, 2, 1, 2, 1, 2, 1, 3]
def baseStart_5346116 : Nat := 118140960795 + 5346116 * 2 ^ 59
def prefixEnd_5346116 : Nat := 4983230072969 + 3 ^ 40 * 5346116 * 2
def baseEnd_5346116 : Nat := 2745127142692110530263667

theorem tailTrace_5346116 : CollatzResearch.WordTrace tailWord_5346116 prefixEnd_5346116 2745127142692110530263667 := by
  unfold tailWord_5346116
  simp only [CollatzResearch.WordTrace]
  refine ⟨97494434749971125383385101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129992579666628167177846801 97494434749971125383385101)
  ·
    refine ⟨36560413031239172018769413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97494434749971125383385101 36560413031239172018769413)
    ·
      refine ⟨6855077443357344753519265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36560413031239172018769413 6855077443357344753519265)
      ·
        refine ⟨5141308082518008565139449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6855077443357344753519265 5141308082518008565139449)
        ·
          refine ⟨3855981061888506423854587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5141308082518008565139449 3855981061888506423854587)
          ·
            refine ⟨5783971592832759635781881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3855981061888506423854587 5783971592832759635781881)
            ·
              refine ⟨4337978694624569726836411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5783971592832759635781881 4337978694624569726836411)
              ·
                refine ⟨6506968041936854590254617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4337978694624569726836411 6506968041936854590254617)
                ·
                  refine ⟨4880226031452640942690963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6506968041936854590254617 4880226031452640942690963)
                  ·
                    refine ⟨7320339047178961414036445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4880226031452640942690963 7320339047178961414036445)
                    ·
                      refine ⟨2745127142692110530263667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7320339047178961414036445 2745127142692110530263667)
                      ·
                        rfl

theorem cell23_5346116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_5346116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346116 prefixEnd_5346116 := by exact prefixLift 5346116
  have htrace : WordTrace (prefixWord ++ tailWord_5346116) baseStart_5346116 baseEnd_5346116 := by
    simpa [prefixWord, tailWord_5346116, baseEnd_5346116] using wordTrace_append hprefix tailTrace_5346116
  have hstable : (prefixWord ++ tailWord_5346116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346116).length < 2 ^ (prefixWord ++ tailWord_5346116).sum := by decide
  have hdescent : baseEnd_5346116 < baseStart_5346116 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346161 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 2, 1, 4]
def baseStart_5346161 : Nat := 118140960795 + 5346161 * 2 ^ 59
def prefixEnd_5346161 : Nat := 4983230072969 + 3 ^ 40 * 5346161 * 2
def baseEnd_5346161 : Nat := 2745150249321562854200959

theorem tailTrace_5346161 : CollatzResearch.WordTrace tailWord_5346161 prefixEnd_5346161 2745150249321562854200959 := by
  unfold tailWord_5346161
  simp only [CollatzResearch.WordTrace]
  refine ⟨194990510784779223452158337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129993673856519482301438891 194990510784779223452158337)
  ·
    refine ⟨146242883088584417589118753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194990510784779223452158337 146242883088584417589118753)
    ·
      refine ⟨109682162316438313191839065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146242883088584417589118753 109682162316438313191839065)
      ·
        refine ⟨82261621737328734893879299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109682162316438313191839065 82261621737328734893879299)
        ·
          refine ⟨123392432605993102340818949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82261621737328734893879299 123392432605993102340818949)
          ·
            refine ⟨23136081113623706688903553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123392432605993102340818949 23136081113623706688903553)
            ·
              refine ⟨17352060835217780016677665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23136081113623706688903553 17352060835217780016677665)
              ·
                refine ⟨13014045626413335012508249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17352060835217780016677665 13014045626413335012508249)
                ·
                  refine ⟨9760534219810001259381187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13014045626413335012508249 9760534219810001259381187)
                  ·
                    refine ⟨14640801329715001889071781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9760534219810001259381187 14640801329715001889071781)
                    ·
                      refine ⟨2745150249321562854200959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14640801329715001889071781 2745150249321562854200959)
                      ·
                        rfl

theorem cell23_5346161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_5346161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346161 prefixEnd_5346161 := by exact prefixLift 5346161
  have htrace : WordTrace (prefixWord ++ tailWord_5346161) baseStart_5346161 baseEnd_5346161 := by
    simpa [prefixWord, tailWord_5346161, baseEnd_5346161] using wordTrace_append hprefix tailTrace_5346161
  have hstable : (prefixWord ++ tailWord_5346161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346161).length < 2 ^ (prefixWord ++ tailWord_5346161).sum := by decide
  have hdescent : baseEnd_5346161 < baseStart_5346161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346205 : List Nat := [1, 4, 2, 1, 2, 1, 4, 3, 1, 4]
def baseStart_5346205 : Nat := 118140960795 + 5346205 * 2 ^ 59
def prefixEnd_5346205 : Nat := 4983230072969 + 3 ^ 40 * 5346205 * 2
def baseEnd_5346205 : Nat := 915057614156786894016919

theorem tailTrace_5346205 : CollatzResearch.WordTrace tailWord_5346205 prefixEnd_5346205 915057614156786894016919 := by
  unfold tailWord_5346205
  simp only [CollatzResearch.WordTrace]
  refine ⟨194992115596619818966760069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129994743731079879311173379 194992115596619818966760069)
  ·
    refine ⟨36561021674366216056267513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 194992115596619818966760069 36561021674366216056267513)
    ·
      refine ⟨27420766255774662042200635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36561021674366216056267513 27420766255774662042200635)
      ·
        refine ⟨41131149383661993063300953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27420766255774662042200635 41131149383661993063300953)
        ·
          refine ⟨30848362037746494797475715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41131149383661993063300953 30848362037746494797475715)
          ·
            refine ⟨46272543056619742196213573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30848362037746494797475715 46272543056619742196213573)
            ·
              refine ⟨8676101823116201661790045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46272543056619742196213573 8676101823116201661790045)
              ·
                refine ⟨3253538183668575623171267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8676101823116201661790045 3253538183668575623171267)
                ·
                  refine ⟨4880307275502863434756901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3253538183668575623171267 4880307275502863434756901)
                  ·
                    refine ⟨915057614156786894016919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4880307275502863434756901 915057614156786894016919)
                    ·
                      rfl

theorem cell23_5346205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_5346205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346205 prefixEnd_5346205 := by exact prefixLift 5346205
  have htrace : WordTrace (prefixWord ++ tailWord_5346205) baseStart_5346205 baseEnd_5346205 := by
    simpa [prefixWord, tailWord_5346205, baseEnd_5346205] using wordTrace_append hprefix tailTrace_5346205
  have hstable : (prefixWord ++ tailWord_5346205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346205).length < 2 ^ (prefixWord ++ tailWord_5346205).sum := by decide
  have hdescent : baseEnd_5346205 < baseStart_5346205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346238 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_5346238 : Nat := 118140960795 + 5346238 * 2 ^ 59
def prefixEnd_5346238 : Nat := 4983230072969 + 3 ^ 40 * 5346238 * 2
def baseEnd_5346238 : Nat := 2745189787331959052938105

theorem tailTrace_5346238 : CollatzResearch.WordTrace tailWord_5346238 prefixEnd_5346238 2745189787331959052938105 := by
  unfold tailWord_5346238
  simp only [CollatzResearch.WordTrace]
  refine ⟨24374164900687533200338921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129995546137000177068474245 24374164900687533200338921)
  ·
    refine ⟨18280623675515649900254191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24374164900687533200338921 18280623675515649900254191)
    ·
      refine ⟨27420935513273474850381287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18280623675515649900254191 27420935513273474850381287)
      ·
        refine ⟨41131403269910212275571931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27420935513273474850381287 41131403269910212275571931)
        ·
          refine ⟨61697104904865318413357897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41131403269910212275571931 61697104904865318413357897)
          ·
            refine ⟨46272828678648988810018423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61697104904865318413357897 46272828678648988810018423)
            ·
              refine ⟨69409243017973483215027635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46272828678648988810018423 69409243017973483215027635)
              ·
                refine ⟨104113864526960224822541453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69409243017973483215027635 104113864526960224822541453)
                ·
                  refine ⟨39042699197610084308453045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104113864526960224822541453 39042699197610084308453045)
                  ·
                    refine ⟨3660253049775945403917473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39042699197610084308453045 3660253049775945403917473)
                    ·
                      refine ⟨2745189787331959052938105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3660253049775945403917473 2745189787331959052938105)
                      ·
                        rfl

theorem cell23_5346238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_5346238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346238 prefixEnd_5346238 := by exact prefixLift 5346238
  have htrace : WordTrace (prefixWord ++ tailWord_5346238) baseStart_5346238 baseEnd_5346238 := by
    simpa [prefixWord, tailWord_5346238, baseEnd_5346238] using wordTrace_append hprefix tailTrace_5346238
  have hstable : (prefixWord ++ tailWord_5346238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346238).length < 2 ^ (prefixWord ++ tailWord_5346238).sum := by decide
  have hdescent : baseEnd_5346238 < baseStart_5346238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346279 : List Nat := [1, 1, 5, 2, 2, 2, 3, 2, 1, 1, 3]
def baseStart_5346279 : Nat := 118140960795 + 5346279 * 2 ^ 59
def prefixEnd_5346279 : Nat := 4983230072969 + 3 ^ 40 * 5346279 * 2
def baseEnd_5346279 : Nat := 2745210840038793392525417

theorem tailTrace_5346279 : CollatzResearch.WordTrace tailWord_5346279 prefixEnd_5346279 2745210840038793392525417 := by
  unfold tailWord_5346279
  simp only [CollatzResearch.WordTrace]
  refine ⟨194994814598351729604953891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129996543065567819736635927 194994814598351729604953891)
  ·
    refine ⟨292492221897527594407430837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194994814598351729604953891 292492221897527594407430837)
    ·
      refine ⟨27421145802893211975696641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 292492221897527594407430837 27421145802893211975696641)
      ·
        refine ⟨20565859352169908981772481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27421145802893211975696641 20565859352169908981772481)
        ·
          refine ⟨15424394514127431736329361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20565859352169908981772481 15424394514127431736329361)
          ·
            refine ⟨11568295885595573802247021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15424394514127431736329361 11568295885595573802247021)
            ·
              refine ⟨4338110957098340175842633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11568295885595573802247021 4338110957098340175842633)
              ·
                refine ⟨3253583217823755131881975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4338110957098340175842633 3253583217823755131881975)
                ·
                  refine ⟨4880374826735632697822963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3253583217823755131881975 4880374826735632697822963)
                  ·
                    refine ⟨7320562240103449046734445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4880374826735632697822963 7320562240103449046734445)
                    ·
                      refine ⟨2745210840038793392525417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7320562240103449046734445 2745210840038793392525417)
                      ·
                        rfl

theorem cell23_5346279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 1, 1, 3].length) (baseStart_5346279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346279 prefixEnd_5346279 := by exact prefixLift 5346279
  have htrace : WordTrace (prefixWord ++ tailWord_5346279) baseStart_5346279 baseEnd_5346279 := by
    simpa [prefixWord, tailWord_5346279, baseEnd_5346279] using wordTrace_append hprefix tailTrace_5346279
  have hstable : (prefixWord ++ tailWord_5346279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346279).length < 2 ^ (prefixWord ++ tailWord_5346279).sum := by decide
  have hdescent : baseEnd_5346279 < baseStart_5346279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346305 : List Nat := [1, 2, 4, 1, 2, 2, 3, 2, 1, 2, 3]
def baseStart_5346305 : Nat := 118140960795 + 5346305 * 2 ^ 59
def prefixEnd_5346305 : Nat := 4983230072969 + 3 ^ 40 * 5346305 * 2
def baseEnd_5346305 : Nat := 2745224190535810290800297

theorem tailTrace_5346305 : CollatzResearch.WordTrace tailWord_5346305 prefixEnd_5346305 2745224190535810290800297 := by
  unfold tailWord_5346305
  simp only [CollatzResearch.WordTrace]
  refine ⟨194995762896257536045400369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129997175264171690696933579 194995762896257536045400369)
  ·
    refine ⟨146246822172193152034050277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194995762896257536045400369 146246822172193152034050277)
    ·
      refine ⟨27421279157286216006384427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146246822172193152034050277 27421279157286216006384427)
      ·
        refine ⟨41131918735929324009576641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27421279157286216006384427 41131918735929324009576641)
        ·
          refine ⟨30848939051946993007182481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41131918735929324009576641 30848939051946993007182481)
          ·
            refine ⟨23136704288960244755386861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30848939051946993007182481 23136704288960244755386861)
            ·
              refine ⟨8676264108360091783270073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23136704288960244755386861 8676264108360091783270073)
              ·
                refine ⟨6507198081270068837452555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8676264108360091783270073 6507198081270068837452555)
                ·
                  refine ⟨9760797121905103256178833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6507198081270068837452555 9760797121905103256178833)
                  ·
                    refine ⟨7320597841428827442134125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9760797121905103256178833 7320597841428827442134125)
                    ·
                      refine ⟨2745224190535810290800297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7320597841428827442134125 2745224190535810290800297)
                      ·
                        rfl

theorem cell23_5346305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 1, 2, 3].length) (baseStart_5346305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346305 prefixEnd_5346305 := by exact prefixLift 5346305
  have htrace : WordTrace (prefixWord ++ tailWord_5346305) baseStart_5346305 baseEnd_5346305 := by
    simpa [prefixWord, tailWord_5346305, baseEnd_5346305] using wordTrace_append hprefix tailTrace_5346305
  have hstable : (prefixWord ++ tailWord_5346305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346305).length < 2 ^ (prefixWord ++ tailWord_5346305).sum := by decide
  have hdescent : baseEnd_5346305 < baseStart_5346305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346318 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_5346318 : Nat := 118140960795 + 5346318 * 2 ^ 59
def prefixEnd_5346318 : Nat := 4983230072969 + 3 ^ 40 * 5346318 * 2
def baseEnd_5346318 : Nat := 2745230865784318739937737

theorem tailTrace_5346318 : CollatzResearch.WordTrace tailWord_5346318 prefixEnd_5346318 2745230865784318739937737 := by
  unfold tailWord_5346318
  simp only [CollatzResearch.WordTrace]
  refine ⟨24374529630651304908202951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 129997491363473626177082405 24374529630651304908202951)
  ·
    refine ⟨36561794445976957362304427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24374529630651304908202951 36561794445976957362304427)
    ·
      refine ⟨54842691668965436043456641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36561794445976957362304427 54842691668965436043456641)
      ·
        refine ⟨41132018751724077032592481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54842691668965436043456641 41132018751724077032592481)
        ·
          refine ⟨30849014063793057774444361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41132018751724077032592481 30849014063793057774444361)
          ·
            refine ⟨23136760547844793330833271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30849014063793057774444361 23136760547844793330833271)
            ·
              refine ⟨34705140821767189996249907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23136760547844793330833271 34705140821767189996249907)
              ·
                refine ⟨52057711232650784994374861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34705140821767189996249907 52057711232650784994374861)
                ·
                  refine ⟨19521641712244044372890573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52057711232650784994374861 19521641712244044372890573)
                  ·
                    refine ⟨7320615642091516639833965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19521641712244044372890573 7320615642091516639833965)
                    ·
                      refine ⟨2745230865784318739937737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7320615642091516639833965 2745230865784318739937737)
                      ·
                        rfl

theorem cell23_5346318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_5346318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346318 prefixEnd_5346318 := by exact prefixLift 5346318
  have htrace : WordTrace (prefixWord ++ tailWord_5346318) baseStart_5346318 baseEnd_5346318 := by
    simpa [prefixWord, tailWord_5346318, baseEnd_5346318] using wordTrace_append hprefix tailTrace_5346318
  have hstable : (prefixWord ++ tailWord_5346318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346318).length < 2 ^ (prefixWord ++ tailWord_5346318).sum := by decide
  have hdescent : baseEnd_5346318 < baseStart_5346318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346335 : List Nat := [1, 1, 2, 4, 1, 3, 1, 4, 2, 1, 3]
def baseStart_5346335 : Nat := 118140960795 + 5346335 * 2 ^ 59
def prefixEnd_5346335 : Nat := 4983230072969 + 3 ^ 40 * 5346335 * 2
def baseEnd_5346335 : Nat := 2745239594955445173425159

theorem tailTrace_5346335 : CollatzResearch.WordTrace tailWord_5346335 prefixEnd_5346335 2745239594955445173425159 := by
  unfold tailWord_5346335
  simp only [CollatzResearch.WordTrace]
  refine ⟨194996857086148851168992459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129997904724099234112661639 194996857086148851168992459)
  ·
    refine ⟨292495285629223276753488689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194996857086148851168992459 292495285629223276753488689)
    ·
      refine ⟨219371464221917457565116517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292495285629223276753488689 219371464221917457565116517)
      ·
        refine ⟨41132149541609523293459347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219371464221917457565116517 41132149541609523293459347)
        ·
          refine ⟨61698224312414284940189021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41132149541609523293459347 61698224312414284940189021)
          ·
            refine ⟨23136834117155356852570883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61698224312414284940189021 23136834117155356852570883)
            ·
              refine ⟨34705251175733035278856325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23136834117155356852570883 34705251175733035278856325)
              ·
                refine ⟨6507234595449944114785561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34705251175733035278856325 6507234595449944114785561)
                ·
                  refine ⟨4880425946587458086089171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6507234595449944114785561 4880425946587458086089171)
                  ·
                    refine ⟨7320638919881187129133757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4880425946587458086089171 7320638919881187129133757)
                    ·
                      refine ⟨2745239594955445173425159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7320638919881187129133757 2745239594955445173425159)
                      ·
                        rfl

theorem cell23_5346335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_5346335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346335 prefixEnd_5346335 := by exact prefixLift 5346335
  have htrace : WordTrace (prefixWord ++ tailWord_5346335) baseStart_5346335 baseEnd_5346335 := by
    simpa [prefixWord, tailWord_5346335, baseEnd_5346335] using wordTrace_append hprefix tailTrace_5346335
  have hstable : (prefixWord ++ tailWord_5346335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346335).length < 2 ^ (prefixWord ++ tailWord_5346335).sum := by decide
  have hdescent : baseEnd_5346335 < baseStart_5346335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346336 : List Nat := [2, 1, 1, 7, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5346336 : Nat := 118140960795 + 5346336 * 2 ^ 59
def prefixEnd_5346336 : Nat := 4983230072969 + 3 ^ 40 * 5346336 * 2
def baseEnd_5346336 : Nat := 2745240108436099669512655

theorem tailTrace_5346336 : CollatzResearch.WordTrace tailWord_5346336 prefixEnd_5346336 2745240108436099669512655 := by
  unfold tailWord_5346336
  simp only [CollatzResearch.WordTrace]
  refine ⟨97498446779572614169889431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129997929039430152226519241 97498446779572614169889431)
  ·
    refine ⟨146247670169358921254834147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97498446779572614169889431 146247670169358921254834147)
    ·
      refine ⟨219371505254038381882251221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146247670169358921254834147 219371505254038381882251221)
      ·
        refine ⟨5141519654391524575365263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 219371505254038381882251221 5141519654391524575365263)
        ·
          refine ⟨7712279481587286863047895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5141519654391524575365263 7712279481587286863047895)
          ·
            refine ⟨11568419222380930294571843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7712279481587286863047895 11568419222380930294571843)
            ·
              refine ⟨17352628833571395441857765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11568419222380930294571843 17352628833571395441857765)
              ·
                refine ⟨3253617906294636645348331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17352628833571395441857765 3253617906294636645348331)
                ·
                  refine ⟨4880426859441954968022497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3253617906294636645348331 4880426859441954968022497)
                  ·
                    refine ⟨3660320144581466226016873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4880426859441954968022497 3660320144581466226016873)
                    ·
                      refine ⟨2745240108436099669512655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3660320144581466226016873 2745240108436099669512655)
                      ·
                        rfl

theorem cell23_5346336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5346336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346336 prefixEnd_5346336 := by exact prefixLift 5346336
  have htrace : WordTrace (prefixWord ++ tailWord_5346336) baseStart_5346336 baseEnd_5346336 := by
    simpa [prefixWord, tailWord_5346336, baseEnd_5346336] using wordTrace_append hprefix tailTrace_5346336
  have hstable : (prefixWord ++ tailWord_5346336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346336).length < 2 ^ (prefixWord ++ tailWord_5346336).sum := by decide
  have hdescent : baseEnd_5346336 < baseStart_5346336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346341 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 1, 5, 4]
def baseStart_5346341 : Nat := 118140960795 + 5346341 * 2 ^ 59
def prefixEnd_5346341 : Nat := 4983230072969 + 3 ^ 40 * 5346341 * 2
def baseEnd_5346341 : Nat := 2745242675839372149950131

theorem tailTrace_5346341 : CollatzResearch.WordTrace tailWord_5346341 prefixEnd_5346341 2745242675839372149950131 := by
  unfold tailWord_5346341
  simp only [CollatzResearch.WordTrace]
  refine ⟨194997075924127114193710877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129998050616084742795807251 194997075924127114193710877)
  ·
    refine ⟨73123903471547667822641579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 194997075924127114193710877 73123903471547667822641579)
    ·
      refine ⟨109685855207321501733962369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73123903471547667822641579 109685855207321501733962369)
      ·
        refine ⟨82264391405491126300471777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109685855207321501733962369 82264391405491126300471777)
        ·
          refine ⟨61698293554118344725353833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82264391405491126300471777 61698293554118344725353833)
          ·
            refine ⟨46273720165588758544015375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61698293554118344725353833 46273720165588758544015375)
            ·
              refine ⟨69410580248383137816023063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46273720165588758544015375 69410580248383137816023063)
              ·
                refine ⟨104115870372574706724034595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69410580248383137816023063 104115870372574706724034595)
                ·
                  refine ⟨156173805558862060086051893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104115870372574706724034595 156173805558862060086051893)
                  ·
                    refine ⟨14641294271143318133067365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 156173805558862060086051893 14641294271143318133067365)
                    ·
                      refine ⟨2745242675839372149950131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14641294271143318133067365 2745242675839372149950131)
                      ·
                        rfl

theorem cell23_5346341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_5346341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346341 prefixEnd_5346341 := by exact prefixLift 5346341
  have htrace : WordTrace (prefixWord ++ tailWord_5346341) baseStart_5346341 baseEnd_5346341 := by
    simpa [prefixWord, tailWord_5346341, baseEnd_5346341] using wordTrace_append hprefix tailTrace_5346341
  have hstable : (prefixWord ++ tailWord_5346341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346341).length < 2 ^ (prefixWord ++ tailWord_5346341).sum := by decide
  have hdescent : baseEnd_5346341 < baseStart_5346341 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346371 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 4]
def baseStart_5346371 : Nat := 118140960795 + 5346371 * 2 ^ 59
def prefixEnd_5346371 : Nat := 4983230072969 + 3 ^ 40 * 5346371 * 2
def baseEnd_5346371 : Nat := 2745258080259007032574993

theorem tailTrace_5346371 : CollatzResearch.WordTrace tailWord_5346371 prefixEnd_5346371 2745258080259007032574993 := by
  unfold tailWord_5346371
  simp only [CollatzResearch.WordTrace]
  refine ⟨194998170114018429317302967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129998780076012286211535311 194998170114018429317302967)
  ·
    refine ⟨292497255171027643975954451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194998170114018429317302967 292497255171027643975954451)
    ·
      refine ⟨438745882756541465963931677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292497255171027643975954451 438745882756541465963931677)
      ·
        refine ⟨164529706033703049736474379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438745882756541465963931677 164529706033703049736474379)
        ·
          refine ⟨246794559050554574604711569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164529706033703049736474379 246794559050554574604711569)
          ·
            refine ⟨185095919287915930953533677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246794559050554574604711569 185095919287915930953533677)
            ·
              refine ⟨69410969732968474107575129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185095919287915930953533677 69410969732968474107575129)
              ·
                refine ⟨52058227299726355580681347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69410969732968474107575129 52058227299726355580681347)
                ·
                  refine ⟨78087340949589533371022021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52058227299726355580681347 78087340949589533371022021)
                  ·
                    refine ⟨14641376428048037507066629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78087340949589533371022021 14641376428048037507066629)
                    ·
                      refine ⟨2745258080259007032574993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14641376428048037507066629 2745258080259007032574993)
                      ·
                        rfl

theorem cell23_5346371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 4, 4].length) (baseStart_5346371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346371 prefixEnd_5346371 := by exact prefixLift 5346371
  have htrace : WordTrace (prefixWord ++ tailWord_5346371) baseStart_5346371 baseEnd_5346371 := by
    simpa [prefixWord, tailWord_5346371, baseEnd_5346371] using wordTrace_append hprefix tailTrace_5346371
  have hstable : (prefixWord ++ tailWord_5346371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346371).length < 2 ^ (prefixWord ++ tailWord_5346371).sum := by decide
  have hdescent : baseEnd_5346371 < baseStart_5346371 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346375 : List Nat := [1, 1, 4, 1, 3, 2, 2, 2, 1, 4, 2]
def baseStart_5346375 : Nat := 118140960795 + 5346375 * 2 ^ 59
def prefixEnd_5346375 : Nat := 4983230072969 + 3 ^ 40 * 5346375 * 2
def baseEnd_5346375 : Nat := 2745260134181625016924975

theorem tailTrace_5346375 : CollatzResearch.WordTrace tailWord_5346375 prefixEnd_5346375 2745260134181625016924975 := by
  unfold tailWord_5346375
  simp only [CollatzResearch.WordTrace]
  refine ⟨194998316006003938000448579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129998877337335958666965719 194998316006003938000448579)
  ·
    refine ⟨292497474009005907000672869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 194998316006003938000448579 292497474009005907000672869)
    ·
      refine ⟨54843276376688607562626163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292497474009005907000672869 54843276376688607562626163)
      ·
        refine ⟨82264914565032911343939245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54843276376688607562626163 82264914565032911343939245)
        ·
          refine ⟨30849342961887341753977217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82264914565032911343939245 30849342961887341753977217)
          ·
            refine ⟨23137007221415506315482913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30849342961887341753977217 23137007221415506315482913)
            ·
              refine ⟨17352755416061629736612185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23137007221415506315482913 17352755416061629736612185)
              ·
                refine ⟨13014566562046222302459139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17352755416061629736612185 13014566562046222302459139)
                ·
                  refine ⟨19521849843069333453688709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13014566562046222302459139 19521849843069333453688709)
                  ·
                    refine ⟨3660346845575500022566633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19521849843069333453688709 3660346845575500022566633)
                    ·
                      refine ⟨2745260134181625016924975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3660346845575500022566633 2745260134181625016924975)
                      ·
                        rfl

theorem cell23_5346375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 2, 1, 4, 2].length) (baseStart_5346375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346375 prefixEnd_5346375 := by exact prefixLift 5346375
  have htrace : WordTrace (prefixWord ++ tailWord_5346375) baseStart_5346375 baseEnd_5346375 := by
    simpa [prefixWord, tailWord_5346375, baseEnd_5346375] using wordTrace_append hprefix tailTrace_5346375
  have hstable : (prefixWord ++ tailWord_5346375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346375).length < 2 ^ (prefixWord ++ tailWord_5346375).sum := by decide
  have hdescent : baseEnd_5346375 < baseStart_5346375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346388 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_5346388 : Nat := 118140960795 + 5346388 * 2 ^ 59
def prefixEnd_5346388 : Nat := 4983230072969 + 3 ^ 40 * 5346388 * 2
def baseEnd_5346388 : Nat := 2745266809430133466062415

theorem tailTrace_5346388 : CollatzResearch.WordTrace tailWord_5346388 prefixEnd_5346388 2745266809430133466062415 := by
  unfold tailWord_5346388
  simp only [CollatzResearch.WordTrace]
  refine ⟨97499395077478420610335909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 129999193436637894147114545 97499395077478420610335909)
  ·
    refine ⟨18281136577027203864437983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97499395077478420610335909 18281136577027203864437983)
    ·
      refine ⟨27421704865540805796656975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18281136577027203864437983 27421704865540805796656975)
      ·
        refine ⟨41132557298311208694985463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27421704865540805796656975 41132557298311208694985463)
        ·
          refine ⟨61698835947466813042478195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41132557298311208694985463 61698835947466813042478195)
          ·
            refine ⟨92548253921200219563717293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61698835947466813042478195 92548253921200219563717293)
            ·
              refine ⟨34705595220450082336393985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 92548253921200219563717293 34705595220450082336393985)
              ·
                refine ⟨26029196415337561752295489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34705595220450082336393985 26029196415337561752295489)
                ·
                  refine ⟨19521897311503171314221617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26029196415337561752295489 19521897311503171314221617)
                  ·
                    refine ⟨14641422983627378485666213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19521897311503171314221617 14641422983627378485666213)
                    ·
                      refine ⟨2745266809430133466062415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14641422983627378485666213 2745266809430133466062415)
                      ·
                        rfl

theorem cell23_5346388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_5346388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346388 prefixEnd_5346388 := by exact prefixLift 5346388
  have htrace : WordTrace (prefixWord ++ tailWord_5346388) baseStart_5346388 baseEnd_5346388 := by
    simpa [prefixWord, tailWord_5346388, baseEnd_5346388] using wordTrace_append hprefix tailTrace_5346388
  have hstable : (prefixWord ++ tailWord_5346388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346388).length < 2 ^ (prefixWord ++ tailWord_5346388).sum := by decide
  have hdescent : baseEnd_5346388 < baseStart_5346388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346409 : List Nat := [1, 2, 1, 1, 1, 7, 3, 1, 2, 2, 2]
def baseStart_5346409 : Nat := 118140960795 + 5346409 * 2 ^ 59
def prefixEnd_5346409 : Nat := 4983230072969 + 3 ^ 40 * 5346409 * 2
def baseEnd_5346409 : Nat := 2745277592523877883899819

theorem tailTrace_5346409 : CollatzResearch.WordTrace tailWord_5346409 prefixEnd_5346409 2745277592523877883899819 := by
  unfold tailWord_5346409
  simp only [CollatzResearch.WordTrace]
  refine ⟨194999556087880761807186281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 129999704058587174538124187 194999556087880761807186281)
  ·
    refine ⟨146249667065910571355389711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 194999556087880761807186281 146249667065910571355389711)
    ·
      refine ⟨219374500598865857033084567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146249667065910571355389711 219374500598865857033084567)
      ·
        refine ⟨329061750898298785549626851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219374500598865857033084567 329061750898298785549626851)
        ·
          refine ⟨493592626347448178324440277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329061750898298785549626851 493592626347448178324440277)
          ·
            refine ⟨11568577180018316679479069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 493592626347448178324440277 11568577180018316679479069)
            ·
              refine ⟨4338216442506868754804651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11568577180018316679479069 4338216442506868754804651)
              ·
                refine ⟨6507324663760303132206977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4338216442506868754804651 6507324663760303132206977)
                ·
                  refine ⟨4880493497820227349155233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6507324663760303132206977 4880493497820227349155233)
                  ·
                    refine ⟨3660370123365170511866425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4880493497820227349155233 3660370123365170511866425)
                    ·
                      refine ⟨2745277592523877883899819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3660370123365170511866425 2745277592523877883899819)
                      ·
                        rfl

theorem cell23_5346409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 2, 2, 2].length) (baseStart_5346409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346409 prefixEnd_5346409 := by exact prefixLift 5346409
  have htrace : WordTrace (prefixWord ++ tailWord_5346409) baseStart_5346409 baseEnd_5346409 := by
    simpa [prefixWord, tailWord_5346409, baseEnd_5346409] using wordTrace_append hprefix tailTrace_5346409
  have hstable : (prefixWord ++ tailWord_5346409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346409).length < 2 ^ (prefixWord ++ tailWord_5346409).sum := by decide
  have hdescent : baseEnd_5346409 < baseStart_5346409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346428 : List Nat := [2, 2, 2, 1, 1, 3, 2, 3, 2, 5]
def baseStart_5346428 : Nat := 118140960795 + 5346428 * 2 ^ 59
def prefixEnd_5346428 : Nat := 4983230072969 + 3 ^ 40 * 5346428 * 2
def baseEnd_5346428 : Nat := 915095782885437769854077

theorem tailTrace_5346428 : CollatzResearch.WordTrace tailWord_5346428 prefixEnd_5346428 915095782885437769854077 := by
  unfold tailWord_5346428
  simp only [CollatzResearch.WordTrace]
  refine ⟨97500124537405964026063969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130000166049874618701418625 97500124537405964026063969)
  ·
    refine ⟨73125093403054473019547977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97500124537405964026063969 73125093403054473019547977)
    ·
      refine ⟨54843820052290854764660983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73125093403054473019547977 54843820052290854764660983)
      ·
        refine ⟨82265730078436282146991475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54843820052290854764660983 82265730078436282146991475)
        ·
          refine ⟨123398595117654423220487213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82265730078436282146991475 123398595117654423220487213)
          ·
            refine ⟨46274473169120408707682705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123398595117654423220487213 46274473169120408707682705)
            ·
              refine ⟨34705854876840306530762029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46274473169120408707682705 34705854876840306530762029)
              ·
                refine ⟨13014695578815114949035761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34705854876840306530762029 13014695578815114949035761)
                ·
                  refine ⟨9761021684111336211776821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13014695578815114949035761 9761021684111336211776821)
                  ·
                    refine ⟨915095782885437769854077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9761021684111336211776821 915095782885437769854077)
                    ·
                      rfl

theorem cell23_5346428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_5346428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346428 prefixEnd_5346428 := by exact prefixLift 5346428
  have htrace : WordTrace (prefixWord ++ tailWord_5346428) baseStart_5346428 baseEnd_5346428 := by
    simpa [prefixWord, tailWord_5346428, baseEnd_5346428] using wordTrace_append hprefix tailTrace_5346428
  have hstable : (prefixWord ++ tailWord_5346428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346428).length < 2 ^ (prefixWord ++ tailWord_5346428).sum := by decide
  have hdescent : baseEnd_5346428 < baseStart_5346428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346465 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 1, 6, 2]
def baseStart_5346465 : Nat := 118140960795 + 5346465 * 2 ^ 59
def prefixEnd_5346465 : Nat := 4983230072969 + 3 ^ 40 * 5346465 * 2
def baseEnd_5346465 : Nat := 2745306347440529664799561

theorem tailTrace_5346465 : CollatzResearch.WordTrace tailWord_5346465 prefixEnd_5346465 2745306347440529664799561 := by
  unfold tailWord_5346465
  simp only [CollatzResearch.WordTrace]
  refine ⟨195001598575677883371224849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130001065717118588914149899 195001598575677883371224849)
  ·
    refine ⟨146251198931758412528418637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195001598575677883371224849 146251198931758412528418637)
    ·
      refine ⟨54844199599409404698156989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146251198931758412528418637 54844199599409404698156989)
      ·
        refine ⟨20566574849778526761808871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54844199599409404698156989 20566574849778526761808871)
        ·
          refine ⟨30849862274667790142713307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20566574849778526761808871 30849862274667790142713307)
          ·
            refine ⟨46274793412001685214069961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30849862274667790142713307 46274793412001685214069961)
            ·
              refine ⟨34706095059001263910552471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46274793412001685214069961 34706095059001263910552471)
              ·
                refine ⟨52059142588501895865828707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34706095059001263910552471 52059142588501895865828707)
                ·
                  refine ⟨78088713882752843798743061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52059142588501895865828707 78088713882752843798743061)
                  ·
                    refine ⟨3660408463254039553066081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 78088713882752843798743061 3660408463254039553066081)
                    ·
                      refine ⟨2745306347440529664799561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3660408463254039553066081 2745306347440529664799561)
                      ·
                        rfl

theorem cell23_5346465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_5346465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346465 prefixEnd_5346465 := by exact prefixLift 5346465
  have htrace : WordTrace (prefixWord ++ tailWord_5346465) baseStart_5346465 baseEnd_5346465 := by
    simpa [prefixWord, tailWord_5346465, baseEnd_5346465] using wordTrace_append hprefix tailTrace_5346465
  have hstable : (prefixWord ++ tailWord_5346465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346465).length < 2 ^ (prefixWord ++ tailWord_5346465).sum := by decide
  have hdescent : baseEnd_5346465 < baseStart_5346465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346565 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 4, 4]
def baseStart_5346565 : Nat := 118140960795 + 5346565 * 2 ^ 59
def prefixEnd_5346565 : Nat := 4983230072969 + 3 ^ 40 * 5346565 * 2
def baseEnd_5346565 : Nat := 915119231835326424516367

theorem tailTrace_5346565 : CollatzResearch.WordTrace tailWord_5346565 prefixEnd_5346565 915119231835326424516367 := by
  unfold tailWord_5346565
  simp only [CollatzResearch.WordTrace]
  refine ⟨195005245875315600449865149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130003497250210400299910099 195005245875315600449865149)
  ·
    refine ⟨73126967203243350168699431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195005245875315600449865149 73126967203243350168699431)
    ·
      refine ⟨109690450804865025253049147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73126967203243350168699431 109690450804865025253049147)
      ·
        refine ⟨164535676207297537879573721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109690450804865025253049147 164535676207297537879573721)
        ·
          refine ⟨123401757155473153409680291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164535676207297537879573721 123401757155473153409680291)
          ·
            refine ⟨185102635733209730114520437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123401757155473153409680291 185102635733209730114520437)
            ·
              refine ⟨17353372099988412198236291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 185102635733209730114520437 17353372099988412198236291)
              ·
                refine ⟨26030058149982618297354437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17353372099988412198236291 26030058149982618297354437)
                ·
                  refine ⟨4880635903121740930753957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26030058149982618297354437 4880635903121740930753957)
                  ·
                    refine ⟨915119231835326424516367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4880635903121740930753957 915119231835326424516367)
                    ·
                      rfl

theorem cell23_5346565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 4, 4].length) (baseStart_5346565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346565 prefixEnd_5346565 := by exact prefixLift 5346565
  have htrace : WordTrace (prefixWord ++ tailWord_5346565) baseStart_5346565 baseEnd_5346565 := by
    simpa [prefixWord, tailWord_5346565, baseEnd_5346565] using wordTrace_append hprefix tailTrace_5346565
  have hstable : (prefixWord ++ tailWord_5346565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346565).length < 2 ^ (prefixWord ++ tailWord_5346565).sum := by decide
  have hdescent : baseEnd_5346565 < baseStart_5346565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346589 : List Nat := [1, 4, 2, 3, 1, 2, 2, 2, 1, 1, 4]
def baseStart_5346589 : Nat := 118140960795 + 5346589 * 2 ^ 59
def prefixEnd_5346589 : Nat := 4983230072969 + 3 ^ 40 * 5346589 * 2
def baseEnd_5346589 : Nat := 2745370019041687179648991

theorem tailTrace_5346589 : CollatzResearch.WordTrace tailWord_5346589 prefixEnd_5346589 2745370019041687179648991 := by
  unfold tailWord_5346589
  simp only [CollatzResearch.WordTrace]
  refine ⟨195006121227228652548738821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130004080818152435032492547 195006121227228652548738821)
  ·
    refine ⟨36563647730105372352888529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195006121227228652548738821 36563647730105372352888529)
    ·
      refine ⟨27422735797579029264666397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36563647730105372352888529 27422735797579029264666397)
      ·
        refine ⟨10283525924092135974249899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27422735797579029264666397 10283525924092135974249899)
        ·
          refine ⟨15425288886138203961374849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10283525924092135974249899 15425288886138203961374849)
          ·
            refine ⟨11568966664603652971031137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15425288886138203961374849 11568966664603652971031137)
            ·
              refine ⟨8676724998452739728273353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11568966664603652971031137 8676724998452739728273353)
              ·
                refine ⟨6507543748839554796205015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8676724998452739728273353 6507543748839554796205015)
                ·
                  refine ⟨9761315623259332194307523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6507543748839554796205015 9761315623259332194307523)
                  ·
                    refine ⟨14641973434888998291461285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9761315623259332194307523 14641973434888998291461285)
                    ·
                      refine ⟨2745370019041687179648991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14641973434888998291461285 2745370019041687179648991)
                      ·
                        rfl

theorem cell23_5346589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_5346589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346589 prefixEnd_5346589 := by exact prefixLift 5346589
  have htrace : WordTrace (prefixWord ++ tailWord_5346589) baseStart_5346589 baseEnd_5346589 := by
    simpa [prefixWord, tailWord_5346589, baseEnd_5346589] using wordTrace_append hprefix tailTrace_5346589
  have hstable : (prefixWord ++ tailWord_5346589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346589).length < 2 ^ (prefixWord ++ tailWord_5346589).sum := by decide
  have hdescent : baseEnd_5346589 < baseStart_5346589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346595 : List Nat := [1, 1, 1, 4, 2, 3, 4, 7]
def baseStart_5346595 : Nat := 118140960795 + 5346595 * 2 ^ 59
def prefixEnd_5346595 : Nat := 4983230072969 + 3 ^ 40 * 5346595 * 2
def baseEnd_5346595 : Nat := 101680485182430153932369

theorem tailTrace_5346595 : CollatzResearch.WordTrace tailWord_5346595 prefixEnd_5346595 101680485182430153932369 := by
  unfold tailWord_5346595
  simp only [CollatzResearch.WordTrace]
  refine ⟨195006340065206915573457239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130004226710137943715638159 195006340065206915573457239)
  ·
    refine ⟨292509510097810373360185859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195006340065206915573457239 292509510097810373360185859)
    ·
      refine ⟨438764265146715560040278789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292509510097810373360185859 438764265146715560040278789)
      ·
        refine ⟨82268299715009167507552273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 438764265146715560040278789 82268299715009167507552273)
        ·
          refine ⟨61701224786256875630664205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82268299715009167507552273 61701224786256875630664205)
          ·
            refine ⟨23137959294846328361499077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61701224786256875630664205 23137959294846328361499077)
            ·
              refine ⟨4338367367783686567781077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23137959294846328361499077 4338367367783686567781077)
              ·
                refine ⟨101680485182430153932369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4338367367783686567781077 101680485182430153932369)
                ·
                  rfl

theorem cell23_5346595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 4, 7].length) (baseStart_5346595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346595 prefixEnd_5346595 := by exact prefixLift 5346595
  have htrace : WordTrace (prefixWord ++ tailWord_5346595) baseStart_5346595 baseEnd_5346595 := by
    simpa [prefixWord, tailWord_5346595, baseEnd_5346595] using wordTrace_append hprefix tailTrace_5346595
  have hstable : (prefixWord ++ tailWord_5346595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346595).length < 2 ^ (prefixWord ++ tailWord_5346595).sum := by decide
  have hdescent : baseEnd_5346595 < baseStart_5346595 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346623 : List Nat := [1, 1, 2, 2, 4, 3, 3, 2, 1, 2, 2]
def baseStart_5346623 : Nat := 118140960795 + 5346623 * 2 ^ 59
def prefixEnd_5346623 : Nat := 4983230072969 + 3 ^ 40 * 5346623 * 2
def baseEnd_5346623 : Nat := 2745387477383940046623835

theorem tailTrace_5346623 : CollatzResearch.WordTrace tailWord_5346623 prefixEnd_5346623 2745387477383940046623835 := by
  unfold tailWord_5346623
  simp only [CollatzResearch.WordTrace]
  refine ⟨195007361309105476355476523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130004907539403650903651015 195007361309105476355476523)
  ·
    refine ⟨292511041963658214533214785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195007361309105476355476523 292511041963658214533214785)
    ·
      refine ⟨219383281472743660899911089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292511041963658214533214785 219383281472743660899911089)
      ·
        refine ⟨164537461104557745674933317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219383281472743660899911089 164537461104557745674933317)
        ·
          refine ⟨30850773957104577314049997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164537461104557745674933317 30850773957104577314049997)
          ·
            refine ⟨11569040233914216492768749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30850773957104577314049997 11569040233914216492768749)
            ·
              refine ⟨4338390087717831184788281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11569040233914216492768749 4338390087717831184788281)
              ·
                refine ⟨3253792565788373388591211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4338390087717831184788281 3253792565788373388591211)
                ·
                  refine ⟨4880688848682560082886817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3253792565788373388591211 4880688848682560082886817)
                  ·
                    refine ⟨3660516636511920062165113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4880688848682560082886817 3660516636511920062165113)
                    ·
                      refine ⟨2745387477383940046623835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3660516636511920062165113 2745387477383940046623835)
                      ·
                        rfl

theorem cell23_5346623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 1, 2, 2].length) (baseStart_5346623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346623 prefixEnd_5346623 := by exact prefixLift 5346623
  have htrace : WordTrace (prefixWord ++ tailWord_5346623) baseStart_5346623 baseEnd_5346623 := by
    simpa [prefixWord, tailWord_5346623, baseEnd_5346623] using wordTrace_append hprefix tailTrace_5346623
  have hstable : (prefixWord ++ tailWord_5346623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346623).length < 2 ^ (prefixWord ++ tailWord_5346623).sum := by decide
  have hdescent : baseEnd_5346623 < baseStart_5346623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346632 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 3, 3, 2]
def baseStart_5346632 : Nat := 118140960795 + 5346632 * 2 ^ 59
def prefixEnd_5346632 : Nat := 4983230072969 + 3 ^ 40 * 5346632 * 2
def baseEnd_5346632 : Nat := 2745392098709830511411293

theorem tailTrace_5346632 : CollatzResearch.WordTrace tailWord_5346632 prefixEnd_5346632 2745392098709830511411293 := by
  unfold tailWord_5346632
  simp only [CollatzResearch.WordTrace]
  refine ⟨97503844783036435446277075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130005126377381913928369433 97503844783036435446277075)
  ·
    refine ⟨146255767174554653169415613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97503844783036435446277075 146255767174554653169415613)
    ·
      refine ⟨54845912690457994938530855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146255767174554653169415613 54845912690457994938530855)
      ·
        refine ⟨82268869035686992407796283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54845912690457994938530855 82268869035686992407796283)
        ·
          refine ⟨123403303553530488611694425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82268869035686992407796283 123403303553530488611694425)
          ·
            refine ⟨92552477665147866458770819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123403303553530488611694425 92552477665147866458770819)
            ·
              refine ⟨138828716497721799688156229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92552477665147866458770819 138828716497721799688156229)
              ·
                refine ⟨26030384343322837441529293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138828716497721799688156229 26030384343322837441529293)
                ·
                  refine ⟨9761394128746064040573485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26030384343322837441529293 9761394128746064040573485)
                  ·
                    refine ⟨3660522798279774015215057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9761394128746064040573485 3660522798279774015215057)
                    ·
                      refine ⟨2745392098709830511411293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3660522798279774015215057 2745392098709830511411293)
                      ·
                        rfl

theorem cell23_5346632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 3, 3, 2].length) (baseStart_5346632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346632 prefixEnd_5346632 := by exact prefixLift 5346632
  have htrace : WordTrace (prefixWord ++ tailWord_5346632) baseStart_5346632 baseEnd_5346632 := by
    simpa [prefixWord, tailWord_5346632, baseEnd_5346632] using wordTrace_append hprefix tailTrace_5346632
  have hstable : (prefixWord ++ tailWord_5346632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346632).length < 2 ^ (prefixWord ++ tailWord_5346632).sum := by decide
  have hdescent : baseEnd_5346632 < baseStart_5346632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346649 : List Nat := [1, 2, 1, 2, 2, 2, 5, 2, 1, 3, 2]
def baseStart_5346649 : Nat := 118140960795 + 5346649 * 2 ^ 59
def prefixEnd_5346649 : Nat := 4983230072969 + 3 ^ 40 * 5346649 * 2
def baseEnd_5346649 : Nat := 2745400827880956944898715

theorem tailTrace_5346649 : CollatzResearch.WordTrace tailWord_5346649 prefixEnd_5346649 2745400827880956944898715 := by
  unfold tailWord_5346649
  simp only [CollatzResearch.WordTrace]
  refine ⟨195008309607011282795923001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130005539738007521863948667 195008309607011282795923001)
  ·
    refine ⟨146256232205258462096942251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195008309607011282795923001 146256232205258462096942251)
    ·
      refine ⟨219384348307887693145413377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146256232205258462096942251 219384348307887693145413377)
      ·
        refine ⟨164538261230915769859060033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219384348307887693145413377 164538261230915769859060033)
        ·
          refine ⟨123403695923186827394295025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164538261230915769859060033 123403695923186827394295025)
          ·
            refine ⟨92552771942390120545721269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123403695923186827394295025 92552771942390120545721269)
            ·
              refine ⟨8676822369599073801161369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 92552771942390120545721269 8676822369599073801161369)
              ·
                refine ⟨6507616777199305350871027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8676822369599073801161369 6507616777199305350871027)
                ·
                  refine ⟨9761425165798958026306541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6507616777199305350871027 9761425165798958026306541)
                  ·
                    refine ⟨3660534437174609259864953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9761425165798958026306541 3660534437174609259864953)
                    ·
                      refine ⟨2745400827880956944898715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3660534437174609259864953 2745400827880956944898715)
                      ·
                        rfl

theorem cell23_5346649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 1, 3, 2].length) (baseStart_5346649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346649 prefixEnd_5346649 := by exact prefixLift 5346649
  have htrace : WordTrace (prefixWord ++ tailWord_5346649) baseStart_5346649 baseEnd_5346649 := by
    simpa [prefixWord, tailWord_5346649, baseEnd_5346649] using wordTrace_append hprefix tailTrace_5346649
  have hstable : (prefixWord ++ tailWord_5346649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346649).length < 2 ^ (prefixWord ++ tailWord_5346649).sum := by decide
  have hdescent : baseEnd_5346649 < baseStart_5346649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346685 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 7]
def baseStart_5346685 : Nat := 118140960795 + 5346685 * 2 ^ 59
def prefixEnd_5346685 : Nat := 4983230072969 + 3 ^ 40 * 5346685 * 2
def baseEnd_5346685 : Nat := 305046590353835422672061

theorem tailTrace_5346685 : CollatzResearch.WordTrace tailWord_5346685 prefixEnd_5346685 305046590353835422672061 := by
  unfold tailWord_5346685
  simp only [CollatzResearch.WordTrace]
  refine ⟨195009622634880860944233509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130006415089920573962822339 195009622634880860944233509)
  ·
    refine ⟨36564304244040161427043783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195009622634880860944233509 36564304244040161427043783)
    ·
      refine ⟨54846456366060242140565675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36564304244040161427043783 54846456366060242140565675)
      ·
        refine ⟨82269684549090363210848513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54846456366060242140565675 82269684549090363210848513)
        ·
          refine ⟨61702263411817772408136385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82269684549090363210848513 61702263411817772408136385)
          ·
            refine ⟨46276697558863329306102289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61702263411817772408136385 46276697558863329306102289)
            ·
              refine ⟨34707523169147496979576717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46276697558863329306102289 34707523169147496979576717)
              ·
                refine ⟨13015321188430311367341269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34707523169147496979576717 13015321188430311367341269)
                ·
                  refine ⟨305046590353835422672061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13015321188430311367341269 305046590353835422672061)
                  ·
                    rfl

theorem cell23_5346685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_5346685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346685 prefixEnd_5346685 := by exact prefixLift 5346685
  have htrace : WordTrace (prefixWord ++ tailWord_5346685) baseStart_5346685 baseEnd_5346685 := by
    simpa [prefixWord, tailWord_5346685, baseEnd_5346685] using wordTrace_append hprefix tailTrace_5346685
  have hstable : (prefixWord ++ tailWord_5346685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346685).length < 2 ^ (prefixWord ++ tailWord_5346685).sum := by decide
  have hdescent : baseEnd_5346685 < baseStart_5346685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346692 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_5346692 : Nat := 118140960795 + 5346692 * 2 ^ 59
def prefixEnd_5346692 : Nat := 4983230072969 + 3 ^ 40 * 5346692 * 2
def baseEnd_5346692 : Nat := 2745422907549100276661017

theorem tailTrace_5346692 : CollatzResearch.WordTrace tailWord_5346692 prefixEnd_5346692 2745422907549100276661017 := by
  unfold tailWord_5346692
  simp only [CollatzResearch.WordTrace]
  refine ⟨97504938972927750569869165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130006585297237000759825553 97504938972927750569869165)
  ·
    refine ⟨36564352114847906463700937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97504938972927750569869165 36564352114847906463700937)
    ·
      refine ⟨27423264086135929847775703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36564352114847906463700937 27423264086135929847775703)
      ·
        refine ⟨41134896129203894771663555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27423264086135929847775703 41134896129203894771663555)
        ·
          refine ⟨61702344193805842157495333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41134896129203894771663555 61702344193805842157495333)
          ·
            refine ⟨11569189536338595404530375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61702344193805842157495333 11569189536338595404530375)
            ·
              refine ⟨17353784304507893106795563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11569189536338595404530375 17353784304507893106795563)
              ·
                refine ⟨26030676456761839660193345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17353784304507893106795563 26030676456761839660193345)
                ·
                  refine ⟨19523007342571379745145009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26030676456761839660193345 19523007342571379745145009)
                  ·
                    refine ⟨14642255506928534808858757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19523007342571379745145009 14642255506928534808858757)
                    ·
                      refine ⟨2745422907549100276661017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14642255506928534808858757 2745422907549100276661017)
                      ·
                        rfl

theorem cell23_5346692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_5346692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346692 prefixEnd_5346692 := by exact prefixLift 5346692
  have htrace : WordTrace (prefixWord ++ tailWord_5346692) baseStart_5346692 baseEnd_5346692 := by
    simpa [prefixWord, tailWord_5346692, baseEnd_5346692] using wordTrace_append hprefix tailTrace_5346692
  have hstable : (prefixWord ++ tailWord_5346692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346692).length < 2 ^ (prefixWord ++ tailWord_5346692).sum := by decide
  have hdescent : baseEnd_5346692 < baseStart_5346692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346696 : List Nat := [2, 1, 3, 3, 1, 2, 2, 3, 2, 2, 2]
def baseStart_5346696 : Nat := 118140960795 + 5346696 * 2 ^ 59
def prefixEnd_5346696 : Nat := 4983230072969 + 3 ^ 40 * 5346696 * 2
def baseEnd_5346696 : Nat := 2745424961471718261010999

theorem tailTrace_5346696 : CollatzResearch.WordTrace tailWord_5346696 prefixEnd_5346696 2745424961471718261010999 := by
  unfold tailWord_5346696
  simp only [CollatzResearch.WordTrace]
  refine ⟨97505011918920504911441971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130006682558560673215255961 97505011918920504911441971)
  ·
    refine ⟨146257517878380757367162957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97505011918920504911441971 146257517878380757367162957)
    ·
      refine ⟨54846569204392784012686109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146257517878380757367162957 54846569204392784012686109)
      ·
        refine ⟨20567463451647294004757291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54846569204392784012686109 20567463451647294004757291)
        ·
          refine ⟨30851195177470941007135937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20567463451647294004757291 30851195177470941007135937)
          ·
            refine ⟨23138396383103205755351953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30851195177470941007135937 23138396383103205755351953)
            ·
              refine ⟨17353797287327404316513965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23138396383103205755351953 17353797287327404316513965)
              ·
                refine ⟨6507673982747776618692737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17353797287327404316513965 6507673982747776618692737)
                ·
                  refine ⟨4880755487060832464019553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6507673982747776618692737 4880755487060832464019553)
                  ·
                    refine ⟨3660566615295624348014665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4880755487060832464019553 3660566615295624348014665)
                    ·
                      refine ⟨2745424961471718261010999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3660566615295624348014665 2745424961471718261010999)
                      ·
                        rfl

theorem cell23_5346696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_5346696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346696 prefixEnd_5346696 := by exact prefixLift 5346696
  have htrace : WordTrace (prefixWord ++ tailWord_5346696) baseStart_5346696 baseEnd_5346696 := by
    simpa [prefixWord, tailWord_5346696, baseEnd_5346696] using wordTrace_append hprefix tailTrace_5346696
  have hstable : (prefixWord ++ tailWord_5346696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346696).length < 2 ^ (prefixWord ++ tailWord_5346696).sum := by decide
  have hdescent : baseEnd_5346696 < baseStart_5346696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346719 : List Nat := [1, 1, 2, 5, 1, 3, 2, 3, 5]
def baseStart_5346719 : Nat := 118140960795 + 5346719 * 2 ^ 59
def prefixEnd_5346719 : Nat := 4983230072969 + 3 ^ 40 * 5346719 * 2
def baseEnd_5346719 : Nat := 305048530169641296780377

theorem tailTrace_5346719 : CollatzResearch.WordTrace tailWord_5346719 prefixEnd_5346719 305048530169641296780377 := by
  unfold tailWord_5346719
  simp only [CollatzResearch.WordTrace]
  refine ⟨195010862716757684750971211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130007241811171789833980807 195010862716757684750971211)
  ·
    refine ⟨292516294075136527126456817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195010862716757684750971211 292516294075136527126456817)
    ·
      refine ⟨219387220556352395344842613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292516294075136527126456817 219387220556352395344842613)
      ·
        refine ⟨20567551927158037063578995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 219387220556352395344842613 20567551927158037063578995)
        ·
          refine ⟨30851327890737055595368493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20567551927158037063578995 30851327890737055595368493)
          ·
            refine ⟨11569247959026395848263185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30851327890737055595368493 11569247959026395848263185)
            ·
              refine ⟨8676935969269796886197389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11569247959026395848263185 8676935969269796886197389)
              ·
                refine ⟨3253850988476173832324021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8676935969269796886197389 3253850988476173832324021)
                ·
                  refine ⟨305048530169641296780377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3253850988476173832324021 305048530169641296780377)
                  ·
                    rfl

theorem cell23_5346719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 5].length) (baseStart_5346719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346719 prefixEnd_5346719 := by exact prefixLift 5346719
  have htrace : WordTrace (prefixWord ++ tailWord_5346719) baseStart_5346719 baseEnd_5346719 := by
    simpa [prefixWord, tailWord_5346719, baseEnd_5346719] using wordTrace_append hprefix tailTrace_5346719
  have hstable : (prefixWord ++ tailWord_5346719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346719).length < 2 ^ (prefixWord ++ tailWord_5346719).sum := by decide
  have hdescent : baseEnd_5346719 < baseStart_5346719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346725 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 1, 2, 5]
def baseStart_5346725 : Nat := 118140960795 + 5346725 * 2 ^ 59
def prefixEnd_5346725 : Nat := 4983230072969 + 3 ^ 40 * 5346725 * 2
def baseEnd_5346725 : Nat := 2745439852410698647548365

theorem tailTrace_5346725 : CollatzResearch.WordTrace tailWord_5346725 prefixEnd_5346725 2745439852410698647548365 := by
  unfold tailWord_5346725
  simp only [CollatzResearch.WordTrace]
  refine ⟨195011081554735947775689629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130007387703157298517126419 195011081554735947775689629)
  ·
    refine ⟨73129155583025980415883611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195011081554735947775689629 73129155583025980415883611)
    ·
      refine ⟨109693733374538970623825417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73129155583025980415883611 109693733374538970623825417)
      ·
        refine ⟨82270300030904227967869063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109693733374538970623825417 82270300030904227967869063)
        ·
          refine ⟨123405450046356341951803595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82270300030904227967869063 123405450046356341951803595)
          ·
            refine ⟨185108175069534512927705393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123405450046356341951803595 185108175069534512927705393)
            ·
              refine ⟨138831131302150884695779045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185108175069534512927705393 138831131302150884695779045)
              ·
                refine ⟨26030837119153290880458571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138831131302150884695779045 26030837119153290880458571)
                ·
                  refine ⟨39046255678729936320687857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26030837119153290880458571 39046255678729936320687857)
                  ·
                    refine ⟨29284691759047452240515893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39046255678729936320687857 29284691759047452240515893)
                    ·
                      refine ⟨2745439852410698647548365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29284691759047452240515893 2745439852410698647548365)
                      ·
                        rfl

theorem cell23_5346725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_5346725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346725 prefixEnd_5346725 := by exact prefixLift 5346725
  have htrace : WordTrace (prefixWord ++ tailWord_5346725) baseStart_5346725 baseEnd_5346725 := by
    simpa [prefixWord, tailWord_5346725, baseEnd_5346725] using wordTrace_append hprefix tailTrace_5346725
  have hstable : (prefixWord ++ tailWord_5346725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346725).length < 2 ^ (prefixWord ++ tailWord_5346725).sum := by decide
  have hdescent : baseEnd_5346725 < baseStart_5346725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346789 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 4, 2, 3]
def baseStart_5346789 : Nat := 118140960795 + 5346789 * 2 ^ 59
def prefixEnd_5346789 : Nat := 4983230072969 + 3 ^ 40 * 5346789 * 2
def baseEnd_5346789 : Nat := 2745472715172586397148071

theorem tailTrace_5346789 : CollatzResearch.WordTrace tailWord_5346789 prefixEnd_5346789 2745472715172586397148071 := by
  unfold tailWord_5346789
  simp only [CollatzResearch.WordTrace]
  refine ⟨195013415826504086706019421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130008943884336057804012947 195013415826504086706019421)
  ·
    refine ⟨73130030934939032514757283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195013415826504086706019421 73130030934939032514757283)
    ·
      refine ⟨109695046402408548772135925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73130030934939032514757283 109695046402408548772135925)
      ·
        refine ⟨10283910600225801447387743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109695046402408548772135925 10283910600225801447387743)
        ·
          refine ⟨15425865900338702171081615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10283910600225801447387743 15425865900338702171081615)
          ·
            refine ⟨23138798850508053256622423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15425865900338702171081615 23138798850508053256622423)
            ·
              refine ⟨34708198275762079884933635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23138798850508053256622423 34708198275762079884933635)
              ·
                refine ⟨52062297413643119827400453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34708198275762079884933635 52062297413643119827400453)
                ·
                  refine ⟨9761680765058084967637585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52062297413643119827400453 9761680765058084967637585)
                  ·
                    refine ⟨7321260573793563725728189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9761680765058084967637585 7321260573793563725728189)
                    ·
                      refine ⟨2745472715172586397148071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7321260573793563725728189 2745472715172586397148071)
                      ·
                        rfl

theorem cell23_5346789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_5346789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346789 prefixEnd_5346789 := by exact prefixLift 5346789
  have htrace : WordTrace (prefixWord ++ tailWord_5346789) baseStart_5346789 baseEnd_5346789 := by
    simpa [prefixWord, tailWord_5346789, baseEnd_5346789] using wordTrace_append hprefix tailTrace_5346789
  have hstable : (prefixWord ++ tailWord_5346789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346789).length < 2 ^ (prefixWord ++ tailWord_5346789).sum := by decide
  have hdescent : baseEnd_5346789 < baseStart_5346789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346792 : List Nat := [2, 1, 4, 1, 1, 2, 2, 4, 6]
def baseStart_5346792 : Nat := 118140960795 + 5346792 * 2 ^ 59
def prefixEnd_5346792 : Nat := 4983230072969 + 3 ^ 40 * 5346792 * 2
def baseEnd_5346792 : Nat := 305052695068283320601173

theorem tailTrace_5346792 : CollatzResearch.WordTrace tailWord_5346792 prefixEnd_5346792 305052695068283320601173 := by
  unfold tailWord_5346792
  simp only [CollatzResearch.WordTrace]
  refine ⟨97506762622746609109189315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130009016830328812145585753 97506762622746609109189315)
  ·
    refine ⟨146260143934119913663783973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97506762622746609109189315 146260143934119913663783973)
    ·
      refine ⟨27423776987647483811959495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146260143934119913663783973 27423776987647483811959495)
      ·
        refine ⟨41135665481471225717939243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27423776987647483811959495 41135665481471225717939243)
        ·
          refine ⟨61703498222206838576908865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41135665481471225717939243 61703498222206838576908865)
          ·
            refine ⟨46277623666655128932681649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61703498222206838576908865 46277623666655128932681649)
            ·
              refine ⟨34708217749991346699511237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46277623666655128932681649 34708217749991346699511237)
              ·
                refine ⟨6507790828123377506158357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34708217749991346699511237 6507790828123377506158357)
                ·
                  refine ⟨305052695068283320601173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6507790828123377506158357 305052695068283320601173)
                  ·
                    rfl

theorem cell23_5346792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 6].length) (baseStart_5346792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346792 prefixEnd_5346792 := by exact prefixLift 5346792
  have htrace : WordTrace (prefixWord ++ tailWord_5346792) baseStart_5346792 baseEnd_5346792 := by
    simpa [prefixWord, tailWord_5346792, baseEnd_5346792] using wordTrace_append hprefix tailTrace_5346792
  have hstable : (prefixWord ++ tailWord_5346792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346792).length < 2 ^ (prefixWord ++ tailWord_5346792).sum := by decide
  have hdescent : baseEnd_5346792 < baseStart_5346792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346795 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 6]
def baseStart_5346795 : Nat := 118140960795 + 5346795 * 2 ^ 59
def prefixEnd_5346795 : Nat := 4983230072969 + 3 ^ 40 * 5346795 * 2
def baseEnd_5346795 : Nat := 2745475796056513373673043

theorem tailTrace_5346795 : CollatzResearch.WordTrace tailWord_5346795 prefixEnd_5346795 2745475796056513373673043 := by
  unfold tailWord_5346795
  simp only [CollatzResearch.WordTrace]
  refine ⟨195013634664482349730737839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130009089776321566487158559 195013634664482349730737839)
  ·
    refine ⟨292520451996723524596106759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195013634664482349730737839 292520451996723524596106759)
    ·
      refine ⟨438780677995085286894160139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292520451996723524596106759 438780677995085286894160139)
      ·
        refine ⟨658171016992627930341240209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438780677995085286894160139 658171016992627930341240209)
        ·
          refine ⟨493628262744470947755930157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 658171016992627930341240209 493628262744470947755930157)
          ·
            refine ⟨185110598529176605408473809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 493628262744470947755930157 185110598529176605408473809)
            ·
              refine ⟨138832948896882454056355357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185110598529176605408473809 138832948896882454056355357)
              ·
                refine ⟨52062355836330920271133259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138832948896882454056355357 52062355836330920271133259)
                ·
                  refine ⟨78093533754496380406699889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52062355836330920271133259 78093533754496380406699889)
                  ·
                    refine ⟨58570150315872285305024917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78093533754496380406699889 58570150315872285305024917)
                    ·
                      refine ⟨2745475796056513373673043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58570150315872285305024917 2745475796056513373673043)
                      ·
                        rfl

theorem cell23_5346795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 1, 2, 6].length) (baseStart_5346795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346795 prefixEnd_5346795 := by exact prefixLift 5346795
  have htrace : WordTrace (prefixWord ++ tailWord_5346795) baseStart_5346795 baseEnd_5346795 := by
    simpa [prefixWord, tailWord_5346795, baseEnd_5346795] using wordTrace_append hprefix tailTrace_5346795
  have hstable : (prefixWord ++ tailWord_5346795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346795).length < 2 ^ (prefixWord ++ tailWord_5346795).sum := by decide
  have hdescent : baseEnd_5346795 < baseStart_5346795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346815 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 7]
def baseStart_5346815 : Nat := 118140960795 + 5346815 * 2 ^ 59
def prefixEnd_5346815 : Nat := 4983230072969 + 3 ^ 40 * 5346815 * 2
def baseEnd_5346815 : Nat := 2745486065669603295422951

theorem tailTrace_5346815 : CollatzResearch.WordTrace tailWord_5346815 prefixEnd_5346815 2745486065669603295422951 := by
  unfold tailWord_5346815
  simp only [CollatzResearch.WordTrace]
  refine ⟨195014364124409893146465899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130009576082939928764310599 195014364124409893146465899)
  ·
    refine ⟨292521546186614839719698849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195014364124409893146465899 292521546186614839719698849)
    ·
      refine ⟨219391159639961129789774137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292521546186614839719698849 219391159639961129789774137)
      ·
        refine ⟨164543369729970847342330603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219391159639961129789774137 164543369729970847342330603)
        ·
          refine ⟨246815054594956271013495905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164543369729970847342330603 246815054594956271013495905)
          ·
            refine ⟨185111290946217203260121929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246815054594956271013495905 185111290946217203260121929)
            ·
              refine ⟨138833468209662902445091447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185111290946217203260121929 138833468209662902445091447)
              ·
                refine ⟨208250202314494353667637171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138833468209662902445091447 208250202314494353667637171)
                ·
                  refine ⟨312375303471741530501455757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 208250202314494353667637171 312375303471741530501455757)
                  ·
                    refine ⟨117140738801903073938045909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 312375303471741530501455757 117140738801903073938045909)
                    ·
                      refine ⟨2745486065669603295422951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117140738801903073938045909 2745486065669603295422951)
                      ·
                        rfl

theorem cell23_5346815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_5346815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346815 prefixEnd_5346815 := by exact prefixLift 5346815
  have htrace : WordTrace (prefixWord ++ tailWord_5346815) baseStart_5346815 baseEnd_5346815 := by
    simpa [prefixWord, tailWord_5346815, baseEnd_5346815] using wordTrace_append hprefix tailTrace_5346815
  have hstable : (prefixWord ++ tailWord_5346815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346815).length < 2 ^ (prefixWord ++ tailWord_5346815).sum := by decide
  have hdescent : baseEnd_5346815 < baseStart_5346815 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346869 : List Nat := [1, 3, 3, 1, 1, 4, 2, 1, 1, 6]
def baseStart_5346869 : Nat := 118140960795 + 5346869 * 2 ^ 59
def prefixEnd_5346869 : Nat := 4983230072969 + 3 ^ 40 * 5346869 * 2
def baseEnd_5346869 : Nat := 915171264541648694715901

theorem tailTrace_5346869 : CollatzResearch.WordTrace tailWord_5346869 prefixEnd_5346869 915171264541648694715901 := by
  unfold tailWord_5346869
  simp only [CollatzResearch.WordTrace]
  refine ⟨195016333666214260368931661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130010889110809506912621107 195016333666214260368931661)
  ·
    refine ⟨73131125124830347638349373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195016333666214260368931661 73131125124830347638349373)
    ·
      refine ⟨27424171921811380364381015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73131125124830347638349373 27424171921811380364381015)
      ·
        refine ⟨41136257882717070546571523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27424171921811380364381015 41136257882717070546571523)
        ·
          refine ⟨61704386824075605819857285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41136257882717070546571523 61704386824075605819857285)
          ·
            refine ⟨11569572529514176091223241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 61704386824075605819857285 11569572529514176091223241)
            ·
              refine ⟨8677179397135632068417431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11569572529514176091223241 8677179397135632068417431)
              ·
                refine ⟨13015769095703448102626147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8677179397135632068417431 13015769095703448102626147)
                ·
                  refine ⟨19523653643555172153939221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13015769095703448102626147 19523653643555172153939221)
                  ·
                    refine ⟨915171264541648694715901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19523653643555172153939221 915171264541648694715901)
                    ·
                      rfl

theorem cell23_5346869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 6].length) (baseStart_5346869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346869 prefixEnd_5346869 := by exact prefixLift 5346869
  have htrace : WordTrace (prefixWord ++ tailWord_5346869) baseStart_5346869 baseEnd_5346869 := by
    simpa [prefixWord, tailWord_5346869, baseEnd_5346869] using wordTrace_append hprefix tailTrace_5346869
  have hstable : (prefixWord ++ tailWord_5346869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346869).length < 2 ^ (prefixWord ++ tailWord_5346869).sum := by decide
  have hdescent : baseEnd_5346869 < baseStart_5346869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346879 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 3]
def baseStart_5346879 : Nat := 118140960795 + 5346879 * 2 ^ 59
def prefixEnd_5346879 : Nat := 4983230072969 + 3 ^ 40 * 5346879 * 2
def baseEnd_5346879 : Nat := 2745518928431491045022657

theorem tailTrace_5346879 : CollatzResearch.WordTrace tailWord_5346879 prefixEnd_5346879 2745518928431491045022657 := by
  unfold tailWord_5346879
  simp only [CollatzResearch.WordTrace]
  refine ⟨195016698396178032076795691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130011132264118688051197127 195016698396178032076795691)
  ·
    refine ⟨292525047594267048115193537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195016698396178032076795691 292525047594267048115193537)
    ·
      refine ⟨219393785695700286086395153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292525047594267048115193537 219393785695700286086395153)
      ·
        refine ⟨164545339271775214564796365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219393785695700286086395153 164545339271775214564796365)
        ·
          refine ⟨61704502226915705461798637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164545339271775214564796365 61704502226915705461798637)
          ·
            refine ⟨23139188335093389548174489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61704502226915705461798637 23139188335093389548174489)
            ·
              refine ⟨17354391251320042161130867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23139188335093389548174489 17354391251320042161130867)
              ·
                refine ⟨26031586876980063241696301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17354391251320042161130867 26031586876980063241696301)
                ·
                  refine ⟨9761845078867523715636113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26031586876980063241696301 9761845078867523715636113)
                  ·
                    refine ⟨7321383809150642786727085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9761845078867523715636113 7321383809150642786727085)
                    ·
                      refine ⟨2745518928431491045022657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7321383809150642786727085 2745518928431491045022657)
                      ·
                        rfl

theorem cell23_5346879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 3].length) (baseStart_5346879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346879 prefixEnd_5346879 := by exact prefixLift 5346879
  have htrace : WordTrace (prefixWord ++ tailWord_5346879) baseStart_5346879 baseEnd_5346879 := by
    simpa [prefixWord, tailWord_5346879, baseEnd_5346879] using wordTrace_append hprefix tailTrace_5346879
  have hstable : (prefixWord ++ tailWord_5346879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346879).length < 2 ^ (prefixWord ++ tailWord_5346879).sum := by decide
  have hdescent : baseEnd_5346879 < baseStart_5346879 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346893 : List Nat := [1, 6, 1, 1, 3, 1, 1, 3, 1, 1, 4]
def baseStart_5346893 : Nat := 118140960795 + 5346893 * 2 ^ 59
def prefixEnd_5346893 : Nat := 4983230072969 + 3 ^ 40 * 5346893 * 2
def baseEnd_5346893 : Nat := 2745526117160653990247593

theorem tailTrace_5346893 : CollatzResearch.WordTrace tailWord_5346893 prefixEnd_5346893 2745526117160653990247593 := by
  unfold tailWord_5346893
  simp only [CollatzResearch.WordTrace]
  refine ⟨195017209018127312467805333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130011472678751541645203555 195017209018127312467805333)
  ·
    refine ⟨9141431672724717771928375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 195017209018127312467805333 9141431672724717771928375)
    ·
      refine ⟨13712147509087076657892563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9141431672724717771928375 13712147509087076657892563)
      ·
        refine ⟨20568221263630614986838845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13712147509087076657892563 20568221263630614986838845)
        ·
          refine ⟨7713082973861480620064567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20568221263630614986838845 7713082973861480620064567)
          ·
            refine ⟨11569624460792220930096851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7713082973861480620064567 11569624460792220930096851)
            ·
              refine ⟨17354436691188331395145277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11569624460792220930096851 17354436691188331395145277)
              ·
                refine ⟨6507913759195624273179479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17354436691188331395145277 6507913759195624273179479)
                ·
                  refine ⟨9761870638793436409769219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6507913759195624273179479 9761870638793436409769219)
                  ·
                    refine ⟨14642805958190154614653829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9761870638793436409769219 14642805958190154614653829)
                    ·
                      refine ⟨2745526117160653990247593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14642805958190154614653829 2745526117160653990247593)
                      ·
                        rfl

theorem cell23_5346893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_5346893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346893 prefixEnd_5346893 := by exact prefixLift 5346893
  have htrace : WordTrace (prefixWord ++ tailWord_5346893) baseStart_5346893 baseEnd_5346893 := by
    simpa [prefixWord, tailWord_5346893, baseEnd_5346893] using wordTrace_append hprefix tailTrace_5346893
  have hstable : (prefixWord ++ tailWord_5346893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346893).length < 2 ^ (prefixWord ++ tailWord_5346893).sum := by decide
  have hdescent : baseEnd_5346893 < baseStart_5346893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5346989 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 9]
def baseStart_5346989 : Nat := 118140960795 + 5346989 * 2 ^ 59
def prefixEnd_5346989 : Nat := 4983230072969 + 3 ^ 40 * 5346989 * 2
def baseEnd_5346989 : Nat := 305063934589276179405239

theorem tailTrace_5346989 : CollatzResearch.WordTrace tailWord_5346989 prefixEnd_5346989 305063934589276179405239 := by
  unfold tailWord_5346989
  simp only [CollatzResearch.WordTrace]
  refine ⟨195020710425779520863300021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130013806950519680575533347 195020710425779520863300021)
  ·
    refine ⟨18283191602416830080934377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195020710425779520863300021 18283191602416830080934377)
    ·
      refine ⟨13712393701812622560700783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18283191602416830080934377 13712393701812622560700783)
      ·
        refine ⟨20568590552718933841051175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13712393701812622560700783 20568590552718933841051175)
        ·
          refine ⟨30852885829078400761576763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20568590552718933841051175 30852885829078400761576763)
          ·
            refine ⟨46279328743617601142365145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30852885829078400761576763 46279328743617601142365145)
            ·
              refine ⟨34709496557713200856773859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46279328743617601142365145 34709496557713200856773859)
              ·
                refine ⟨52064244836569801285160789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34709496557713200856773859 52064244836569801285160789)
                ·
                  refine ⟨305063934589276179405239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52064244836569801285160789 305063934589276179405239)
                  ·
                    rfl

theorem cell23_5346989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_5346989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5346989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5346989 prefixEnd_5346989 := by exact prefixLift 5346989
  have htrace : WordTrace (prefixWord ++ tailWord_5346989) baseStart_5346989 baseEnd_5346989 := by
    simpa [prefixWord, tailWord_5346989, baseEnd_5346989] using wordTrace_append hprefix tailTrace_5346989
  have hstable : (prefixWord ++ tailWord_5346989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5346989).length < 2 ^ (prefixWord ++ tailWord_5346989).sum := by decide
  have hdescent : baseEnd_5346989 < baseStart_5346989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5346989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347030 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 2, 2, 4]
def baseStart_5347030 : Nat := 118140960795 + 5347030 * 2 ^ 59
def prefixEnd_5347030 : Nat := 4983230072969 + 3 ^ 40 * 5347030 * 2
def baseEnd_5347030 : Nat := 2745596464010319954234463

theorem tailTrace_5347030 : CollatzResearch.WordTrace tailWord_5347030 prefixEnd_5347030 2745596464010319954234463 := by
  unfold tailWord_5347030
  simp only [CollatzResearch.WordTrace]
  refine ⟨12188887863664436554096409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130014803879087323243695029 12188887863664436554096409)
  ·
    refine ⟨9141665897748327415572307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12188887863664436554096409 9141665897748327415572307)
    ·
      refine ⟨13712498846622491123358461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9141665897748327415572307 13712498846622491123358461)
      ·
        refine ⟨5142187067483434171259423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13712498846622491123358461 5142187067483434171259423)
        ·
          refine ⟨7713280601225151256889135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5142187067483434171259423 7713280601225151256889135)
          ·
            refine ⟨11569920901837726885333703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7713280601225151256889135 11569920901837726885333703)
            ·
              refine ⟨17354881352756590328000555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11569920901837726885333703 17354881352756590328000555)
              ·
                refine ⟨26032322029134885492000833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17354881352756590328000555 26032322029134885492000833)
                ·
                  refine ⟨19524241521851164119000625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26032322029134885492000833 19524241521851164119000625)
                  ·
                    refine ⟨14643181141388373089250469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19524241521851164119000625 14643181141388373089250469)
                    ·
                      refine ⟨2745596464010319954234463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14643181141388373089250469 2745596464010319954234463)
                      ·
                        rfl

theorem cell23_5347030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_5347030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347030 prefixEnd_5347030 := by exact prefixLift 5347030
  have htrace : WordTrace (prefixWord ++ tailWord_5347030) baseStart_5347030 baseEnd_5347030 := by
    simpa [prefixWord, tailWord_5347030, baseEnd_5347030] using wordTrace_append hprefix tailTrace_5347030
  have hstable : (prefixWord ++ tailWord_5347030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347030).length < 2 ^ (prefixWord ++ tailWord_5347030).sum := by decide
  have hdescent : baseEnd_5347030 < baseStart_5347030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347039 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 4]
def baseStart_5347039 : Nat := 118140960795 + 5347039 * 2 ^ 59
def prefixEnd_5347039 : Nat := 4983230072969 + 3 ^ 40 * 5347039 * 2
def baseEnd_5347039 : Nat := 2745601085336210419021921

theorem tailTrace_5347039 : CollatzResearch.WordTrace tailWord_5347039 prefixEnd_5347039 2745601085336210419021921 := by
  unfold tailWord_5347039
  simp only [CollatzResearch.WordTrace]
  refine ⟨195022534075598379402620171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130015022717065586268413447 195022534075598379402620171)
  ·
    refine ⟨292533801113397569103930257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195022534075598379402620171 292533801113397569103930257)
    ·
      refine ⟨219400350835048176827947693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292533801113397569103930257 219400350835048176827947693)
      ·
        refine ⟨82275131563143066310480385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219400350835048176827947693 82275131563143066310480385)
        ·
          refine ⟨61706348672357299732860289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82275131563143066310480385 61706348672357299732860289)
          ·
            refine ⟨46279761504267974799645217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61706348672357299732860289 46279761504267974799645217)
            ·
              refine ⟨34709821128200981099733913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46279761504267974799645217 34709821128200981099733913)
              ·
                refine ⟨26032365846150735824800435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34709821128200981099733913 26032365846150735824800435)
                ·
                  refine ⟨39048548769226103737200653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26032365846150735824800435 39048548769226103737200653)
                  ·
                    refine ⟨14643205788459788901450245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39048548769226103737200653 14643205788459788901450245)
                    ·
                      refine ⟨2745601085336210419021921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14643205788459788901450245 2745601085336210419021921)
                      ·
                        rfl

theorem cell23_5347039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_5347039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347039 prefixEnd_5347039 := by exact prefixLift 5347039
  have htrace : WordTrace (prefixWord ++ tailWord_5347039) baseStart_5347039 baseEnd_5347039 := by
    simpa [prefixWord, tailWord_5347039, baseEnd_5347039] using wordTrace_append hprefix tailTrace_5347039
  have hstable : (prefixWord ++ tailWord_5347039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347039).length < 2 ^ (prefixWord ++ tailWord_5347039).sum := by decide
  have hdescent : baseEnd_5347039 < baseStart_5347039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347053 : List Nat := [1, 5, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_5347053 : Nat := 118140960795 + 5347053 * 2 ^ 59
def prefixEnd_5347053 : Nat := 4983230072969 + 3 ^ 40 * 5347053 * 2
def baseEnd_5347053 : Nat := 915202758021791121415619

theorem tailTrace_5347053 : CollatzResearch.WordTrace tailWord_5347053 prefixEnd_5347053 915202758021791121415619 := by
  unfold tailWord_5347053
  simp only [CollatzResearch.WordTrace]
  refine ⟨195023044697547659793629813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130015363131698439862419875 195023044697547659793629813)
  ·
    refine ⟨18283410440395093105652795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195023044697547659793629813 18283410440395093105652795)
    ·
      refine ⟨27425115660592639658479193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18283410440395093105652795 27425115660592639658479193)
      ·
        refine ⟨20568836745444479743859395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27425115660592639658479193 20568836745444479743859395)
        ·
          refine ⟨30853255118166719615789093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20568836745444479743859395 30853255118166719615789093)
          ·
            refine ⟨5784985334656259927960455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30853255118166719615789093 5784985334656259927960455)
            ·
              refine ⟨8677478001984389891940683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5784985334656259927960455 8677478001984389891940683)
              ·
                refine ⟨13016217002976584837911025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8677478001984389891940683 13016217002976584837911025)
                ·
                  refine ⟨9762162752232438628433269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13016217002976584837911025 9762162752232438628433269)
                  ·
                    refine ⟨915202758021791121415619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9762162752232438628433269 915202758021791121415619)
                    ·
                      rfl

theorem cell23_5347053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_5347053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347053 prefixEnd_5347053 := by exact prefixLift 5347053
  have htrace : WordTrace (prefixWord ++ tailWord_5347053) baseStart_5347053 baseEnd_5347053 := by
    simpa [prefixWord, tailWord_5347053, baseEnd_5347053] using wordTrace_append hprefix tailTrace_5347053
  have hstable : (prefixWord ++ tailWord_5347053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347053).length < 2 ^ (prefixWord ++ tailWord_5347053).sum := by decide
  have hdescent : baseEnd_5347053 < baseStart_5347053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347083 : List Nat := [1, 1, 1, 1, 5, 1, 4, 4, 1, 4]
def baseStart_5347083 : Nat := 118140960795 + 5347083 * 2 ^ 59
def prefixEnd_5347083 : Nat := 4983230072969 + 3 ^ 40 * 5347083 * 2
def baseEnd_5347083 : Nat := 915207892828336082290573

theorem tailTrace_5347083 : CollatzResearch.WordTrace tailWord_5347083 prefixEnd_5347083 915207892828336082290573 := by
  unfold tailWord_5347083
  simp only [CollatzResearch.WordTrace]
  refine ⟨195024138887438974917221903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130016092591625983278147935 195024138887438974917221903)
  ·
    refine ⟨292536208331158462375832855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195024138887438974917221903 292536208331158462375832855)
    ·
      refine ⟨438804312496737693563749283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292536208331158462375832855 438804312496737693563749283)
      ·
        refine ⟨658206468745106540345623925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438804312496737693563749283 658206468745106540345623925)
        ·
          refine ⟨61706856444853738157402243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 658206468745106540345623925 61706856444853738157402243)
          ·
            refine ⟨92560284667280607236103365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61706856444853738157402243 92560284667280607236103365)
            ·
              refine ⟨17355053375115113856769381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92560284667280607236103365 17355053375115113856769381)
              ·
                refine ⟨3254072507834083848144259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17355053375115113856769381 3254072507834083848144259)
                ·
                  refine ⟨4881108761751125772216389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254072507834083848144259 4881108761751125772216389)
                  ·
                    refine ⟨915207892828336082290573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4881108761751125772216389 915207892828336082290573)
                    ·
                      rfl

theorem cell23_5347083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 4, 1, 4].length) (baseStart_5347083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347083 prefixEnd_5347083 := by exact prefixLift 5347083
  have htrace : WordTrace (prefixWord ++ tailWord_5347083) baseStart_5347083 baseEnd_5347083 := by
    simpa [prefixWord, tailWord_5347083, baseEnd_5347083] using wordTrace_append hprefix tailTrace_5347083
  have hstable : (prefixWord ++ tailWord_5347083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347083).length < 2 ^ (prefixWord ++ tailWord_5347083).sum := by decide
  have hdescent : baseEnd_5347083 < baseStart_5347083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347090 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_5347090 : Nat := 118140960795 + 5347090 * 2 ^ 59
def prefixEnd_5347090 : Nat := 4983230072969 + 3 ^ 40 * 5347090 * 2
def baseEnd_5347090 : Nat := 2745627272849589719484187

theorem tailTrace_5347090 : CollatzResearch.WordTrace tailWord_5347090 prefixEnd_5347090 2745627272849589719484187 := by
  unfold tailWord_5347090
  simp only [CollatzResearch.WordTrace]
  refine ⟨48756098549603403778181681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130016262798942410075151149 48756098549603403778181681)
  ·
    refine ⟨36567073912202552833636261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48756098549603403778181681 36567073912202552833636261)
    ·
      refine ⟨6856326358537978656306799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36567073912202552833636261 6856326358537978656306799)
      ·
        refine ⟨10284489537806967984460199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6856326358537978656306799 10284489537806967984460199)
        ·
          refine ⟨15426734306710451976690299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10284489537806967984460199 15426734306710451976690299)
          ·
            refine ⟨23140101460065677965035449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15426734306710451976690299 23140101460065677965035449)
            ·
              refine ⟨17355076095049258473776587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23140101460065677965035449 17355076095049258473776587)
              ·
                refine ⟨26032614142573887710664881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17355076095049258473776587 26032614142573887710664881)
                ·
                  refine ⟨19524460606930415782998661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26032614142573887710664881 19524460606930415782998661)
                  ·
                    refine ⟨3660836363799452959312249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19524460606930415782998661 3660836363799452959312249)
                    ·
                      refine ⟨2745627272849589719484187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3660836363799452959312249 2745627272849589719484187)
                      ·
                        rfl

theorem cell23_5347090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_5347090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347090 prefixEnd_5347090 := by exact prefixLift 5347090
  have htrace : WordTrace (prefixWord ++ tailWord_5347090) baseStart_5347090 baseEnd_5347090 := by
    simpa [prefixWord, tailWord_5347090, baseEnd_5347090] using wordTrace_append hprefix tailTrace_5347090
  have hstable : (prefixWord ++ tailWord_5347090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347090).length < 2 ^ (prefixWord ++ tailWord_5347090).sum := by decide
  have hdescent : baseEnd_5347090 < baseStart_5347090 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347106 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 2, 5, 3]
def baseStart_5347106 : Nat := 118140960795 + 5347106 * 2 ^ 59
def prefixEnd_5347106 : Nat := 4983230072969 + 3 ^ 40 * 5347106 * 2
def baseEnd_5347106 : Nat := 2745635488540061656884113

theorem tailTrace_5347106 : CollatzResearch.WordTrace tailWord_5347106 prefixEnd_5347106 2745635488540061656884113 := by
  unfold tailWord_5347106
  simp only [CollatzResearch.WordTrace]
  refine ⟨48756244441588912461327293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130016651844237099896872781 48756244441588912461327293)
  ·
    refine ⟨18283591665595842172997735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48756244441588912461327293 18283591665595842172997735)
    ·
      refine ⟨27425387498393763259496603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18283591665595842172997735 27425387498393763259496603)
      ·
        refine ⟨41138081247590644889244905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27425387498393763259496603 41138081247590644889244905)
        ·
          refine ⟨30853560935692983666933679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41138081247590644889244905 30853560935692983666933679)
          ·
            refine ⟨46280341403539475500400519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30853560935692983666933679 46280341403539475500400519)
            ·
              refine ⟨69420512105309213250600779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46280341403539475500400519 69420512105309213250600779)
              ·
                refine ⟨104130768157963819875901169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69420512105309213250600779 104130768157963819875901169)
                ·
                  refine ⟨78098076118472864906925877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104130768157963819875901169 78098076118472864906925877)
                  ·
                    refine ⟨7321694636106831085024301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 78098076118472864906925877 7321694636106831085024301)
                    ·
                      refine ⟨2745635488540061656884113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7321694636106831085024301 2745635488540061656884113)
                      ·
                        rfl

theorem cell23_5347106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_5347106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347106 prefixEnd_5347106 := by exact prefixLift 5347106
  have htrace : WordTrace (prefixWord ++ tailWord_5347106) baseStart_5347106 baseEnd_5347106 := by
    simpa [prefixWord, tailWord_5347106, baseEnd_5347106] using wordTrace_append hprefix tailTrace_5347106
  have hstable : (prefixWord ++ tailWord_5347106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347106).length < 2 ^ (prefixWord ++ tailWord_5347106).sum := by decide
  have hdescent : baseEnd_5347106 < baseStart_5347106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347146 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 3, 1, 4]
def baseStart_5347146 : Nat := 118140960795 + 5347146 * 2 ^ 59
def prefixEnd_5347146 : Nat := 4983230072969 + 3 ^ 40 * 5347146 * 2
def baseEnd_5347146 : Nat := 2745656027766241500383929

theorem tailTrace_5347146 : CollatzResearch.WordTrace tailWord_5347146 prefixEnd_5347146 2745656027766241500383929 := by
  unfold tailWord_5347146
  simp only [CollatzResearch.WordTrace]
  refine ⟨48756609171552684169191323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130017624457473824451176861 48756609171552684169191323)
  ·
    refine ⟨73134913757329026253786985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48756609171552684169191323 73134913757329026253786985)
    ·
      refine ⟨54851185317996769690340239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73134913757329026253786985 54851185317996769690340239)
      ·
        refine ⟨82276777976995154535510359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54851185317996769690340239 82276777976995154535510359)
        ·
          refine ⟨123415166965492731803265539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82276777976995154535510359 123415166965492731803265539)
          ·
            refine ⟨185122750448239097704898309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123415166965492731803265539 185122750448239097704898309)
            ·
              refine ⟨34710515709044830819668433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185122750448239097704898309 34710515709044830819668433)
              ·
                refine ⟨26032886781783623114751325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34710515709044830819668433 26032886781783623114751325)
                ·
                  refine ⟨9762332543168858668031747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26032886781783623114751325 9762332543168858668031747)
                  ·
                    refine ⟨14643498814753288002047621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9762332543168858668031747 14643498814753288002047621)
                    ·
                      refine ⟨2745656027766241500383929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14643498814753288002047621 2745656027766241500383929)
                      ·
                        rfl

theorem cell23_5347146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_5347146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347146 prefixEnd_5347146 := by exact prefixLift 5347146
  have htrace : WordTrace (prefixWord ++ tailWord_5347146) baseStart_5347146 baseEnd_5347146 := by
    simpa [prefixWord, tailWord_5347146, baseEnd_5347146] using wordTrace_append hprefix tailTrace_5347146
  have hstable : (prefixWord ++ tailWord_5347146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347146).length < 2 ^ (prefixWord ++ tailWord_5347146).sum := by decide
  have hdescent : baseEnd_5347146 < baseStart_5347146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347169 : List Nat := [1, 2, 3, 1, 1, 1, 3, 11]
def baseStart_5347169 : Nat := 118140960795 + 5347169 * 2 ^ 59
def prefixEnd_5347169 : Nat := 4983230072969 + 3 ^ 40 * 5347169 * 2
def baseEnd_5347169 : Nat := 101691401400788700385049

theorem tailTrace_5347169 : CollatzResearch.WordTrace tailWord_5347169 prefixEnd_5347169 101691401400788700385049 := by
  unfold tailWord_5347169
  simp only [CollatzResearch.WordTrace]
  refine ⟨195027275565127411604852561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130018183710084941069901707 195027275565127411604852561)
  ·
    refine ⟨146270456673845558703639421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195027275565127411604852561 146270456673845558703639421)
    ·
      refine ⟨54851421252692084513864783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146270456673845558703639421 54851421252692084513864783)
      ·
        refine ⟨82277131879038126770797175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54851421252692084513864783 82277131879038126770797175)
        ·
          refine ⟨123415697818557190156195763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82277131879038126770797175 123415697818557190156195763)
          ·
            refine ⟨185123546727835785234293645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123415697818557190156195763 185123546727835785234293645)
            ·
              refine ⟨69421330022938419462860117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185123546727835785234293645 69421330022938419462860117)
              ·
                refine ⟨101691401400788700385049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 69421330022938419462860117 101691401400788700385049)
                ·
                  rfl

theorem cell23_5347169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 11].length) (baseStart_5347169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347169 prefixEnd_5347169 := by exact prefixLift 5347169
  have htrace : WordTrace (prefixWord ++ tailWord_5347169) baseStart_5347169 baseEnd_5347169 := by
    simpa [prefixWord, tailWord_5347169, baseEnd_5347169] using wordTrace_append hprefix tailTrace_5347169
  have hstable : (prefixWord ++ tailWord_5347169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347169).length < 2 ^ (prefixWord ++ tailWord_5347169).sum := by decide
  have hdescent : baseEnd_5347169 < baseStart_5347169 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347180 : List Nat := [2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 4]
def baseStart_5347180 : Nat := 118140960795 + 5347180 * 2 ^ 59
def prefixEnd_5347180 : Nat := 4983230072969 + 3 ^ 40 * 5347180 * 2
def baseEnd_5347180 : Nat := 2745673486108494367358773

theorem tailTrace_5347180 : CollatzResearch.WordTrace tailWord_5347180 prefixEnd_5347180 2745673486108494367358773 := by
  unfold tailWord_5347180
  simp only [CollatzResearch.WordTrace]
  refine ⟨97513838384043780241751497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130018451178725040322335329 97513838384043780241751497)
  ·
    refine ⟨73135378788032835181313623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97513838384043780241751497 73135378788032835181313623)
    ·
      refine ⟨109703068182049252771970435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73135378788032835181313623 109703068182049252771970435)
      ·
        refine ⟨164554602273073879157955653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109703068182049252771970435 164554602273073879157955653)
        ·
          refine ⟨30853987926201352342116685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164554602273073879157955653 30853987926201352342116685)
          ·
            refine ⟨11570245472325507128293757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30853987926201352342116685 11570245472325507128293757)
            ·
              refine ⟨4338842052122065173110159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11570245472325507128293757 4338842052122065173110159)
              ·
                refine ⟨6508263078183097759665239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4338842052122065173110159 6508263078183097759665239)
                ·
                  refine ⟨9762394617274646639497859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6508263078183097759665239 9762394617274646639497859)
                  ·
                    refine ⟨14643591925911969959246789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9762394617274646639497859 14643591925911969959246789)
                    ·
                      refine ⟨2745673486108494367358773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14643591925911969959246789 2745673486108494367358773)
                      ·
                        rfl

theorem cell23_5347180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 4].length) (baseStart_5347180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347180 prefixEnd_5347180 := by exact prefixLift 5347180
  have htrace : WordTrace (prefixWord ++ tailWord_5347180) baseStart_5347180 baseEnd_5347180 := by
    simpa [prefixWord, tailWord_5347180, baseEnd_5347180] using wordTrace_append hprefix tailTrace_5347180
  have hstable : (prefixWord ++ tailWord_5347180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347180).length < 2 ^ (prefixWord ++ tailWord_5347180).sum := by decide
  have hdescent : baseEnd_5347180 < baseStart_5347180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347210 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 1, 2, 4]
def baseStart_5347210 : Nat := 118140960795 + 5347210 * 2 ^ 59
def prefixEnd_5347210 : Nat := 4983230072969 + 3 ^ 40 * 5347210 * 2
def baseEnd_5347210 : Nat := 2745688890528129249983635

theorem tailTrace_5347210 : CollatzResearch.WordTrace tailWord_5347210 prefixEnd_5347210 2745688890528129249983635 := by
  unfold tailWord_5347210
  simp only [CollatzResearch.WordTrace]
  refine ⟨48757192739494718901773771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130019180638652583738063389 48757192739494718901773771)
  ·
    refine ⟨73135789109242078352660657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48757192739494718901773771 73135789109242078352660657)
    ·
      refine ⟨54851841831931558764495493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73135789109242078352660657 54851841831931558764495493)
      ·
        refine ⟨10284720343487167268342905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54851841831931558764495493 10284720343487167268342905)
        ·
          refine ⟨7713540257615375451257179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10284720343487167268342905 7713540257615375451257179)
          ·
            refine ⟨11570310386423063176885769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7713540257615375451257179 11570310386423063176885769)
            ·
              refine ⟨8677732789817297382664327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11570310386423063176885769 8677732789817297382664327)
              ·
                refine ⟨13016599184725946073996491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8677732789817297382664327 13016599184725946073996491)
                ·
                  refine ⟨19524898777088919110994737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13016599184725946073996491 19524898777088919110994737)
                  ·
                    refine ⟨14643674082816689333246053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19524898777088919110994737 14643674082816689333246053)
                    ·
                      refine ⟨2745688890528129249983635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14643674082816689333246053 2745688890528129249983635)
                      ·
                        rfl

theorem cell23_5347210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_5347210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347210 prefixEnd_5347210 := by exact prefixLift 5347210
  have htrace : WordTrace (prefixWord ++ tailWord_5347210) baseStart_5347210 baseEnd_5347210 := by
    simpa [prefixWord, tailWord_5347210, baseEnd_5347210] using wordTrace_append hprefix tailTrace_5347210
  have hstable : (prefixWord ++ tailWord_5347210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347210).length < 2 ^ (prefixWord ++ tailWord_5347210).sum := by decide
  have hdescent : baseEnd_5347210 < baseStart_5347210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347214 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2]
def baseStart_5347214 : Nat := 118140960795 + 5347214 * 2 ^ 59
def prefixEnd_5347214 : Nat := 4983230072969 + 3 ^ 40 * 5347214 * 2
def baseEnd_5347214 : Nat := 2745690944450747234333617

theorem tailTrace_5347214 : CollatzResearch.WordTrace tailWord_5347214 prefixEnd_5347214 2745690944450747234333617 := by
  unfold tailWord_5347214
  simp only [CollatzResearch.WordTrace]
  refine ⟨24378614606245548036280087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130019277899976256193493797 24378614606245548036280087)
  ·
    refine ⟨36567921909368322054420131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24378614606245548036280087 36567921909368322054420131)
    ·
      refine ⟨54851882864052483081630197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36567921909368322054420131 54851882864052483081630197)
      ·
        refine ⟨5142364018504920288902831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54851882864052483081630197 5142364018504920288902831)
        ·
          refine ⟨7713546027757380433354247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5142364018504920288902831 7713546027757380433354247)
          ·
            refine ⟨11570319041636070650031371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7713546027757380433354247 11570319041636070650031371)
            ·
              refine ⟨17355478562454105975047057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11570319041636070650031371 17355478562454105975047057)
              ·
                refine ⟨13016608921840579481285293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17355478562454105975047057 13016608921840579481285293)
                ·
                  refine ⟨4881228345690217305481985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13016608921840579481285293 4881228345690217305481985)
                  ·
                    refine ⟨3660921259267662979111489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4881228345690217305481985 3660921259267662979111489)
                    ·
                      refine ⟨2745690944450747234333617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3660921259267662979111489 2745690944450747234333617)
                      ·
                        rfl

theorem cell23_5347214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_5347214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347214 prefixEnd_5347214 := by exact prefixLift 5347214
  have htrace : WordTrace (prefixWord ++ tailWord_5347214) baseStart_5347214 baseEnd_5347214 := by
    simpa [prefixWord, tailWord_5347214, baseEnd_5347214] using wordTrace_append hprefix tailTrace_5347214
  have hstable : (prefixWord ++ tailWord_5347214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347214).length < 2 ^ (prefixWord ++ tailWord_5347214).sum := by decide
  have hdescent : baseEnd_5347214 < baseStart_5347214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347234 : List Nat := [3, 3, 1, 2, 3, 2, 2, 1, 1, 2, 3]
def baseStart_5347234 : Nat := 118140960795 + 5347234 * 2 ^ 59
def prefixEnd_5347234 : Nat := 4983230072969 + 3 ^ 40 * 5347234 * 2
def baseEnd_5347234 : Nat := 2745701214063837156083525

theorem tailTrace_5347234 : CollatzResearch.WordTrace tailWord_5347234 prefixEnd_5347234 2745701214063837156083525 := by
  unfold tailWord_5347234
  simp only [CollatzResearch.WordTrace]
  refine ⟨48757411577472981926492189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130019764206594618470645837 48757411577472981926492189)
  ·
    refine ⟨18284029341552368222434571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48757411577472981926492189 18284029341552368222434571)
    ·
      refine ⟨27426044012328552333651857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18284029341552368222434571 27426044012328552333651857)
      ·
        refine ⟨20569533009246414250238893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27426044012328552333651857 20569533009246414250238893)
        ·
          refine ⟨7713574878467405343839585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20569533009246414250238893 7713574878467405343839585)
          ·
            refine ⟨5785181158850554007879689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7713574878467405343839585 5785181158850554007879689)
            ·
              refine ⟨4338885869137915505909767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5785181158850554007879689 4338885869137915505909767)
              ·
                refine ⟨6508328803706873258864651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4338885869137915505909767 6508328803706873258864651)
                ·
                  refine ⟨9762493205560309888296977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6508328803706873258864651 9762493205560309888296977)
                  ·
                    refine ⟨7321869904170232416222733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9762493205560309888296977 7321869904170232416222733)
                    ·
                      refine ⟨2745701214063837156083525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7321869904170232416222733 2745701214063837156083525)
                      ·
                        rfl

theorem cell23_5347234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_5347234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347234 prefixEnd_5347234 := by exact prefixLift 5347234
  have htrace : WordTrace (prefixWord ++ tailWord_5347234) baseStart_5347234 baseEnd_5347234 := by
    simpa [prefixWord, tailWord_5347234, baseEnd_5347234] using wordTrace_append hprefix tailTrace_5347234
  have hstable : (prefixWord ++ tailWord_5347234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347234).length < 2 ^ (prefixWord ++ tailWord_5347234).sum := by decide
  have hdescent : baseEnd_5347234 < baseStart_5347234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347310 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 7]
def baseStart_5347310 : Nat := 118140960795 + 5347310 * 2 ^ 59
def prefixEnd_5347310 : Nat := 4983230072969 + 3 ^ 40 * 5347310 * 2
def baseEnd_5347310 : Nat := 305082248732619873192575

theorem tailTrace_5347310 : CollatzResearch.WordTrace tailWord_5347310 prefixEnd_5347310 305082248732619873192575 := by
  unfold tailWord_5347310
  simp only [CollatzResearch.WordTrace]
  refine ⟨24379052282202074085716923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130021612171744395123823589 24379052282202074085716923)
  ·
    refine ⟨36568578423303111128575385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24379052282202074085716923 36568578423303111128575385)
    ·
      refine ⟨27426433817477333346431539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36568578423303111128575385 27426433817477333346431539)
      ·
        refine ⟨41139650726216000019647309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27426433817477333346431539 41139650726216000019647309)
        ·
          refine ⟨15427369022331000007367741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41139650726216000019647309 15427369022331000007367741)
          ·
            refine ⟨5785263383374125002762903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15427369022331000007367741 5785263383374125002762903)
            ·
              refine ⟨8677895075061187504144355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5785263383374125002762903 8677895075061187504144355)
              ·
                refine ⟨13016842612591781256216533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8677895075061187504144355 13016842612591781256216533)
                ·
                  refine ⟨305082248732619873192575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13016842612591781256216533 305082248732619873192575)
                  ·
                    rfl

theorem cell23_5347310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_5347310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347310 prefixEnd_5347310 := by exact prefixLift 5347310
  have htrace : WordTrace (prefixWord ++ tailWord_5347310) baseStart_5347310 baseEnd_5347310 := by
    simpa [prefixWord, tailWord_5347310, baseEnd_5347310] using wordTrace_append hprefix tailTrace_5347310
  have hstable : (prefixWord ++ tailWord_5347310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347310).length < 2 ^ (prefixWord ++ tailWord_5347310).sum := by decide
  have hdescent : baseEnd_5347310 < baseStart_5347310 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347383 : List Nat := [1, 1, 3, 1, 2, 2, 4, 3, 6]
def baseStart_5347383 : Nat := 118140960795 + 5347383 * 2 ^ 59
def prefixEnd_5347383 : Nat := 4983230072969 + 3 ^ 40 * 5347383 * 2
def baseEnd_5347383 : Nat := 305086413631261897013371

theorem tailTrace_5347383 : CollatzResearch.WordTrace tailWord_5347383 prefixEnd_5347383 305086413631261897013371 := by
  unfold tailWord_5347383
  simp only [CollatzResearch.WordTrace]
  refine ⟨195035080786352126153142803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130023387190901417435428535 195035080786352126153142803)
  ·
    refine ⟨292552621179528189229714205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195035080786352126153142803 292552621179528189229714205)
    ·
      refine ⟨109707232942323070961142827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292552621179528189229714205 109707232942323070961142827)
      ·
        refine ⟨164560849413484606441714241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109707232942323070961142827 164560849413484606441714241)
        ·
          refine ⟨123420637060113454831285681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164560849413484606441714241 123420637060113454831285681)
          ·
            refine ⟨92565477795085091123464261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123420637060113454831285681 92565477795085091123464261)
            ·
              refine ⟨17356027086578454585649549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92565477795085091123464261 17356027086578454585649549)
              ·
                refine ⟨6508510157466920469618581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17356027086578454585649549 6508510157466920469618581)
                ·
                  refine ⟨305086413631261897013371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6508510157466920469618581 305086413631261897013371)
                  ·
                    rfl

theorem cell23_5347383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 6].length) (baseStart_5347383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347383 prefixEnd_5347383 := by exact prefixLift 5347383
  have htrace : WordTrace (prefixWord ++ tailWord_5347383) baseStart_5347383 baseEnd_5347383 := by
    simpa [prefixWord, tailWord_5347383, baseEnd_5347383] using wordTrace_append hprefix tailTrace_5347383
  have hstable : (prefixWord ++ tailWord_5347383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347383).length < 2 ^ (prefixWord ++ tailWord_5347383).sum := by decide
  have hdescent : baseEnd_5347383 < baseStart_5347383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347460 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_5347460 : Nat := 118140960795 + 5347460 * 2 ^ 59
def prefixEnd_5347460 : Nat := 4983230072969 + 3 ^ 40 * 5347460 * 2
def baseEnd_5347460 : Nat := 915272420230584423952495

theorem tailTrace_5347460 : CollatzResearch.WordTrace tailWord_5347460 prefixEnd_5347460 915272420230584423952495 := by
  unfold tailWord_5347460
  simp only [CollatzResearch.WordTrace]
  refine ⟨97518944603536584151847917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130025259471382112202463889 97518944603536584151847917)
  ·
    refine ⟨36569604226326219056942969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97518944603536584151847917 36569604226326219056942969)
    ·
      refine ⟨27427203169744664292707227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36569604226326219056942969 27427203169744664292707227)
      ·
        refine ⟨41140804754616996439060841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27427203169744664292707227 41140804754616996439060841)
        ·
          refine ⟨30855603565962747329295631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41140804754616996439060841 30855603565962747329295631)
          ·
            refine ⟨46283405348944120993943447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30855603565962747329295631 46283405348944120993943447)
            ·
              refine ⟨69425108023416181490915171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46283405348944120993943447 69425108023416181490915171)
              ·
                refine ⟨104137662035124272236372757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69425108023416181490915171 104137662035124272236372757)
                ·
                  refine ⟨4881452907896450261079973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 104137662035124272236372757 4881452907896450261079973)
                  ·
                    refine ⟨915272420230584423952495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4881452907896450261079973 915272420230584423952495)
                    ·
                      rfl

theorem cell23_5347460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_5347460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347460 prefixEnd_5347460 := by exact prefixLift 5347460
  have htrace : WordTrace (prefixWord ++ tailWord_5347460) baseStart_5347460 baseEnd_5347460 := by
    simpa [prefixWord, tailWord_5347460, baseEnd_5347460] using wordTrace_append hprefix tailTrace_5347460
  have hstable : (prefixWord ++ tailWord_5347460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347460).length < 2 ^ (prefixWord ++ tailWord_5347460).sum := by decide
  have hdescent : baseEnd_5347460 < baseStart_5347460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347461 : List Nat := [1, 3, 1, 1, 5, 3, 1, 3, 1, 1, 3]
def baseStart_5347461 : Nat := 118140960795 + 5347461 * 2 ^ 59
def prefixEnd_5347461 : Nat := 4983230072969 + 3 ^ 40 * 5347461 * 2
def baseEnd_5347461 : Nat := 2745817774172407767944981

theorem tailTrace_5347461 : CollatzResearch.WordTrace tailWord_5347461 prefixEnd_5347461 2745817774172407767944981 := by
  unfold tailWord_5347461
  simp only [CollatzResearch.WordTrace]
  refine ⟨195037925680069545474482237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130025283786713030316321491 195037925680069545474482237)
  ·
    refine ⟨73139222130026079552930839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195037925680069545474482237 73139222130026079552930839)
    ·
      refine ⟨109708833195039119329396259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73139222130026079552930839 109708833195039119329396259)
      ·
        refine ⟨164563249792558678994094389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109708833195039119329396259 164563249792558678994094389)
        ·
          refine ⟨15427804668052376155696349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164563249792558678994094389 15427804668052376155696349)
          ·
            refine ⟨5785426750519641058386131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15427804668052376155696349 5785426750519641058386131)
            ·
              refine ⟨8678140125779461587579197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5785426750519641058386131 8678140125779461587579197)
              ·
                refine ⟨3254302547167298095342199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8678140125779461587579197 3254302547167298095342199)
                ·
                  refine ⟨4881453820750947143013299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254302547167298095342199 4881453820750947143013299)
                  ·
                    refine ⟨7322180731126420714519949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4881453820750947143013299 7322180731126420714519949)
                    ·
                      refine ⟨2745817774172407767944981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7322180731126420714519949 2745817774172407767944981)
                      ·
                        rfl

theorem cell23_5347461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 1, 3, 1, 1, 3].length) (baseStart_5347461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347461 prefixEnd_5347461 := by exact prefixLift 5347461
  have htrace : WordTrace (prefixWord ++ tailWord_5347461) baseStart_5347461 baseEnd_5347461 := by
    simpa [prefixWord, tailWord_5347461, baseEnd_5347461] using wordTrace_append hprefix tailTrace_5347461
  have hstable : (prefixWord ++ tailWord_5347461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347461).length < 2 ^ (prefixWord ++ tailWord_5347461).sum := by decide
  have hdescent : baseEnd_5347461 < baseStart_5347461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347490 : List Nat := [3, 3, 1, 3, 1, 1, 1, 10]
def baseStart_5347490 : Nat := 118140960795 + 5347490 * 2 ^ 59
def prefixEnd_5347490 : Nat := 4983230072969 + 3 ^ 40 * 5347490 * 2
def baseEnd_5347490 : Nat := 101697506115236598314161

theorem tailTrace_5347490 : CollatzResearch.WordTrace tailWord_5347490 prefixEnd_5347490 101697506115236598314161 := by
  unfold tailWord_5347490
  simp only [CollatzResearch.WordTrace]
  refine ⟨48759745849241120856821981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130025988931309655618191949 48759745849241120856821981)
  ·
    refine ⟨18284904693465420321308243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48759745849241120856821981 18284904693465420321308243)
    ·
      refine ⟨27427357040198130481962365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18284904693465420321308243 27427357040198130481962365)
      ·
        refine ⟨10285258890074298930735887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27427357040198130481962365 10285258890074298930735887)
        ·
          refine ⟨15427888335111448396103831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10285258890074298930735887 15427888335111448396103831)
          ·
            refine ⟨23141832502667172594155747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15427888335111448396103831 23141832502667172594155747)
            ·
              refine ⟨34712748754000758891233621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23141832502667172594155747 34712748754000758891233621)
              ·
                refine ⟨101697506115236598314161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 34712748754000758891233621 101697506115236598314161)
                ·
                  rfl

theorem cell23_5347490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 10].length) (baseStart_5347490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347490 prefixEnd_5347490 := by exact prefixLift 5347490
  have htrace : WordTrace (prefixWord ++ tailWord_5347490) baseStart_5347490 baseEnd_5347490 := by
    simpa [prefixWord, tailWord_5347490, baseEnd_5347490] using wordTrace_append hprefix tailTrace_5347490
  have hstable : (prefixWord ++ tailWord_5347490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347490).length < 2 ^ (prefixWord ++ tailWord_5347490).sum := by decide
  have hdescent : baseEnd_5347490 < baseStart_5347490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347493 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 6]
def baseStart_5347493 : Nat := 118140960795 + 5347493 * 2 ^ 59
def prefixEnd_5347493 : Nat := 4983230072969 + 3 ^ 40 * 5347493 * 2
def baseEnd_5347493 : Nat := 2745834205553351642744833

theorem tailTrace_5347493 : CollatzResearch.WordTrace tailWord_5347493 prefixEnd_5347493 2745834205553351642744833 := by
  unfold tailWord_5347493
  simp only [CollatzResearch.WordTrace]
  refine ⟨195039092815953614939647133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130026061877302409959764755 195039092815953614939647133)
  ·
    refine ⟨73139659805982605602367675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195039092815953614939647133 73139659805982605602367675)
    ·
      refine ⟨109709489708973908403551513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73139659805982605602367675 109709489708973908403551513)
      ·
        refine ⟨82282117281730431302663635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109709489708973908403551513 82282117281730431302663635)
        ·
          refine ⟨123423175922595646953995453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82282117281730431302663635 123423175922595646953995453)
          ·
            refine ⟨46283690970973367607748295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123423175922595646953995453 46283690970973367607748295)
            ·
              refine ⟨69425536456460051411622443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46283690970973367607748295 69425536456460051411622443)
              ·
                refine ⟨104138304684690077117433665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69425536456460051411622443 104138304684690077117433665)
                ·
                  refine ⟨78103728513517557838075249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104138304684690077117433665 78103728513517557838075249)
                  ·
                    refine ⟨58577796385138168378556437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78103728513517557838075249 58577796385138168378556437)
                    ·
                      refine ⟨2745834205553351642744833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58577796385138168378556437 2745834205553351642744833)
                      ·
                        rfl

theorem cell23_5347493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_5347493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347493 prefixEnd_5347493 := by exact prefixLift 5347493
  have htrace : WordTrace (prefixWord ++ tailWord_5347493) baseStart_5347493 baseEnd_5347493 := by
    simpa [prefixWord, tailWord_5347493, baseEnd_5347493] using wordTrace_append hprefix tailTrace_5347493
  have hstable : (prefixWord ++ tailWord_5347493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347493).length < 2 ^ (prefixWord ++ tailWord_5347493).sum := by decide
  have hdescent : baseEnd_5347493 < baseStart_5347493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347521 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 1, 1, 5]
def baseStart_5347521 : Nat := 118140960795 + 5347521 * 2 ^ 59
def prefixEnd_5347521 : Nat := 4983230072969 + 3 ^ 40 * 5347521 * 2
def baseEnd_5347521 : Nat := 2745848583011677533194705

theorem tailTrace_5347521 : CollatzResearch.WordTrace tailWord_5347521 prefixEnd_5347521 2745848583011677533194705 := by
  unfold tailWord_5347521
  simp only [CollatzResearch.WordTrace]
  refine ⟨195040114059852175721666417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130026742706568117147777611 195040114059852175721666417)
  ·
    refine ⟨146280085544889131791249813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195040114059852175721666417 146280085544889131791249813)
    ·
      refine ⟨6856879009916678052714835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 146280085544889131791249813 6856879009916678052714835)
      ·
        refine ⟨10285318514875017079072253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6856879009916678052714835 10285318514875017079072253)
        ·
          refine ⟨3856994443078131404652095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10285318514875017079072253 3856994443078131404652095)
          ·
            refine ⟨5785491664617197106978143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3856994443078131404652095 5785491664617197106978143)
            ·
              refine ⟨8678237496925795660467215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5785491664617197106978143 8678237496925795660467215)
              ·
                refine ⟨13017356245388693490700823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8678237496925795660467215 13017356245388693490700823)
                ·
                  refine ⟨19526034368083040236051235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13017356245388693490700823 19526034368083040236051235)
                  ·
                    refine ⟨29289051552124560354076853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19526034368083040236051235 29289051552124560354076853)
                    ·
                      refine ⟨2745848583011677533194705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29289051552124560354076853 2745848583011677533194705)
                      ·
                        rfl

theorem cell23_5347521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 1, 1, 5].length) (baseStart_5347521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347521 prefixEnd_5347521 := by exact prefixLift 5347521
  have htrace : WordTrace (prefixWord ++ tailWord_5347521) baseStart_5347521 baseEnd_5347521 := by
    simpa [prefixWord, tailWord_5347521, baseEnd_5347521] using wordTrace_append hprefix tailTrace_5347521
  have hstable : (prefixWord ++ tailWord_5347521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347521).length < 2 ^ (prefixWord ++ tailWord_5347521).sum := by decide
  have hdescent : baseEnd_5347521 < baseStart_5347521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347534 : List Nat := [4, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3]
def baseStart_5347534 : Nat := 118140960795 + 5347534 * 2 ^ 59
def prefixEnd_5347534 : Nat := 4983230072969 + 3 ^ 40 * 5347534 * 2
def baseEnd_5347534 : Nat := 2745855258260185982332145

theorem tailTrace_5347534 : CollatzResearch.WordTrace tailWord_5347534 prefixEnd_5347534 2745855258260185982332145 := by
  unfold tailWord_5347534
  simp only [CollatzResearch.WordTrace]
  refine ⟨24380073526100634867736207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130027058805870052627926437 24380073526100634867736207)
  ·
    refine ⟨36570110289150952301604311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24380073526100634867736207 36570110289150952301604311)
    ·
      refine ⟨54855165433726428452406467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36570110289150952301604311 54855165433726428452406467)
      ·
        refine ⟨82282748150589642678609701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54855165433726428452406467 82282748150589642678609701)
        ·
          refine ⟨15428015278235558002239319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82282748150589642678609701 15428015278235558002239319)
          ·
            refine ⟨23142022917353337003358979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15428015278235558002239319 23142022917353337003358979)
            ·
              refine ⟨34713034376030005505038469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23142022917353337003358979 34713034376030005505038469)
              ·
                refine ⟨6508693945505626032194713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34713034376030005505038469 6508693945505626032194713)
                ·
                  refine ⟨4881520459129219524146035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6508693945505626032194713 4881520459129219524146035)
                  ·
                    refine ⟨7322280688693829286219053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4881520459129219524146035 7322280688693829286219053)
                    ·
                      refine ⟨2745855258260185982332145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7322280688693829286219053 2745855258260185982332145)
                      ·
                        rfl

theorem cell23_5347534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_5347534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347534 prefixEnd_5347534 := by exact prefixLift 5347534
  have htrace : WordTrace (prefixWord ++ tailWord_5347534) baseStart_5347534 baseEnd_5347534 := by
    simpa [prefixWord, tailWord_5347534, baseEnd_5347534] using wordTrace_append hprefix tailTrace_5347534
  have hstable : (prefixWord ++ tailWord_5347534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347534).length < 2 ^ (prefixWord ++ tailWord_5347534).sum := by decide
  have hdescent : baseEnd_5347534 < baseStart_5347534 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347574 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2]
def baseStart_5347574 : Nat := 118140960795 + 5347574 * 2 ^ 59
def prefixEnd_5347574 : Nat := 4983230072969 + 3 ^ 40 * 5347574 * 2
def baseEnd_5347574 : Nat := 2745875797486365825831961

theorem tailTrace_5347574 : CollatzResearch.WordTrace tailWord_5347574 prefixEnd_5347574 2745875797486365825831961 := by
  unfold tailWord_5347574
  simp only [CollatzResearch.WordTrace]
  refine ⟨12190127945541260360834111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130028031419106777182230517 12190127945541260360834111)
  ·
    refine ⟨18285191918311890541251167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12190127945541260360834111 18285191918311890541251167)
    ·
      refine ⟨27427787877467835811876751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18285191918311890541251167 27427787877467835811876751)
      ·
        refine ⟨41141681816201753717815127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27427787877467835811876751 41141681816201753717815127)
        ·
          refine ⟨61712522724302630576722691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41141681816201753717815127 61712522724302630576722691)
          ·
            refine ⟨92568784086453945865084037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61712522724302630576722691 92568784086453945865084037)
            ·
              refine ⟨17356647016210114849703257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92568784086453945865084037 17356647016210114849703257)
              ·
                refine ⟨13017485262157586137277443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17356647016210114849703257 13017485262157586137277443)
                ·
                  refine ⟨19526227893236379205916165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13017485262157586137277443 19526227893236379205916165)
                  ·
                    refine ⟨3661167729981821101109281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19526227893236379205916165 3661167729981821101109281)
                    ·
                      refine ⟨2745875797486365825831961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3661167729981821101109281 2745875797486365825831961)
                      ·
                        rfl

theorem cell23_5347574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 1, 4, 2].length) (baseStart_5347574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347574 prefixEnd_5347574 := by exact prefixLift 5347574
  have htrace : WordTrace (prefixWord ++ tailWord_5347574) baseStart_5347574 baseEnd_5347574 := by
    simpa [prefixWord, tailWord_5347574, baseEnd_5347574] using wordTrace_append hprefix tailTrace_5347574
  have hstable : (prefixWord ++ tailWord_5347574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347574).length < 2 ^ (prefixWord ++ tailWord_5347574).sum := by decide
  have hdescent : baseEnd_5347574 < baseStart_5347574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347607 : List Nat := [1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 3]
def baseStart_5347607 : Nat := 118140960795 + 5347607 * 2 ^ 59
def prefixEnd_5347607 : Nat := 4983230072969 + 3 ^ 40 * 5347607 * 2
def baseEnd_5347607 : Nat := 2745892742347964196719309

theorem tailTrace_5347607 : CollatzResearch.WordTrace tailWord_5347607 prefixEnd_5347607 2745892742347964196719309 := by
  unfold tailWord_5347607
  simp only [CollatzResearch.WordTrace]
  refine ⟨195043250737540612409297075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130028833825027074939531383 195043250737540612409297075)
  ·
    refine ⟨292564876106310918613945613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195043250737540612409297075 292564876106310918613945613)
    ·
      refine ⟨109711828539866594480229605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292564876106310918613945613 109711828539866594480229605)
      ·
        refine ⟨20570967851224986465043051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109711828539866594480229605 20570967851224986465043051)
        ·
          refine ⟨30856451776837479697564577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20570967851224986465043051 30856451776837479697564577)
          ·
            refine ⟨23142338832628109773173433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30856451776837479697564577 23142338832628109773173433)
            ·
              refine ⟨17356754124471082329880075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23142338832628109773173433 17356754124471082329880075)
              ·
                refine ⟨26035131186706623494820113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17356754124471082329880075 26035131186706623494820113)
                ·
                  refine ⟨19526348390029967621115085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26035131186706623494820113 19526348390029967621115085)
                  ·
                    refine ⟨7322380646261237857918157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19526348390029967621115085 7322380646261237857918157)
                    ·
                      refine ⟨2745892742347964196719309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7322380646261237857918157 2745892742347964196719309)
                      ·
                        rfl

theorem cell23_5347607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_5347607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347607 prefixEnd_5347607 := by exact prefixLift 5347607
  have htrace : WordTrace (prefixWord ++ tailWord_5347607) baseStart_5347607 baseEnd_5347607 := by
    simpa [prefixWord, tailWord_5347607, baseEnd_5347607] using wordTrace_append hprefix tailTrace_5347607
  have hstable : (prefixWord ++ tailWord_5347607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347607).length < 2 ^ (prefixWord ++ tailWord_5347607).sum := by decide
  have hdescent : baseEnd_5347607 < baseStart_5347607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347614 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 7]
def baseStart_5347614 : Nat := 118140960795 + 5347614 * 2 ^ 59
def prefixEnd_5347614 : Nat := 4983230072969 + 3 ^ 40 * 5347614 * 2
def baseEnd_5347614 : Nat := 305099592968060629925753

theorem tailTrace_5347614 : CollatzResearch.WordTrace tailWord_5347614 prefixEnd_5347614 305099592968060629925753 := by
  unfold tailWord_5347614
  simp only [CollatzResearch.WordTrace]
  refine ⟨24380438256064406575600237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130029004032343501736534597 24380438256064406575600237)
  ·
    refine ⟨9142664346024152465850089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24380438256064406575600237 9142664346024152465850089)
    ·
      refine ⟨6856998259518114349387567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9142664346024152465850089 6856998259518114349387567)
      ·
        refine ⟨10285497389277171524081351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6856998259518114349387567 10285497389277171524081351)
        ·
          refine ⟨15428246083915757286122027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10285497389277171524081351 15428246083915757286122027)
          ·
            refine ⟨23142369125873635929183041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15428246083915757286122027 23142369125873635929183041)
            ·
              refine ⟨17356776844405226946887281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23142369125873635929183041 17356776844405226946887281)
              ·
                refine ⟨13017582633303920210165461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17356776844405226946887281 13017582633303920210165461)
                ·
                  refine ⟨305099592968060629925753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13017582633303920210165461 305099592968060629925753)
                  ·
                    rfl

theorem cell23_5347614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_5347614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347614 prefixEnd_5347614 := by exact prefixLift 5347614
  have htrace : WordTrace (prefixWord ++ tailWord_5347614) baseStart_5347614 baseEnd_5347614 := by
    simpa [prefixWord, tailWord_5347614, baseEnd_5347614] using wordTrace_append hprefix tailTrace_5347614
  have hstable : (prefixWord ++ tailWord_5347614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347614).length < 2 ^ (prefixWord ++ tailWord_5347614).sum := by decide
  have hdescent : baseEnd_5347614 < baseStart_5347614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347617 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 2, 5, 2]
def baseStart_5347617 : Nat := 118140960795 + 5347617 * 2 ^ 59
def prefixEnd_5347617 : Nat := 4983230072969 + 3 ^ 40 * 5347617 * 2
def baseEnd_5347617 : Nat := 2745897877154509157594263

theorem tailTrace_5347617 : CollatzResearch.WordTrace tailWord_5347617 prefixEnd_5347617 2745897877154509157594263 := by
  unfold tailWord_5347617
  simp only [CollatzResearch.WordTrace]
  refine ⟨195043615467504384117161105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130029076978336256078107403 195043615467504384117161105)
  ·
    refine ⟨146282711600628288087870829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195043615467504384117161105 146282711600628288087870829)
    ·
      refine ⟨54856016850235608032951561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146282711600628288087870829 54856016850235608032951561)
      ·
        refine ⟨41142012637676706024713671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54856016850235608032951561 41142012637676706024713671)
        ·
          refine ⟨61713018956515059037070507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41142012637676706024713671 61713018956515059037070507)
          ·
            refine ⟨92569528434772588555605761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61713018956515059037070507 92569528434772588555605761)
            ·
              refine ⟨69427146326079441416704321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92569528434772588555605761 69427146326079441416704321)
              ·
                refine ⟨52070359744559581062528241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69427146326079441416704321 52070359744559581062528241)
                ·
                  refine ⟨39052769808419685796896181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52070359744559581062528241 39052769808419685796896181)
                  ·
                    refine ⟨3661197169539345543459017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39052769808419685796896181 3661197169539345543459017)
                    ·
                      refine ⟨2745897877154509157594263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3661197169539345543459017 2745897877154509157594263)
                      ·
                        rfl

theorem cell23_5347617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_5347617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347617 prefixEnd_5347617 := by exact prefixLift 5347617
  have htrace : WordTrace (prefixWord ++ tailWord_5347617) baseStart_5347617 baseEnd_5347617 := by
    simpa [prefixWord, tailWord_5347617, baseEnd_5347617] using wordTrace_append hprefix tailTrace_5347617
  have hstable : (prefixWord ++ tailWord_5347617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347617).length < 2 ^ (prefixWord ++ tailWord_5347617).sum := by decide
  have hdescent : baseEnd_5347617 < baseStart_5347617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347647 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 4]
def baseStart_5347647 : Nat := 118140960795 + 5347647 * 2 ^ 59
def prefixEnd_5347647 : Nat := 4983230072969 + 3 ^ 40 * 5347647 * 2
def baseEnd_5347647 : Nat := 2745913281574144040219125

theorem tailTrace_5347647 : CollatzResearch.WordTrace tailWord_5347647 prefixEnd_5347647 2745913281574144040219125 := by
  unfold tailWord_5347647
  simp only [CollatzResearch.WordTrace]
  refine ⟨195044709657395699240753195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130029806438263799493835463 195044709657395699240753195)
  ·
    refine ⟨292567064486093548861129793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195044709657395699240753195 292567064486093548861129793)
    ·
      refine ⟨219425298364570161645847345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292567064486093548861129793 219425298364570161645847345)
      ·
        refine ⟨164568973773427621234385509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219425298364570161645847345 164568973773427621234385509)
        ·
          refine ⟨30856682582517678981447283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164568973773427621234385509 30856682582517678981447283)
          ·
            refine ⟨46285023873776518472170925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30856682582517678981447283 46285023873776518472170925)
            ·
              refine ⟨17356883952666194427064097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46285023873776518472170925 17356883952666194427064097)
              ·
                refine ⟨13017662964499645820298073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17356883952666194427064097 13017662964499645820298073)
                ·
                  refine ⟨9763247223374734365223555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13017662964499645820298073 9763247223374734365223555)
                  ·
                    refine ⟨14644870835062101547835333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9763247223374734365223555 14644870835062101547835333)
                    ·
                      refine ⟨2745913281574144040219125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14644870835062101547835333 2745913281574144040219125)
                      ·
                        rfl

theorem cell23_5347647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_5347647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347647 prefixEnd_5347647 := by exact prefixLift 5347647
  have htrace : WordTrace (prefixWord ++ tailWord_5347647) baseStart_5347647 baseEnd_5347647 := by
    simpa [prefixWord, tailWord_5347647, baseEnd_5347647] using wordTrace_append hprefix tailTrace_5347647
  have hstable : (prefixWord ++ tailWord_5347647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347647).length < 2 ^ (prefixWord ++ tailWord_5347647).sum := by decide
  have hdescent : baseEnd_5347647 < baseStart_5347647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347684 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_5347684 : Nat := 118140960795 + 5347684 * 2 ^ 59
def prefixEnd_5347684 : Nat := 4983230072969 + 3 ^ 40 * 5347684 * 2
def baseEnd_5347684 : Nat := 2745932280358360395456455

theorem tailTrace_5347684 : CollatzResearch.WordTrace tailWord_5347684 prefixEnd_5347684 2745932280358360395456455 := by
  unfold tailWord_5347684
  simp only [CollatzResearch.WordTrace]
  refine ⟨97523029579130827279925053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130030706105507769706566737 97523029579130827279925053)
  ·
    refine ⟨36571136092174060229971895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97523029579130827279925053 36571136092174060229971895)
    ·
      refine ⟨54856704138261090344957843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36571136092174060229971895 54856704138261090344957843)
      ·
        refine ⟨82285056207391635517436765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54856704138261090344957843 82285056207391635517436765)
        ·
          refine ⟨30856896077771863319038787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82285056207391635517436765 30856896077771863319038787)
          ·
            refine ⟨46285344116657794978558181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30856896077771863319038787 46285344116657794978558181)
            ·
              refine ⟨8678502021873336558479659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46285344116657794978558181 8678502021873336558479659)
              ·
                refine ⟨13017753032810004837719489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8678502021873336558479659 13017753032810004837719489)
                ·
                  refine ⟨9763314774607503628289617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13017753032810004837719489 9763314774607503628289617)
                  ·
                    refine ⟨7322486080955627721217213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9763314774607503628289617 7322486080955627721217213)
                    ·
                      refine ⟨2745932280358360395456455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7322486080955627721217213 2745932280358360395456455)
                      ·
                        rfl

theorem cell23_5347684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_5347684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347684 prefixEnd_5347684 := by exact prefixLift 5347684
  have htrace : WordTrace (prefixWord ++ tailWord_5347684) baseStart_5347684 baseEnd_5347684 := by
    simpa [prefixWord, tailWord_5347684, baseEnd_5347684] using wordTrace_append hprefix tailTrace_5347684
  have hstable : (prefixWord ++ tailWord_5347684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347684).length < 2 ^ (prefixWord ++ tailWord_5347684).sum := by decide
  have hdescent : baseEnd_5347684 < baseStart_5347684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347737 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 3, 1, 4]
def baseStart_5347737 : Nat := 118140960795 + 5347737 * 2 ^ 59
def prefixEnd_5347737 : Nat := 4983230072969 + 3 ^ 40 * 5347737 * 2
def baseEnd_5347737 : Nat := 2745959494833048688093711

theorem tailTrace_5347737 : CollatzResearch.WordTrace tailWord_5347737 prefixEnd_5347737 2745959494833048688093711 := by
  unfold tailWord_5347737
  simp only [CollatzResearch.WordTrace]
  refine ⟨195047992227069644611529465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130031994818046429741019643 195047992227069644611529465)
  ·
    refine ⟨146285994170302233458647099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195047992227069644611529465 146285994170302233458647099)
    ·
      refine ⟨219428991255453350187970649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146285994170302233458647099 219428991255453350187970649)
      ·
        refine ⟨164571743441590012640977987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219428991255453350187970649 164571743441590012640977987)
        ·
          refine ⟨246857615162385018961466981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164571743441590012640977987 246857615162385018961466981)
          ·
            refine ⟨46285802842947191055275059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246857615162385018961466981 46285802842947191055275059)
            ·
              refine ⟨69428704264420786582912589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46285802842947191055275059 69428704264420786582912589)
              ·
                refine ⟨26035764099157794968592221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69428704264420786582912589 26035764099157794968592221)
                ·
                  refine ⟨9763411537184173113222083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26035764099157794968592221 9763411537184173113222083)
                  ·
                    refine ⟨14645117305776259669833125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9763411537184173113222083 14645117305776259669833125)
                    ·
                      refine ⟨2745959494833048688093711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14645117305776259669833125 2745959494833048688093711)
                      ·
                        rfl

theorem cell23_5347737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 1, 4].length) (baseStart_5347737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347737 prefixEnd_5347737 := by exact prefixLift 5347737
  have htrace : WordTrace (prefixWord ++ tailWord_5347737) baseStart_5347737 baseEnd_5347737 := by
    simpa [prefixWord, tailWord_5347737, baseEnd_5347737] using wordTrace_append hprefix tailTrace_5347737
  have hstable : (prefixWord ++ tailWord_5347737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347737).length < 2 ^ (prefixWord ++ tailWord_5347737).sum := by decide
  have hdescent : baseEnd_5347737 < baseStart_5347737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347741 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 1, 5, 2]
def baseStart_5347741 : Nat := 118140960795 + 5347741 * 2 ^ 59
def prefixEnd_5347741 : Nat := 4983230072969 + 3 ^ 40 * 5347741 * 2
def baseEnd_5347741 : Nat := 2745961548755666672443693

theorem tailTrace_5347741 : CollatzResearch.WordTrace tailWord_5347741 prefixEnd_5347741 2745961548755666672443693 := by
  unfold tailWord_5347741
  simp only [CollatzResearch.WordTrace]
  refine ⟨195048138119055153294675077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130032092079370102196450051 195048138119055153294675077)
  ·
    refine ⟨36571525897322841242751577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195048138119055153294675077 36571525897322841242751577)
    ·
      refine ⟨27428644422992130932063683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36571525897322841242751577 27428644422992130932063683)
      ·
        refine ⟨41142966634488196398095525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27428644422992130932063683 41142966634488196398095525)
        ·
          refine ⟨7714306243966536824642911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41142966634488196398095525 7714306243966536824642911)
          ·
            refine ⟨11571459365949805236964367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7714306243966536824642911 11571459365949805236964367)
            ·
              refine ⟨17357189048924707855446551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11571459365949805236964367 17357189048924707855446551)
              ·
                refine ⟨26035783573387061783169827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17357189048924707855446551 26035783573387061783169827)
                ·
                  refine ⟨39053675360080592674754741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26035783573387061783169827 39053675360080592674754741)
                  ·
                    refine ⟨3661282065007555563258257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39053675360080592674754741 3661282065007555563258257)
                    ·
                      refine ⟨2745961548755666672443693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3661282065007555563258257 2745961548755666672443693)
                      ·
                        rfl

theorem cell23_5347741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_5347741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347741 prefixEnd_5347741 := by exact prefixLift 5347741
  have htrace : WordTrace (prefixWord ++ tailWord_5347741) baseStart_5347741 baseEnd_5347741 := by
    simpa [prefixWord, tailWord_5347741, baseEnd_5347741] using wordTrace_append hprefix tailTrace_5347741
  have hstable : (prefixWord ++ tailWord_5347741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347741).length < 2 ^ (prefixWord ++ tailWord_5347741).sum := by decide
  have hdescent : baseEnd_5347741 < baseStart_5347741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347747 : List Nat := [1, 1, 1, 4, 1, 4, 2, 2, 1, 6]
def baseStart_5347747 : Nat := 118140960795 + 5347747 * 2 ^ 59
def prefixEnd_5347747 : Nat := 4983230072969 + 3 ^ 40 * 5347747 * 2
def baseEnd_5347747 : Nat := 915321543213197882989555

theorem tailTrace_5347747 : CollatzResearch.WordTrace tailWord_5347747 prefixEnd_5347747 915321543213197882989555 := by
  unfold tailWord_5347747
  simp only [CollatzResearch.WordTrace]
  refine ⟨195048356957033416319393495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130032237971355610879595663 195048356957033416319393495)
  ·
    refine ⟨292572535435550124479090243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195048356957033416319393495 292572535435550124479090243)
    ·
      refine ⟨438858803153325186718635365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292572535435550124479090243 438858803153325186718635365)
      ·
        refine ⟨82286025591248472509744131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 438858803153325186718635365 82286025591248472509744131)
        ·
          refine ⟨123429038386872708764616197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82286025591248472509744131 123429038386872708764616197)
          ·
            refine ⟨23142944697538632893365537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123429038386872708764616197 23142944697538632893365537)
            ·
              refine ⟨17357208523153974670024153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23142944697538632893365537 17357208523153974670024153)
              ·
                refine ⟨13017906392365481002518115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17357208523153974670024153 13017906392365481002518115)
                ·
                  refine ⟨19526859588548221503777173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13017906392365481002518115 19526859588548221503777173)
                  ·
                    refine ⟨915321543213197882989555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19526859588548221503777173 915321543213197882989555)
                    ·
                      rfl

theorem cell23_5347747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 1, 6].length) (baseStart_5347747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347747 prefixEnd_5347747 := by exact prefixLift 5347747
  have htrace : WordTrace (prefixWord ++ tailWord_5347747) baseStart_5347747 baseEnd_5347747 := by
    simpa [prefixWord, tailWord_5347747, baseEnd_5347747] using wordTrace_append hprefix tailTrace_5347747
  have hstable : (prefixWord ++ tailWord_5347747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347747).length < 2 ^ (prefixWord ++ tailWord_5347747).sum := by decide
  have hdescent : baseEnd_5347747 < baseStart_5347747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347751 : List Nat := [1, 1, 6, 1, 1, 2, 4, 1, 1, 5]
def baseStart_5347751 : Nat := 118140960795 + 5347751 * 2 ^ 59
def prefixEnd_5347751 : Nat := 4983230072969 + 3 ^ 40 * 5347751 * 2
def baseEnd_5347751 : Nat := 915322227854070544439549

theorem tailTrace_5347751 : CollatzResearch.WordTrace tailWord_5347751 prefixEnd_5347751 915322227854070544439549 := by
  unfold tailWord_5347751
  simp only [CollatzResearch.WordTrace]
  refine ⟨195048502849018925002539107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130032335232679283335026071 195048502849018925002539107)
  ·
    refine ⟨292572754273528387503808661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195048502849018925002539107 292572754273528387503808661)
    ·
      refine ⟨13714347856571643164241031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 292572754273528387503808661 13714347856571643164241031)
      ·
        refine ⟨20571521784857464746361547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13714347856571643164241031 20571521784857464746361547)
        ·
          refine ⟨30857282677286197119542321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20571521784857464746361547 30857282677286197119542321)
          ·
            refine ⟨23142962007964647839656741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30857282677286197119542321 23142962007964647839656741)
            ·
              refine ⟨4339305376493371469935639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23142962007964647839656741 4339305376493371469935639)
              ·
                refine ⟨6508958064740057204903459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4339305376493371469935639 6508958064740057204903459)
                ·
                  refine ⟨9763437097110085807355189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6508958064740057204903459 9763437097110085807355189)
                  ·
                    refine ⟨915322227854070544439549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9763437097110085807355189 915322227854070544439549)
                    ·
                      rfl

theorem cell23_5347751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_5347751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347751 prefixEnd_5347751 := by exact prefixLift 5347751
  have htrace : WordTrace (prefixWord ++ tailWord_5347751) baseStart_5347751 baseEnd_5347751 := by
    simpa [prefixWord, tailWord_5347751, baseEnd_5347751] using wordTrace_append hprefix tailTrace_5347751
  have hstable : (prefixWord ++ tailWord_5347751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347751).length < 2 ^ (prefixWord ++ tailWord_5347751).sum := by decide
  have hdescent : baseEnd_5347751 < baseStart_5347751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347774 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_5347774 : Nat := 118140960795 + 5347774 * 2 ^ 59
def prefixEnd_5347774 : Nat := 4983230072969 + 3 ^ 40 * 5347774 * 2
def baseEnd_5347774 : Nat := 2745978493617265043331041

theorem tailTrace_5347774 : CollatzResearch.WordTrace tailWord_5347774 prefixEnd_5347774 2745978493617265043331041 := by
  unfold tailWord_5347774
  simp only [CollatzResearch.WordTrace]
  refine ⟨24381167715991949991328297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130032894485290399953750917 24381167715991949991328297)
  ·
    refine ⟨18285875786993962493496223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24381167715991949991328297 18285875786993962493496223)
    ·
      refine ⟨27428813680490943740244335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18285875786993962493496223 27428813680490943740244335)
      ·
        refine ⟨41143220520736415610366503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27428813680490943740244335 41143220520736415610366503)
        ·
          refine ⟨61714830781104623415549755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41143220520736415610366503 61714830781104623415549755)
          ·
            refine ⟨92572246171656935123324633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61714830781104623415549755 92572246171656935123324633)
            ·
              refine ⟨69429184628742701342493475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92572246171656935123324633 69429184628742701342493475)
              ·
                refine ⟨104143776943114052013740213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69429184628742701342493475 104143776943114052013740213)
                ·
                  refine ⟨9763479088416942376288145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 104143776943114052013740213 9763479088416942376288145)
                  ·
                    refine ⟨7322609316312706782216109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9763479088416942376288145 7322609316312706782216109)
                    ·
                      refine ⟨2745978493617265043331041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7322609316312706782216109 2745978493617265043331041)
                      ·
                        rfl

theorem cell23_5347774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_5347774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347774 prefixEnd_5347774 := by exact prefixLift 5347774
  have htrace : WordTrace (prefixWord ++ tailWord_5347774) baseStart_5347774 baseEnd_5347774 := by
    simpa [prefixWord, tailWord_5347774, baseEnd_5347774] using wordTrace_append hprefix tailTrace_5347774
  have hstable : (prefixWord ++ tailWord_5347774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347774).length < 2 ^ (prefixWord ++ tailWord_5347774).sum := by decide
  have hdescent : baseEnd_5347774 < baseStart_5347774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347784 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_5347784 : Nat := 118140960795 + 5347784 * 2 ^ 59
def prefixEnd_5347784 : Nat := 4983230072969 + 3 ^ 40 * 5347784 * 2
def baseEnd_5347784 : Nat := 2745983628423810004205995

theorem tailTrace_5347784 : CollatzResearch.WordTrace tailWord_5347784 prefixEnd_5347784 2745983628423810004205995 := by
  unfold tailWord_5347784
  simp only [CollatzResearch.WordTrace]
  refine ⟨97524853228949685819245203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130033137638599581092326937 97524853228949685819245203)
  ·
    refine ⟨146287279843424528728867805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97524853228949685819245203 146287279843424528728867805)
    ·
      refine ⟨54857729941284198273325427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146287279843424528728867805 54857729941284198273325427)
      ·
        refine ⟨82286594911926297409988141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54857729941284198273325427 82286594911926297409988141)
        ·
          refine ⟨30857473091972361528745553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82286594911926297409988141 30857473091972361528745553)
          ·
            refine ⟨23143104818979271146559165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30857473091972361528745553 23143104818979271146559165)
            ·
              refine ⟨8678664307117226679959687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23143104818979271146559165 8678664307117226679959687)
              ·
                refine ⟨13017996460675840019939531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8678664307117226679959687 13017996460675840019939531)
                ·
                  refine ⟨19526994691013760029909297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13017996460675840019939531 19526994691013760029909297)
                  ·
                    refine ⟨14645246018260320022431973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19526994691013760029909297 14645246018260320022431973)
                    ·
                      refine ⟨2745983628423810004205995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14645246018260320022431973 2745983628423810004205995)
                      ·
                        rfl

theorem cell23_5347784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_5347784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347784 prefixEnd_5347784 := by exact prefixLift 5347784
  have htrace : WordTrace (prefixWord ++ tailWord_5347784) baseStart_5347784 baseEnd_5347784 := by
    simpa [prefixWord, tailWord_5347784, baseEnd_5347784] using wordTrace_append hprefix tailTrace_5347784
  have hstable : (prefixWord ++ tailWord_5347784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347784).length < 2 ^ (prefixWord ++ tailWord_5347784).sum := by decide
  have hdescent : baseEnd_5347784 < baseStart_5347784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347822 : List Nat := [4, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2]
def baseStart_5347822 : Nat := 118140960795 + 5347822 * 2 ^ 59
def prefixEnd_5347822 : Nat := 4983230072969 + 3 ^ 40 * 5347822 * 2
def baseEnd_5347822 : Nat := 2746003140688680855530821

theorem tailTrace_5347822 : CollatzResearch.WordTrace tailWord_5347822 prefixEnd_5347822 2746003140688680855530821 := by
  unfold tailWord_5347822
  simp only [CollatzResearch.WordTrace]
  refine ⟨24381386553970213016046715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130034061621174469418915813 24381386553970213016046715)
  ·
    refine ⟨36572079830955319524070073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24381386553970213016046715 36572079830955319524070073)
    ·
      refine ⟨27429059873216489643052555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36572079830955319524070073 27429059873216489643052555)
      ·
        refine ⟨41143589809824734464578833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27429059873216489643052555 41143589809824734464578833)
        ·
          refine ⟨30857692357368550848434125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41143589809824734464578833 30857692357368550848434125)
          ·
            refine ⟨11571634634013206568162797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30857692357368550848434125 11571634634013206568162797)
            ·
              refine ⟨4339362987754952463061049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11571634634013206568162797 4339362987754952463061049)
              ·
                refine ⟨3254522240816214347295787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4339362987754952463061049 3254522240816214347295787)
                ·
                  refine ⟨4881783361224321520943681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254522240816214347295787 4881783361224321520943681)
                  ·
                    refine ⟨3661337520918241140707761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4881783361224321520943681 3661337520918241140707761)
                    ·
                      refine ⟨2746003140688680855530821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3661337520918241140707761 2746003140688680855530821)
                      ·
                        rfl

theorem cell23_5347822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_5347822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347822 prefixEnd_5347822 := by exact prefixLift 5347822
  have htrace : WordTrace (prefixWord ++ tailWord_5347822) baseStart_5347822 baseEnd_5347822 := by
    simpa [prefixWord, tailWord_5347822, baseEnd_5347822] using wordTrace_append hprefix tailTrace_5347822
  have hstable : (prefixWord ++ tailWord_5347822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347822).length < 2 ^ (prefixWord ++ tailWord_5347822).sum := by decide
  have hdescent : baseEnd_5347822 < baseStart_5347822 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347827 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 4]
def baseStart_5347827 : Nat := 118140960795 + 5347827 * 2 ^ 59
def prefixEnd_5347827 : Nat := 4983230072969 + 3 ^ 40 * 5347827 * 2
def baseEnd_5347827 : Nat := 2746005708091953335968297

theorem tailTrace_5347827 : CollatzResearch.WordTrace tailWord_5347827 prefixEnd_5347827 2746005708091953335968297 := by
  unfold tailWord_5347827
  simp only [CollatzResearch.WordTrace]
  refine ⟨195051274796743589982305735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130034183197829059988203823 195051274796743589982305735)
  ·
    refine ⟨292576912195115384973458603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195051274796743589982305735 292576912195115384973458603)
    ·
      refine ⟨438865368292673077460187905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292576912195115384973458603 438865368292673077460187905)
      ·
        refine ⟨329149026219504808095140929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438865368292673077460187905 329149026219504808095140929)
        ·
          refine ⟨246861769664628606071355697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329149026219504808095140929 246861769664628606071355697)
          ·
            refine ⟨185146327248471454553516773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246861769664628606071355697 185146327248471454553516773)
            ·
              refine ⟨34714936359088397728784395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185146327248471454553516773 34714936359088397728784395)
              ·
                refine ⟨52072404538632596593176593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34714936359088397728784395 52072404538632596593176593)
                ·
                  refine ⟨39054303403974447444882445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52072404538632596593176593 39054303403974447444882445)
                  ·
                    refine ⟨14645363776490417791830917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39054303403974447444882445 14645363776490417791830917)
                    ·
                      refine ⟨2746005708091953335968297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14645363776490417791830917 2746005708091953335968297)
                      ·
                        rfl

theorem cell23_5347827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 4].length) (baseStart_5347827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347827 prefixEnd_5347827 := by exact prefixLift 5347827
  have htrace : WordTrace (prefixWord ++ tailWord_5347827) baseStart_5347827 baseEnd_5347827 := by
    simpa [prefixWord, tailWord_5347827, baseEnd_5347827] using wordTrace_append hprefix tailTrace_5347827
  have hstable : (prefixWord ++ tailWord_5347827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347827).length < 2 ^ (prefixWord ++ tailWord_5347827).sum := by decide
  have hdescent : baseEnd_5347827 < baseStart_5347827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347837 : List Nat := [1, 4, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_5347837 : Nat := 118140960795 + 5347837 * 2 ^ 59
def prefixEnd_5347837 : Nat := 4983230072969 + 3 ^ 40 * 5347837 * 2
def baseEnd_5347837 : Nat := 915336947632832765614417

theorem tailTrace_5347837 : CollatzResearch.WordTrace tailWord_5347837 prefixEnd_5347837 915336947632832765614417 := by
  unfold tailWord_5347837
  simp only [CollatzResearch.WordTrace]
  refine ⟨195051639526707361690169765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130034426351138241126779843 195051639526707361690169765)
  ·
    refine ⟨36572182411257630316906831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195051639526707361690169765 36572182411257630316906831)
    ·
      refine ⟨54858273616886445475360247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36572182411257630316906831 54858273616886445475360247)
      ·
        refine ⟨82287410425329668213040371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54858273616886445475360247 82287410425329668213040371)
        ·
          refine ⟨123431115637994502319560557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82287410425329668213040371 123431115637994502319560557)
          ·
            refine ⟨46286668364247938369835209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123431115637994502319560557 46286668364247938369835209)
            ·
              refine ⟨34715001273185953777376407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46286668364247938369835209 34715001273185953777376407)
              ·
                refine ⟨52072501909778930666064611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34715001273185953777376407 52072501909778930666064611)
                ·
                  refine ⟨78108752864668395999096917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52072501909778930666064611 78108752864668395999096917)
                  ·
                    refine ⟨915336947632832765614417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78108752864668395999096917 915336947632832765614417)
                    ·
                      rfl

theorem cell23_5347837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_5347837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347837 prefixEnd_5347837 := by exact prefixLift 5347837
  have htrace : WordTrace (prefixWord ++ tailWord_5347837) baseStart_5347837 baseEnd_5347837 := by
    simpa [prefixWord, tailWord_5347837, baseEnd_5347837] using wordTrace_append hprefix tailTrace_5347837
  have hstable : (prefixWord ++ tailWord_5347837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347837).length < 2 ^ (prefixWord ++ tailWord_5347837).sum := by decide
  have hdescent : baseEnd_5347837 < baseStart_5347837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347842 : List Nat := [3, 4, 1, 2, 3, 1, 1, 2, 1, 2, 3]
def baseStart_5347842 : Nat := 118140960795 + 5347842 * 2 ^ 59
def prefixEnd_5347842 : Nat := 4983230072969 + 3 ^ 40 * 5347842 * 2
def baseEnd_5347842 : Nat := 2746013410301770777280729

theorem tailTrace_5347842 : CollatzResearch.WordTrace tailWord_5347842 prefixEnd_5347842 2746013410301770777280729 := by
  unfold tailWord_5347842
  simp only [CollatzResearch.WordTrace]
  refine ⟨48762955472922311886025445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130034547927792831696067853 48762955472922311886025445)
  ·
    refine ⟨9143054151172933478629771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48762955472922311886025445 9143054151172933478629771)
    ·
      refine ⟨13714581226759400217944657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9143054151172933478629771 13714581226759400217944657)
      ·
        refine ⟨10285935920069550163458493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13714581226759400217944657 10285935920069550163458493)
        ·
          refine ⟨3857225970026081311296935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10285935920069550163458493 3857225970026081311296935)
          ·
            refine ⟨5785838955039121966945403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3857225970026081311296935 5785838955039121966945403)
            ·
              refine ⟨8678758432558682950418105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5785838955039121966945403 8678758432558682950418105)
              ·
                refine ⟨6509068824419012212813579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8678758432558682950418105 6509068824419012212813579)
                ·
                  refine ⟨9763603236628518319220369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6509068824419012212813579 9763603236628518319220369)
                  ·
                    refine ⟨7322702427471388739415277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9763603236628518319220369 7322702427471388739415277)
                    ·
                      refine ⟨2746013410301770777280729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7322702427471388739415277 2746013410301770777280729)
                      ·
                        rfl

theorem cell23_5347842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_5347842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347842 prefixEnd_5347842 := by exact prefixLift 5347842
  have htrace : WordTrace (prefixWord ++ tailWord_5347842) baseStart_5347842 baseEnd_5347842 := by
    simpa [prefixWord, tailWord_5347842, baseEnd_5347842] using wordTrace_append hprefix tailTrace_5347842
  have hstable : (prefixWord ++ tailWord_5347842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347842).length < 2 ^ (prefixWord ++ tailWord_5347842).sum := by decide
  have hdescent : baseEnd_5347842 < baseStart_5347842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347857 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 4]
def baseStart_5347857 : Nat := 118140960795 + 5347857 * 2 ^ 59
def prefixEnd_5347857 : Nat := 4983230072969 + 3 ^ 40 * 5347857 * 2
def baseEnd_5347857 : Nat := 2746021112511588218593159

theorem tailTrace_5347857 : CollatzResearch.WordTrace tailWord_5347857 prefixEnd_5347857 2746021112511588218593159 := by
  unfold tailWord_5347857
  simp only [CollatzResearch.WordTrace]
  refine ⟨195052368986634905105897825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130034912657756603403931883 195052368986634905105897825)
  ·
    refine ⟨146289276739976178829423369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195052368986634905105897825 146289276739976178829423369)
    ·
      refine ⟨109716957554982134122067527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146289276739976178829423369 109716957554982134122067527)
      ·
        refine ⟨164575436332473201183101291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109716957554982134122067527 164575436332473201183101291)
        ·
          refine ⟨246863154498709801774651937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164575436332473201183101291 246863154498709801774651937)
          ·
            refine ⟨185147365874032351330988953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246863154498709801774651937 185147365874032351330988953)
            ·
              refine ⟨138860524405524263498241715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185147365874032351330988953 138860524405524263498241715)
              ·
                refine ⟨208290786608286395247362573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138860524405524263498241715 208290786608286395247362573)
                ·
                  refine ⟨78109044978107398217760965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208290786608286395247362573 78109044978107398217760965)
                  ·
                    refine ⟨14645445933395137165830181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 78109044978107398217760965 14645445933395137165830181)
                    ·
                      refine ⟨2746021112511588218593159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14645445933395137165830181 2746021112511588218593159)
                      ·
                        rfl

theorem cell23_5347857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 4].length) (baseStart_5347857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347857 prefixEnd_5347857 := by exact prefixLift 5347857
  have htrace : WordTrace (prefixWord ++ tailWord_5347857) baseStart_5347857 baseEnd_5347857 := by
    simpa [prefixWord, tailWord_5347857, baseEnd_5347857] using wordTrace_append hprefix tailTrace_5347857
  have hstable : (prefixWord ++ tailWord_5347857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347857).length < 2 ^ (prefixWord ++ tailWord_5347857).sum := by decide
  have hdescent : baseEnd_5347857 < baseStart_5347857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347861 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 1, 4, 2]
def baseStart_5347861 : Nat := 118140960795 + 5347861 * 2 ^ 59
def prefixEnd_5347861 : Nat := 4983230072969 + 3 ^ 40 * 5347861 * 2
def baseEnd_5347861 : Nat := 2746023166434206202943141

theorem tailTrace_5347861 : CollatzResearch.WordTrace tailWord_5347861 prefixEnd_5347861 2746023166434206202943141 := by
  unfold tailWord_5347861
  simp only [CollatzResearch.WordTrace]
  refine ⟨195052514878620413789043437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130035009919080275859362291 195052514878620413789043437)
  ·
    refine ⟨73144693079482655170891289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195052514878620413789043437 73144693079482655170891289)
    ·
      refine ⟨54858519809611991378168467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73144693079482655170891289 54858519809611991378168467)
      ·
        refine ⟨82287779714417987067252701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54858519809611991378168467 82287779714417987067252701)
        ·
          refine ⟨30857917392906745150219763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82287779714417987067252701 30857917392906745150219763)
          ·
            refine ⟨46286876089360117725329645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30857917392906745150219763 46286876089360117725329645)
            ·
              refine ⟨17357578533510044146998617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46286876089360117725329645 17357578533510044146998617)
              ·
                refine ⟨13018183900132533110248963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17357578533510044146998617 13018183900132533110248963)
                ·
                  refine ⟨19527275850198799665373445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13018183900132533110248963 19527275850198799665373445)
                  ·
                    refine ⟨3661364221912274937257521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19527275850198799665373445 3661364221912274937257521)
                    ·
                      refine ⟨2746023166434206202943141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3661364221912274937257521 2746023166434206202943141)
                      ·
                        rfl

theorem cell23_5347861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_5347861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347861 prefixEnd_5347861 := by exact prefixLift 5347861
  have htrace : WordTrace (prefixWord ++ tailWord_5347861) baseStart_5347861 baseEnd_5347861 := by
    simpa [prefixWord, tailWord_5347861, baseEnd_5347861] using wordTrace_append hprefix tailTrace_5347861
  have hstable : (prefixWord ++ tailWord_5347861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347861).length < 2 ^ (prefixWord ++ tailWord_5347861).sum := by decide
  have hdescent : baseEnd_5347861 < baseStart_5347861 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347864 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_5347864 : Nat := 118140960795 + 5347864 * 2 ^ 59
def prefixEnd_5347864 : Nat := 4983230072969 + 3 ^ 40 * 5347864 * 2
def baseEnd_5347864 : Nat := 2746024706876169691205627

theorem tailTrace_5347864 : CollatzResearch.WordTrace tailWord_5347864 prefixEnd_5347864 2746024706876169691205627 := by
  unfold tailWord_5347864
  simp only [CollatzResearch.WordTrace]
  refine ⟨97526312148804772650701323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130035082865073030200935097 97526312148804772650701323)
  ·
    refine ⟨146289468223207158976051985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97526312148804772650701323 146289468223207158976051985)
    ·
      refine ⟨109717101167405369232038989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146289468223207158976051985 109717101167405369232038989)
      ·
        refine ⟨41143912937777013462014621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109717101167405369232038989 41143912937777013462014621)
        ·
          refine ⟨15428967351666380048255483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41143912937777013462014621 15428967351666380048255483)
          ·
            refine ⟨23143451027499570072383225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15428967351666380048255483 23143451027499570072383225)
            ·
              refine ⟨17357588270624677554287419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23143451027499570072383225 17357588270624677554287419)
              ·
                refine ⟨26036382405937016331431129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17357588270624677554287419 26036382405937016331431129)
                ·
                  refine ⟨19527286804452762248573347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26036382405937016331431129 19527286804452762248573347)
                  ·
                    refine ⟨29290930206679143372860021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19527286804452762248573347 29290930206679143372860021)
                    ·
                      refine ⟨2746024706876169691205627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29290930206679143372860021 2746024706876169691205627)
                      ·
                        rfl

theorem cell23_5347864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_5347864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347864 prefixEnd_5347864 := by exact prefixLift 5347864
  have htrace : WordTrace (prefixWord ++ tailWord_5347864) baseStart_5347864 baseEnd_5347864 := by
    simpa [prefixWord, tailWord_5347864, baseEnd_5347864] using wordTrace_append hprefix tailTrace_5347864
  have hstable : (prefixWord ++ tailWord_5347864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347864).length < 2 ^ (prefixWord ++ tailWord_5347864).sum := by decide
  have hdescent : baseEnd_5347864 < baseStart_5347864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347874 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 2, 2, 4]
def baseStart_5347874 : Nat := 118140960795 + 5347874 * 2 ^ 59
def prefixEnd_5347874 : Nat := 4983230072969 + 3 ^ 40 * 5347874 * 2
def baseEnd_5347874 : Nat := 2746029841682714652080581

theorem tailTrace_5347874 : CollatzResearch.WordTrace tailWord_5347874 prefixEnd_5347874 2746029841682714652080581 := by
  unfold tailWord_5347874
  simp only [CollatzResearch.WordTrace]
  refine ⟨48763247256893329252316669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130035326018382211339511117 48763247256893329252316669)
  ·
    refine ⟨18286217721334998469618751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48763247256893329252316669 18286217721334998469618751)
    ·
      refine ⟨27429326582002497704428127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18286217721334998469618751 27429326582002497704428127)
      ·
        refine ⟨41143989873003746556642191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27429326582002497704428127 41143989873003746556642191)
        ·
          refine ⟨61715984809505619834963287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41143989873003746556642191 61715984809505619834963287)
          ·
            refine ⟨92573977214258429752444931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61715984809505619834963287 92573977214258429752444931)
            ·
              refine ⟨138860965821387644628667397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92573977214258429752444931 138860965821387644628667397)
              ·
                refine ⟨26036431091510183367875137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138860965821387644628667397 26036431091510183367875137)
                ·
                  refine ⟨19527323318632637525906353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26036431091510183367875137 19527323318632637525906353)
                  ·
                    refine ⟨14645492488974478144429765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19527323318632637525906353 14645492488974478144429765)
                    ·
                      refine ⟨2746029841682714652080581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14645492488974478144429765 2746029841682714652080581)
                      ·
                        rfl

theorem cell23_5347874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_5347874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347874 prefixEnd_5347874 := by exact prefixLift 5347874
  have htrace : WordTrace (prefixWord ++ tailWord_5347874) baseStart_5347874 baseEnd_5347874 := by
    simpa [prefixWord, tailWord_5347874, baseEnd_5347874] using wordTrace_append hprefix tailTrace_5347874
  have hstable : (prefixWord ++ tailWord_5347874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347874).length < 2 ^ (prefixWord ++ tailWord_5347874).sum := by decide
  have hdescent : baseEnd_5347874 < baseStart_5347874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347877 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 7]
def baseStart_5347877 : Nat := 118140960795 + 5347877 * 2 ^ 59
def prefixEnd_5347877 : Nat := 4983230072969 + 3 ^ 40 * 5347877 * 2
def baseEnd_5347877 : Nat := 2746031382124678140343067

theorem tailTrace_5347877 : CollatzResearch.WordTrace tailWord_5347877 prefixEnd_5347877 2746031382124678140343067 := by
  unfold tailWord_5347877
  simp only [CollatzResearch.WordTrace]
  refine ⟨195053098446562448521625885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130035398964374965681083923 195053098446562448521625885)
  ·
    refine ⟨73144911917460918195609707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195053098446562448521625885 73144911917460918195609707)
    ·
      refine ⟨109717367876191377293414561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73144911917460918195609707 109717367876191377293414561)
      ·
        refine ⟨82288025907143532970060921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109717367876191377293414561 82288025907143532970060921)
        ·
          refine ⟨61716019430357649727545691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82288025907143532970060921 61716019430357649727545691)
          ·
            refine ⟨92574029145536474591318537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61716019430357649727545691 92574029145536474591318537)
            ·
              refine ⟨69430521859152355943488903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92574029145536474591318537 69430521859152355943488903)
              ·
                refine ⟨104145782788728533915233355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69430521859152355943488903 104145782788728533915233355)
                ·
                  refine ⟨156218674183092800872850033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104145782788728533915233355 156218674183092800872850033)
                  ·
                    refine ⟨117164005637319600654637525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 156218674183092800872850033 117164005637319600654637525)
                    ·
                      refine ⟨2746031382124678140343067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117164005637319600654637525 2746031382124678140343067)
                      ·
                        rfl

theorem cell23_5347877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_5347877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347877 prefixEnd_5347877 := by exact prefixLift 5347877
  have htrace : WordTrace (prefixWord ++ tailWord_5347877) baseStart_5347877 baseEnd_5347877 := by
    simpa [prefixWord, tailWord_5347877, baseEnd_5347877] using wordTrace_append hprefix tailTrace_5347877
  have hstable : (prefixWord ++ tailWord_5347877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347877).length < 2 ^ (prefixWord ++ tailWord_5347877).sum := by decide
  have hdescent : baseEnd_5347877 < baseStart_5347877 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347907 : List Nat := [1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 7]
def baseStart_5347907 : Nat := 118140960795 + 5347907 * 2 ^ 59
def prefixEnd_5347907 : Nat := 4983230072969 + 3 ^ 40 * 5347907 * 2
def baseEnd_5347907 : Nat := 2746046786544313022967929

theorem tailTrace_5347907 : CollatzResearch.WordTrace tailWord_5347907 prefixEnd_5347907 2746046786544313022967929 := by
  unfold tailWord_5347907
  simp only [CollatzResearch.WordTrace]
  refine ⟨195054192636453763645217975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130036128424302509096811983 195054192636453763645217975)
  ·
    refine ⟨292581288954680645467826963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195054192636453763645217975 292581288954680645467826963)
    ·
      refine ⟨438871933432020968201740445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292581288954680645467826963 438871933432020968201740445)
      ·
        refine ⟨164576975037007863075652667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438871933432020968201740445 164576975037007863075652667)
        ·
          refine ⟨246865462555511794613479001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164576975037007863075652667 246865462555511794613479001)
          ·
            refine ⟨185149096916633845960109251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246865462555511794613479001 185149096916633845960109251)
            ·
              refine ⟨277723645374950768940163877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185149096916633845960109251 277723645374950768940163877)
              ·
                refine ⟨52073183507803269176280727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 277723645374950768940163877 52073183507803269176280727)
                ·
                  refine ⟨78109775261704903764421091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52073183507803269176280727 78109775261704903764421091)
                  ·
                    refine ⟨117164662892557355646631637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 78109775261704903764421091 117164662892557355646631637)
                    ·
                      refine ⟨2746046786544313022967929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117164662892557355646631637 2746046786544313022967929)
                      ·
                        rfl

theorem cell23_5347907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 7].length) (baseStart_5347907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347907 prefixEnd_5347907 := by exact prefixLift 5347907
  have htrace : WordTrace (prefixWord ++ tailWord_5347907) baseStart_5347907 baseEnd_5347907 := by
    simpa [prefixWord, tailWord_5347907, baseEnd_5347907] using wordTrace_append hprefix tailTrace_5347907
  have hstable : (prefixWord ++ tailWord_5347907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347907).length < 2 ^ (prefixWord ++ tailWord_5347907).sum := by decide
  have hdescent : baseEnd_5347907 < baseStart_5347907 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347914 : List Nat := [3, 1, 2, 1, 1, 5, 1, 1, 1, 7]
def baseStart_5347914 : Nat := 118140960795 + 5347914 * 2 ^ 59
def prefixEnd_5347914 : Nat := 4983230072969 + 3 ^ 40 * 5347914 * 2
def baseEnd_5347914 : Nat := 915350126969631498526799

theorem tailTrace_5347914 : CollatzResearch.WordTrace tailWord_5347914 prefixEnd_5347914 915350126969631498526799 := by
  unfold tailWord_5347914
  simp only [CollatzResearch.WordTrace]
  refine ⟨48763611986857100960180699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130036298631618935893815197 48763611986857100960180699)
  ·
    refine ⟨73145417980285651440271049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48763611986857100960180699 73145417980285651440271049)
    ·
      refine ⟨54859063485214238580203287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73145417980285651440271049 54859063485214238580203287)
      ·
        refine ⟨82288595227821357870304931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54859063485214238580203287 82288595227821357870304931)
        ·
          refine ⟨123432892841732036805457397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82288595227821357870304931 123432892841732036805457397)
          ·
            refine ⟨11571833703912378450511631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123432892841732036805457397 11571833703912378450511631)
            ·
              refine ⟨17357750555868567675767447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11571833703912378450511631 17357750555868567675767447)
              ·
                refine ⟨26036625833802851513651171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17357750555868567675767447 26036625833802851513651171)
                ·
                  refine ⟨39054938750704277270476757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26036625833802851513651171 39054938750704277270476757)
                  ·
                    refine ⟨915350126969631498526799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39054938750704277270476757 915350126969631498526799)
                    ·
                      rfl

theorem cell23_5347914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 1, 1, 1, 7].length) (baseStart_5347914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347914 prefixEnd_5347914 := by exact prefixLift 5347914
  have htrace : WordTrace (prefixWord ++ tailWord_5347914) baseStart_5347914 baseEnd_5347914 := by
    simpa [prefixWord, tailWord_5347914, baseEnd_5347914] using wordTrace_append hprefix tailTrace_5347914
  have hstable : (prefixWord ++ tailWord_5347914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347914).length < 2 ^ (prefixWord ++ tailWord_5347914).sum := by decide
  have hdescent : baseEnd_5347914 < baseStart_5347914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347951 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 2, 4, 2]
def baseStart_5347951 : Nat := 118140960795 + 5347951 * 2 ^ 59
def prefixEnd_5347951 : Nat := 4983230072969 + 3 ^ 40 * 5347951 * 2
def baseEnd_5347951 : Nat := 2746069379693110850817727

theorem tailTrace_5347951 : CollatzResearch.WordTrace tailWord_5347951 prefixEnd_5347951 2746069379693110850817727 := by
  unfold tailWord_5347951
  simp only [CollatzResearch.WordTrace]
  refine ⟨195055797448294359159819707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130037198298862906106546471 195055797448294359159819707)
  ·
    refine ⟨292583696172441538739729561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195055797448294359159819707 292583696172441538739729561)
    ·
      refine ⟨219437772129331154054797171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292583696172441538739729561 219437772129331154054797171)
      ·
        refine ⟨329156658193996731082195757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219437772129331154054797171 329156658193996731082195757)
        ·
          refine ⟨123433746822748774155823409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 329156658193996731082195757 123433746822748774155823409)
          ·
            refine ⟨92575310117061580616867557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 123433746822748774155823409 92575310117061580616867557)
            ·
              refine ⟨17357870646949046365662667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 92575310117061580616867557 17357870646949046365662667)
              ·
                refine ⟨26036805970423569548494001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17357870646949046365662667 26036805970423569548494001)
                ·
                  refine ⟨19527604477817677161370501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26036805970423569548494001 19527604477817677161370501)
                  ·
                    refine ⟨3661425839590814467756969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19527604477817677161370501 3661425839590814467756969)
                    ·
                      refine ⟨2746069379693110850817727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3661425839590814467756969 2746069379693110850817727)
                      ·
                        rfl

theorem cell23_5347951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 4, 2].length) (baseStart_5347951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347951 prefixEnd_5347951 := by exact prefixLift 5347951
  have htrace : WordTrace (prefixWord ++ tailWord_5347951) baseStart_5347951 baseEnd_5347951 := by
    simpa [prefixWord, tailWord_5347951, baseEnd_5347951] using wordTrace_append hprefix tailTrace_5347951
  have hstable : (prefixWord ++ tailWord_5347951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347951).length < 2 ^ (prefixWord ++ tailWord_5347951).sum := by decide
  have hdescent : baseEnd_5347951 < baseStart_5347951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347961 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 3, 4]
def baseStart_5347961 : Nat := 118140960795 + 5347961 * 2 ^ 59
def prefixEnd_5347961 : Nat := 4983230072969 + 3 ^ 40 * 5347961 * 2
def baseEnd_5347961 : Nat := 915358171499885270564227

theorem tailTrace_5347961 : CollatzResearch.WordTrace tailWord_5347961 prefixEnd_5347961 915358171499885270564227 := by
  unfold tailWord_5347961
  simp only [CollatzResearch.WordTrace]
  refine ⟨195056162178258130867683737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130037441452172087245122491 195056162178258130867683737)
  ·
    refine ⟨146292121633693598150762803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195056162178258130867683737 146292121633693598150762803)
    ·
      refine ⟨219438182450540397226144205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146292121633693598150762803 219438182450540397226144205)
      ·
        refine ⟨82289318418952648959804077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 219438182450540397226144205 82289318418952648959804077)
        ·
          refine ⟨30858494407107243359926529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82289318418952648959804077 30858494407107243359926529)
          ·
            refine ⟨23143870805330432519944897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30858494407107243359926529 23143870805330432519944897)
            ·
              refine ⟨17357903103997824389958673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23143870805330432519944897 17357903103997824389958673)
              ·
                refine ⟨13018427327998368292469005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17357903103997824389958673 13018427327998368292469005)
                ·
                  refine ⟨4881910247999388109675877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13018427327998368292469005 4881910247999388109675877)
                  ·
                    refine ⟨915358171499885270564227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4881910247999388109675877 915358171499885270564227)
                    ·
                      rfl

theorem cell23_5347961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 3, 4].length) (baseStart_5347961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347961 prefixEnd_5347961 := by exact prefixLift 5347961
  have htrace : WordTrace (prefixWord ++ tailWord_5347961) baseStart_5347961 baseEnd_5347961 := by
    simpa [prefixWord, tailWord_5347961, baseEnd_5347961] using wordTrace_append hprefix tailTrace_5347961
  have hstable : (prefixWord ++ tailWord_5347961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347961).length < 2 ^ (prefixWord ++ tailWord_5347961).sum := by decide
  have hdescent : baseEnd_5347961 < baseStart_5347961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5347988 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_5347988 : Nat := 118140960795 + 5347988 * 2 ^ 59
def prefixEnd_5347988 : Nat := 4983230072969 + 3 ^ 40 * 5347988 * 2
def baseEnd_5347988 : Nat := 2746088378477327206055057

theorem tailTrace_5347988 : CollatzResearch.WordTrace tailWord_5347988 prefixEnd_5347988 2746088378477327206055057 := by
  unfold tailWord_5347988
  simp only [CollatzResearch.WordTrace]
  refine ⟨97528573474580157239458309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130038097966106876319277745 97528573474580157239458309)
  ·
    refine ⟨18286607526483779482398433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97528573474580157239458309 18286607526483779482398433)
    ·
      refine ⟨13714955644862834611798825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18286607526483779482398433 13714955644862834611798825)
      ·
        refine ⟨10286216733647125958849119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13714955644862834611798825 10286216733647125958849119)
        ·
          refine ⟨15429325100470688938273679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10286216733647125958849119 15429325100470688938273679)
          ·
            refine ⟨23143987650706033407410519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15429325100470688938273679 23143987650706033407410519)
            ·
              refine ⟨34715981476059050111115779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23143987650706033407410519 34715981476059050111115779)
              ·
                refine ⟨52073972214088575166673669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34715981476059050111115779 52073972214088575166673669)
                ·
                  refine ⟨9763869790141607843751313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52073972214088575166673669 9763869790141607843751313)
                  ·
                    refine ⟨7322902342606205882813485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9763869790141607843751313 7322902342606205882813485)
                    ·
                      refine ⟨2746088378477327206055057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7322902342606205882813485 2746088378477327206055057)
                      ·
                        rfl

theorem cell23_5347988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_5347988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5347988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5347988 prefixEnd_5347988 := by exact prefixLift 5347988
  have htrace : WordTrace (prefixWord ++ tailWord_5347988) baseStart_5347988 baseEnd_5347988 := by
    simpa [prefixWord, tailWord_5347988, baseEnd_5347988] using wordTrace_append hprefix tailTrace_5347988
  have hstable : (prefixWord ++ tailWord_5347988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5347988).length < 2 ^ (prefixWord ++ tailWord_5347988).sum := by decide
  have hdescent : baseEnd_5347988 < baseStart_5347988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5347988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348022 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3]
def baseStart_5348022 : Nat := 118140960795 + 5348022 * 2 ^ 59
def prefixEnd_5348022 : Nat := 4983230072969 + 3 ^ 40 * 5348022 * 2
def baseEnd_5348022 : Nat := 2746105836819580073029901

theorem tailTrace_5348022 : CollatzResearch.WordTrace tailWord_5348022 prefixEnd_5348022 2746105836819580073029901 := by
  unfold tailWord_5348022
  simp only [CollatzResearch.WordTrace]
  refine ⟨12191149189439821142853395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130038924687358092190436213 12191149189439821142853395)
  ·
    refine ⟨18286723784159731714280093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12191149189439821142853395 18286723784159731714280093)
    ·
      refine ⟨6857521419059899392855035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18286723784159731714280093 6857521419059899392855035)
      ·
        refine ⟨10286282128589849089282553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6857521419059899392855035 10286282128589849089282553)
        ·
          refine ⟨7714711596442386816961915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10286282128589849089282553 7714711596442386816961915)
          ·
            refine ⟨11572067394663580225442873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7714711596442386816961915 11572067394663580225442873)
            ·
              refine ⟨8679050545997685169082155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11572067394663580225442873 8679050545997685169082155)
              ·
                refine ⟨13018575818996527753623233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8679050545997685169082155 13018575818996527753623233)
                ·
                  refine ⟨9763931864247395815217425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13018575818996527753623233 9763931864247395815217425)
                  ·
                    refine ⟨7322948898185546861413069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9763931864247395815217425 7322948898185546861413069)
                    ·
                      refine ⟨2746105836819580073029901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7322948898185546861413069 2746105836819580073029901)
                      ·
                        rfl

theorem cell23_5348022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_5348022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348022 prefixEnd_5348022 := by exact prefixLift 5348022
  have htrace : WordTrace (prefixWord ++ tailWord_5348022) baseStart_5348022 baseEnd_5348022 := by
    simpa [prefixWord, tailWord_5348022, baseEnd_5348022] using wordTrace_append hprefix tailTrace_5348022
  have hstable : (prefixWord ++ tailWord_5348022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348022).length < 2 ^ (prefixWord ++ tailWord_5348022).sum := by decide
  have hdescent : baseEnd_5348022 < baseStart_5348022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348068 : List Nat := [2, 3, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_5348068 : Nat := 118140960795 + 5348068 * 2 ^ 59
def prefixEnd_5348068 : Nat := 4983230072969 + 3 ^ 40 * 5348068 * 2
def baseEnd_5348068 : Nat := 915376485643228964351563

theorem tailTrace_5348068 : CollatzResearch.WordTrace tailWord_5348068 prefixEnd_5348068 915376485643228964351563 := by
  unfold tailWord_5348068
  simp only [CollatzResearch.WordTrace]
  refine ⟨97530032394435244070914429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130040043192580325427885905 97530032394435244070914429)
  ·
    refine ⟨36573762147913216526592911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97530032394435244070914429 36573762147913216526592911)
    ·
      refine ⟨54860643221869824789889367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36573762147913216526592911 54860643221869824789889367)
      ·
        refine ⟨82290964832804737184834051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54860643221869824789889367 82290964832804737184834051)
        ·
          refine ⟨123436447249207105777251077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82290964832804737184834051 123436447249207105777251077)
          ·
            refine ⟨23144333859226332333234577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123436447249207105777251077 23144333859226332333234577)
            ·
              refine ⟨17358250394419749249925933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23144333859226332333234577 17358250394419749249925933)
              ·
                refine ⟨6509343897907405968722225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17358250394419749249925933 6509343897907405968722225)
                ·
                  refine ⟨4882007923430554476541669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6509343897907405968722225 4882007923430554476541669)
                  ·
                    refine ⟨915376485643228964351563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4882007923430554476541669 915376485643228964351563)
                    ·
                      rfl

theorem cell23_5348068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_5348068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348068 prefixEnd_5348068 := by exact prefixLift 5348068
  have htrace : WordTrace (prefixWord ++ tailWord_5348068) baseStart_5348068 baseEnd_5348068 := by
    simpa [prefixWord, tailWord_5348068, baseEnd_5348068] using wordTrace_append hprefix tailTrace_5348068
  have hstable : (prefixWord ++ tailWord_5348068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348068).length < 2 ^ (prefixWord ++ tailWord_5348068).sum := by decide
  have hdescent : baseEnd_5348068 < baseStart_5348068 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348078 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_5348078 : Nat := 118140960795 + 5348078 * 2 ^ 59
def prefixEnd_5348078 : Nat := 4983230072969 + 3 ^ 40 * 5348078 * 2
def baseEnd_5348078 : Nat := 2746134591736231853929643

theorem tailTrace_5348078 : CollatzResearch.WordTrace tailWord_5348078 prefixEnd_5348078 2746134591736231853929643 := by
  unfold tailWord_5348078
  simp only [CollatzResearch.WordTrace]
  refine ⟨24382553689854282481211611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130040286345889506566461925 24382553689854282481211611)
  ·
    refine ⟨36573830534781423721817417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24382553689854282481211611 36573830534781423721817417)
    ·
      refine ⟨27430372901086067791363063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36573830534781423721817417 27430372901086067791363063)
      ·
        refine ⟨41145559351629101687044595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27430372901086067791363063 41145559351629101687044595)
        ·
          refine ⟨61718339027443652530566893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41145559351629101687044595 61718339027443652530566893)
          ·
            refine ⟨23144377135291369698962585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61718339027443652530566893 23144377135291369698962585)
            ·
              refine ⟨17358282851468527274221939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23144377135291369698962585 17358282851468527274221939)
              ·
                refine ⟨26037424277202790911332909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17358282851468527274221939 26037424277202790911332909)
                ·
                  refine ⟨9764034103951046591749841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26037424277202790911332909 9764034103951046591749841)
                  ·
                    refine ⟨7323025577963284943812381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9764034103951046591749841 7323025577963284943812381)
                    ·
                      refine ⟨2746134591736231853929643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7323025577963284943812381 2746134591736231853929643)
                      ·
                        rfl

theorem cell23_5348078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_5348078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348078 prefixEnd_5348078 := by exact prefixLift 5348078
  have htrace : WordTrace (prefixWord ++ tailWord_5348078) baseStart_5348078 baseEnd_5348078 := by
    simpa [prefixWord, tailWord_5348078, baseEnd_5348078] using wordTrace_append hprefix tailTrace_5348078
  have hstable : (prefixWord ++ tailWord_5348078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348078).length < 2 ^ (prefixWord ++ tailWord_5348078).sum := by decide
  have hdescent : baseEnd_5348078 < baseStart_5348078 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348081 : List Nat := [1, 2, 2, 2, 2, 2, 5, 7]
def baseStart_5348081 : Nat := 118140960795 + 5348081 * 2 ^ 59
def prefixEnd_5348081 : Nat := 4983230072969 + 3 ^ 40 * 5348081 * 2
def baseEnd_5348081 : Nat := 101708745636229457118227

theorem tailTrace_5348081 : CollatzResearch.WordTrace tailWord_5348081 prefixEnd_5348081 101708745636229457118227 := by
  unfold tailWord_5348081
  simp only [CollatzResearch.WordTrace]
  refine ⟨195060538937823391362052097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130040359291882260908034731 195060538937823391362052097)
  ·
    refine ⟨146295404203367543521539073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195060538937823391362052097 146295404203367543521539073)
    ·
      refine ⟨109721553152525657641154305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146295404203367543521539073 109721553152525657641154305)
      ·
        refine ⟨82291164864394243230865729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109721553152525657641154305 82291164864394243230865729)
        ·
          refine ⟨61718373648295682423149297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82291164864394243230865729 61718373648295682423149297)
          ·
            refine ⟨46288780236221761817361973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61718373648295682423149297 46288780236221761817361973)
            ·
              refine ⟨4339573147145790170377685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46288780236221761817361973 4339573147145790170377685)
              ·
                refine ⟨101708745636229457118227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4339573147145790170377685 101708745636229457118227)
                ·
                  rfl

theorem cell23_5348081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 5, 7].length) (baseStart_5348081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348081 prefixEnd_5348081 := by exact prefixLift 5348081
  have htrace : WordTrace (prefixWord ++ tailWord_5348081) baseStart_5348081 baseEnd_5348081 := by
    simpa [prefixWord, tailWord_5348081, baseEnd_5348081] using wordTrace_append hprefix tailTrace_5348081
  have hstable : (prefixWord ++ tailWord_5348081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348081).length < 2 ^ (prefixWord ++ tailWord_5348081).sum := by decide
  have hdescent : baseEnd_5348081 < baseStart_5348081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348092 : List Nat := [2, 2, 2, 1, 3, 2, 1, 5, 1, 2, 2]
def baseStart_5348092 : Nat := 118140960795 + 5348092 * 2 ^ 59
def prefixEnd_5348092 : Nat := 4983230072969 + 3 ^ 40 * 5348092 * 2
def baseEnd_5348092 : Nat := 2746141780465394799154579

theorem tailTrace_5348092 : CollatzResearch.WordTrace tailWord_5348092 prefixEnd_5348092 2746141780465394799154579 := by
  unfold tailWord_5348092
  simp only [CollatzResearch.WordTrace]
  refine ⟨97530470070391770120351265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130040626760522360160468353 97530470070391770120351265)
  ·
    refine ⟨73147852552793827590263449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97530470070391770120351265 73147852552793827590263449)
    ·
      refine ⟨54860889414595370692697587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73147852552793827590263449 54860889414595370692697587)
      ·
        refine ⟨82291334121893056039046381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54860889414595370692697587 82291334121893056039046381)
        ·
          refine ⟨30859250295709896014642393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82291334121893056039046381 30859250295709896014642393)
          ·
            refine ⟨23144437721782422010981795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30859250295709896014642393 23144437721782422010981795)
            ·
              refine ⟨34716656582673633016472693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23144437721782422010981795 34716656582673633016472693)
              ·
                refine ⟨3254686554625653095294315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34716656582673633016472693 3254686554625653095294315)
                ·
                  refine ⟨4882029831938479642941473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3254686554625653095294315 4882029831938479642941473)
                  ·
                    refine ⟨3661522373953859732206105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4882029831938479642941473 3661522373953859732206105)
                    ·
                      refine ⟨2746141780465394799154579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3661522373953859732206105 2746141780465394799154579)
                      ·
                        rfl

theorem cell23_5348092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 1, 2, 2].length) (baseStart_5348092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348092 prefixEnd_5348092 := by exact prefixLift 5348092
  have htrace : WordTrace (prefixWord ++ tailWord_5348092) baseStart_5348092 baseEnd_5348092 := by
    simpa [prefixWord, tailWord_5348092, baseEnd_5348092] using wordTrace_append hprefix tailTrace_5348092
  have hstable : (prefixWord ++ tailWord_5348092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348092).length < 2 ^ (prefixWord ++ tailWord_5348092).sum := by decide
  have hdescent : baseEnd_5348092 < baseStart_5348092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348151 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 5]
def baseStart_5348151 : Nat := 118140960795 + 5348151 * 2 ^ 59
def prefixEnd_5348151 : Nat := 4983230072969 + 3 ^ 40 * 5348151 * 2
def baseEnd_5348151 : Nat := 2746172075824010068316807

theorem tailTrace_5348151 : CollatzResearch.WordTrace tailWord_5348151 prefixEnd_5348151 2746172075824010068316807 := by
  unfold tailWord_5348151
  simp only [CollatzResearch.WordTrace]
  refine ⟨195063092047569793317100307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130042061365046528878066871 195063092047569793317100307)
  ·
    refine ⟨292594638071354689975650461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195063092047569793317100307 292594638071354689975650461)
    ·
      refine ⟨109722989276758008740868923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292594638071354689975650461 109722989276758008740868923)
      ·
        refine ⟨164584483915137013111303385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109722989276758008740868923 164584483915137013111303385)
        ·
          refine ⟨123438362936352759833477539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164584483915137013111303385 123438362936352759833477539)
          ·
            refine ⟨185157544404529139750216309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123438362936352759833477539 185157544404529139750216309)
            ·
              refine ⟨17358519787924606851582779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 185157544404529139750216309 17358519787924606851582779)
              ·
                refine ⟨26037779681886910277374169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17358519787924606851582779 26037779681886910277374169)
                ·
                  refine ⟨19528334761415182708030627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26037779681886910277374169 19528334761415182708030627)
                  ·
                    refine ⟨29292502142122774062045941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19528334761415182708030627 29292502142122774062045941)
                    ·
                      refine ⟨2746172075824010068316807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29292502142122774062045941 2746172075824010068316807)
                      ·
                        rfl

theorem cell23_5348151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 1, 5].length) (baseStart_5348151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348151 prefixEnd_5348151 := by exact prefixLift 5348151
  have htrace : WordTrace (prefixWord ++ tailWord_5348151) baseStart_5348151 baseEnd_5348151 := by
    simpa [prefixWord, tailWord_5348151, baseEnd_5348151] using wordTrace_append hprefix tailTrace_5348151
  have hstable : (prefixWord ++ tailWord_5348151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348151).length < 2 ^ (prefixWord ++ tailWord_5348151).sum := by decide
  have hdescent : baseEnd_5348151 < baseStart_5348151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348211 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 5]
def baseStart_5348211 : Nat := 118140960795 + 5348211 * 2 ^ 59
def prefixEnd_5348211 : Nat := 4983230072969 + 3 ^ 40 * 5348211 * 2
def baseEnd_5348211 : Nat := 2746202884663279833566531

theorem tailTrace_5348211 : CollatzResearch.WordTrace tailWord_5348211 prefixEnd_5348211 2746202884663279833566531 := by
  unfold tailWord_5348211
  simp only [CollatzResearch.WordTrace]
  refine ⟨195065280427352423564284487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130043520284901615709522991 195065280427352423564284487)
  ·
    refine ⟨292597920641028635346426731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195065280427352423564284487 292597920641028635346426731)
    ·
      refine ⟨438896880961542953019640097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292597920641028635346426731 438896880961542953019640097)
      ·
        refine ⟨329172660721157214764730073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438896880961542953019640097 329172660721157214764730073)
        ·
          refine ⟨246879495540867911073547555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329172660721157214764730073 246879495540867911073547555)
          ·
            refine ⟨370319243311301866610321333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246879495540867911073547555 370319243311301866610321333)
            ·
              refine ⟨34717429060434549994717625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 370319243311301866610321333 34717429060434549994717625)
              ·
                refine ⟨26038071795325912496038219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34717429060434549994717625 26038071795325912496038219)
                ·
                  refine ⟨39057107692988868744057329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26038071795325912496038219 39057107692988868744057329)
                  ·
                    refine ⟨29292830769741651558042997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39057107692988868744057329 29292830769741651558042997)
                    ·
                      refine ⟨2746202884663279833566531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29292830769741651558042997 2746202884663279833566531)
                      ·
                        rfl

theorem cell23_5348211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 2, 5].length) (baseStart_5348211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348211 prefixEnd_5348211 := by exact prefixLift 5348211
  have htrace : WordTrace (prefixWord ++ tailWord_5348211) baseStart_5348211 baseEnd_5348211 := by
    simpa [prefixWord, tailWord_5348211, baseEnd_5348211] using wordTrace_append hprefix tailTrace_5348211
  have hstable : (prefixWord ++ tailWord_5348211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348211).length < 2 ^ (prefixWord ++ tailWord_5348211).sum := by decide
  have hdescent : baseEnd_5348211 < baseStart_5348211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348252 : List Nat := [2, 2, 3, 3, 2, 2, 1, 1, 2, 5]
def baseStart_5348252 : Nat := 118140960795 + 5348252 * 2 ^ 59
def prefixEnd_5348252 : Nat := 4983230072969 + 3 ^ 40 * 5348252 * 2
def baseEnd_5348252 : Nat := 915407979123371391051281

theorem tailTrace_5348252 : CollatzResearch.WordTrace tailWord_5348252 prefixEnd_5348252 915407979123371391051281 := by
  unfold tailWord_5348252
  simp only [CollatzResearch.WordTrace]
  refine ⟨97533387910101943783263505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130044517213469258377684673 97533387910101943783263505)
  ·
    refine ⟨73150040932576457837447629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97533387910101943783263505 73150040932576457837447629)
    ·
      refine ⟨27431265349716171689042861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73150040932576457837447629 27431265349716171689042861)
      ·
        refine ⟨10286724506143564383391073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27431265349716171689042861 10286724506143564383391073)
        ·
          refine ⟨7715043379607673287543305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10286724506143564383391073 7715043379607673287543305)
          ·
            refine ⟨5786282534705754965657479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7715043379607673287543305 5786282534705754965657479)
            ·
              refine ⟨8679423802058632448486219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5786282534705754965657479 8679423802058632448486219)
              ·
                refine ⟨13019135703087948672729329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8679423802058632448486219 13019135703087948672729329)
                ·
                  refine ⟨9764351777315961504546997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13019135703087948672729329 9764351777315961504546997)
                  ·
                    refine ⟨915407979123371391051281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9764351777315961504546997 915407979123371391051281)
                    ·
                      rfl

theorem cell23_5348252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_5348252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348252 prefixEnd_5348252 := by exact prefixLift 5348252
  have htrace : WordTrace (prefixWord ++ tailWord_5348252) baseStart_5348252 baseEnd_5348252 := by
    simpa [prefixWord, tailWord_5348252, baseEnd_5348252] using wordTrace_append hprefix tailTrace_5348252
  have hstable : (prefixWord ++ tailWord_5348252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348252).length < 2 ^ (prefixWord ++ tailWord_5348252).sum := by decide
  have hdescent : baseEnd_5348252 < baseStart_5348252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348255 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 4]
def baseStart_5348255 : Nat := 118140960795 + 5348255 * 2 ^ 59
def prefixEnd_5348255 : Nat := 4983230072969 + 3 ^ 40 * 5348255 * 2
def baseEnd_5348255 : Nat := 2746225477812077661416329

theorem tailTrace_5348255 : CollatzResearch.WordTrace tailWord_5348255 prefixEnd_5348255 2746225477812077661416329 := by
  unfold tailWord_5348255
  simp only [CollatzResearch.WordTrace]
  refine ⟨195066885239193019078886219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130044590159462012719257479 195066885239193019078886219)
  ·
    refine ⟨292600327858789528618329329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195066885239193019078886219 292600327858789528618329329)
    ·
      refine ⟨219450245894092146463746997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292600327858789528618329329 219450245894092146463746997)
      ·
        refine ⟨20573460552571138730976281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 219450245894092146463746997 20573460552571138730976281)
        ·
          refine ⟨15430095414428354048232211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20573460552571138730976281 15430095414428354048232211)
          ·
            refine ⟨23145143121642531072348317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15430095414428354048232211 23145143121642531072348317)
            ·
              refine ⟨8679428670615949152130619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23145143121642531072348317 8679428670615949152130619)
              ·
                refine ⟨13019143005923923728195929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8679428670615949152130619 13019143005923923728195929)
                ·
                  refine ⟨9764357254442942796146947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13019143005923923728195929 9764357254442942796146947)
                  ·
                    refine ⟨14646535881664414194220421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9764357254442942796146947 14646535881664414194220421)
                    ·
                      refine ⟨2746225477812077661416329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14646535881664414194220421 2746225477812077661416329)
                      ·
                        rfl

theorem cell23_5348255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_5348255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348255 prefixEnd_5348255 := by exact prefixLift 5348255
  have htrace : WordTrace (prefixWord ++ tailWord_5348255) baseStart_5348255 baseEnd_5348255 := by
    simpa [prefixWord, tailWord_5348255, baseEnd_5348255] using wordTrace_append hprefix tailTrace_5348255
  have hstable : (prefixWord ++ tailWord_5348255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348255).length < 2 ^ (prefixWord ++ tailWord_5348255).sum := by decide
  have hdescent : baseEnd_5348255 < baseStart_5348255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348305 : List Nat := [1, 2, 2, 1, 2, 1, 3, 4, 3, 1, 3]
def baseStart_5348305 : Nat := 118140960795 + 5348305 * 2 ^ 59
def prefixEnd_5348305 : Nat := 4983230072969 + 3 ^ 40 * 5348305 * 2
def baseEnd_5348305 : Nat := 2746251151844802465791099

theorem tailTrace_5348305 : CollatzResearch.WordTrace tailWord_5348305 prefixEnd_5348305 2746251151844802465791099 := by
  unfold tailWord_5348305
  simp only [CollatzResearch.WordTrace]
  refine ⟨195068708889011877618206369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130045805926007918412137579 195068708889011877618206369)
  ·
    refine ⟨146301531666758908213654777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195068708889011877618206369 146301531666758908213654777)
    ·
      refine ⟨109726148750069181160241083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146301531666758908213654777 109726148750069181160241083)
      ·
        refine ⟨164589223125103771740361625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109726148750069181160241083 164589223125103771740361625)
        ·
          refine ⟨123441917343827828805271219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164589223125103771740361625 123441917343827828805271219)
          ·
            refine ⟨185162876015741743207906829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123441917343827828805271219 185162876015741743207906829)
            ·
              refine ⟨69436078505903153702965061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 185162876015741743207906829 69436078505903153702965061)
              ·
                refine ⟨13019264719856841319305949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69436078505903153702965061 13019264719856841319305949)
                ·
                  refine ⟨4882224269946315494739731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13019264719856841319305949 4882224269946315494739731)
                  ·
                    refine ⟨7323336404919473242109597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4882224269946315494739731 7323336404919473242109597)
                    ·
                      refine ⟨2746251151844802465791099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7323336404919473242109597 2746251151844802465791099)
                      ·
                        rfl

theorem cell23_5348305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 4, 3, 1, 3].length) (baseStart_5348305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348305 prefixEnd_5348305 := by exact prefixLift 5348305
  have htrace : WordTrace (prefixWord ++ tailWord_5348305) baseStart_5348305 baseEnd_5348305 := by
    simpa [prefixWord, tailWord_5348305, baseEnd_5348305] using wordTrace_append hprefix tailTrace_5348305
  have hstable : (prefixWord ++ tailWord_5348305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348305).length < 2 ^ (prefixWord ++ tailWord_5348305).sum := by decide
  have hdescent : baseEnd_5348305 < baseStart_5348305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348362 : List Nat := [3, 1, 2, 2, 3, 1, 3, 2, 1, 1, 4]
def baseStart_5348362 : Nat := 118140960795 + 5348362 * 2 ^ 59
def prefixEnd_5348362 : Nat := 4983230072969 + 3 ^ 40 * 5348362 * 2
def baseEnd_5348362 : Nat := 2746280420242108742778337

theorem tailTrace_5348362 : CollatzResearch.WordTrace tailWord_5348362 prefixEnd_5348362 2746280420242108742778337 := by
  unfold tailWord_5348362
  simp only [CollatzResearch.WordTrace]
  refine ⟨48767696962451344088257835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130047191899870250902020893 48767696962451344088257835)
  ·
    refine ⟨73151545443677016132386753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48767696962451344088257835 73151545443677016132386753)
    ·
      refine ⟨54863659082757762099290065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73151545443677016132386753 54863659082757762099290065)
      ·
        refine ⟨41147744312068321574467549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54863659082757762099290065 41147744312068321574467549)
        ·
          refine ⟨15430404117025620590425331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41147744312068321574467549 15430404117025620590425331)
          ·
            refine ⟨23145606175538430885637997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15430404117025620590425331 23145606175538430885637997)
            ·
              refine ⟨8679602315826911582114249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23145606175538430885637997 8679602315826911582114249)
              ·
                refine ⟨6509701736870183686585687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8679602315826911582114249 6509701736870183686585687)
                ·
                  refine ⟨9764552605305275529878531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6509701736870183686585687 9764552605305275529878531)
                  ·
                    refine ⟨14646828907957913294817797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9764552605305275529878531 14646828907957913294817797)
                    ·
                      refine ⟨2746280420242108742778337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14646828907957913294817797 2746280420242108742778337)
                      ·
                        rfl

theorem cell23_5348362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_5348362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348362 prefixEnd_5348362 := by exact prefixLift 5348362
  have htrace : WordTrace (prefixWord ++ tailWord_5348362) baseStart_5348362 baseEnd_5348362 := by
    simpa [prefixWord, tailWord_5348362, baseEnd_5348362] using wordTrace_append hprefix tailTrace_5348362
  have hstable : (prefixWord ++ tailWord_5348362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348362).length < 2 ^ (prefixWord ++ tailWord_5348362).sum := by decide
  have hdescent : baseEnd_5348362 < baseStart_5348362 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348375 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 4]
def baseStart_5348375 : Nat := 118140960795 + 5348375 * 2 ^ 59
def prefixEnd_5348375 : Nat := 4983230072969 + 3 ^ 40 * 5348375 * 2
def baseEnd_5348375 : Nat := 2746287095490617191915777

theorem tailTrace_5348375 : CollatzResearch.WordTrace tailWord_5348375 prefixEnd_5348375 2746287095490617191915777 := by
  unfold tailWord_5348375
  simp only [CollatzResearch.WordTrace]
  refine ⟨195071261998758279573254579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130047507999172186382169719 195071261998758279573254579)
  ·
    refine ⟨292606892998137419359881869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195071261998758279573254579 292606892998137419359881869)
    ·
      refine ⟨109727584874301532259955701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292606892998137419359881869 109727584874301532259955701)
      ·
        refine ⟨10286961081965768649370847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 109727584874301532259955701 10286961081965768649370847)
        ·
          refine ⟨15430441622948652974056271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10286961081965768649370847 15430441622948652974056271)
          ·
            refine ⟨23145662434422979461084407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15430441622948652974056271 23145662434422979461084407)
            ·
              refine ⟨34718493651634469191626611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23145662434422979461084407 34718493651634469191626611)
              ·
                refine ⟨52077740477451703787439917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34718493651634469191626611 52077740477451703787439917)
                ·
                  refine ⟨19529152679044388920289969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52077740477451703787439917 19529152679044388920289969)
                  ·
                    refine ⟨14646864509283291690217477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19529152679044388920289969 14646864509283291690217477)
                    ·
                      refine ⟨2746287095490617191915777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14646864509283291690217477 2746287095490617191915777)
                      ·
                        rfl

theorem cell23_5348375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_5348375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348375 prefixEnd_5348375 := by exact prefixLift 5348375
  have htrace : WordTrace (prefixWord ++ tailWord_5348375) baseStart_5348375 baseEnd_5348375 := by
    simpa [prefixWord, tailWord_5348375, baseEnd_5348375] using wordTrace_append hprefix tailTrace_5348375
  have hstable : (prefixWord ++ tailWord_5348375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348375).length < 2 ^ (prefixWord ++ tailWord_5348375).sum := by decide
  have hdescent : baseEnd_5348375 < baseStart_5348375 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348412 : List Nat := [2, 2, 2, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_5348412 : Nat := 118140960795 + 5348412 * 2 ^ 59
def prefixEnd_5348412 : Nat := 4983230072969 + 3 ^ 40 * 5348412 * 2
def baseEnd_5348412 : Nat := 2746306094274833547153107

theorem tailTrace_5348412 : CollatzResearch.WordTrace tailWord_5348412 prefixEnd_5348412 2746306094274833547153107 := by
  unfold tailWord_5348412
  simp only [CollatzResearch.WordTrace]
  refine ⟨97536305749812117446175745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130048407666416156594900993 97536305749812117446175745)
  ·
    refine ⟨73152229312359088084631809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97536305749812117446175745 73152229312359088084631809)
    ·
      refine ⟨54864171984269316063473857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73152229312359088084631809 54864171984269316063473857)
      ·
        refine ⟨41148128988201987047605393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54864171984269316063473857 41148128988201987047605393)
        ·
          refine ⟨30861096741151490285704045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41148128988201987047605393 30861096741151490285704045)
          ·
            refine ⟨11572911277931808857139017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30861096741151490285704045 11572911277931808857139017)
            ·
              refine ⟨8679683458448856642854263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11572911277931808857139017 8679683458448856642854263)
              ·
                refine ⟨13019525187673284964281395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8679683458448856642854263 13019525187673284964281395)
                ·
                  refine ⟨19529287781509927446422093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13019525187673284964281395 19529287781509927446422093)
                  ·
                    refine ⟨7323482918066222792408285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19529287781509927446422093 7323482918066222792408285)
                    ·
                      refine ⟨2746306094274833547153107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7323482918066222792408285 2746306094274833547153107)
                      ·
                        rfl

theorem cell23_5348412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_5348412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348412 prefixEnd_5348412 := by exact prefixLift 5348412
  have htrace : WordTrace (prefixWord ++ tailWord_5348412) baseStart_5348412 baseEnd_5348412 := by
    simpa [prefixWord, tailWord_5348412, baseEnd_5348412] using wordTrace_append hprefix tailTrace_5348412
  have hstable : (prefixWord ++ tailWord_5348412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348412).length < 2 ^ (prefixWord ++ tailWord_5348412).sum := by decide
  have hdescent : baseEnd_5348412 < baseStart_5348412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348428 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 3, 8]
def baseStart_5348428 : Nat := 118140960795 + 5348428 * 2 ^ 59
def prefixEnd_5348428 : Nat := 4983230072969 + 3 ^ 40 * 5348428 * 2
def baseEnd_5348428 : Nat := 915438103321768494851011

theorem tailTrace_5348428 : CollatzResearch.WordTrace tailWord_5348428 prefixEnd_5348428 915438103321768494851011 := by
  unfold tailWord_5348428
  simp only [CollatzResearch.WordTrace]
  refine ⟨97536597533783134812466969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130048796711710846416622625 97536597533783134812466969)
  ·
    refine ⟨73152448150337351109350227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97536597533783134812466969 73152448150337351109350227)
    ·
      refine ⟨109728672225506026664025341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73152448150337351109350227 109728672225506026664025341)
      ·
        refine ⟨41148252084564759999009503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109728672225506026664025341 41148252084564759999009503)
        ·
          refine ⟨61722378126847139998514255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41148252084564759999009503 61722378126847139998514255)
          ·
            refine ⟨92583567190270709997771383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61722378126847139998514255 92583567190270709997771383)
            ·
              refine ⟨138875350785406064996657075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92583567190270709997771383 138875350785406064996657075)
              ·
                refine ⟨208313026178109097494985613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138875350785406064996657075 208313026178109097494985613)
                ·
                  refine ⟨78117384816790911560619605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208313026178109097494985613 78117384816790911560619605)
                  ·
                    refine ⟨915438103321768494851011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 78117384816790911560619605 915438103321768494851011)
                    ·
                      rfl

theorem cell23_5348428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_5348428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348428 prefixEnd_5348428 := by exact prefixLift 5348428
  have htrace : WordTrace (prefixWord ++ tailWord_5348428) baseStart_5348428 baseEnd_5348428 := by
    simpa [prefixWord, tailWord_5348428, baseEnd_5348428] using wordTrace_append hprefix tailTrace_5348428
  have hstable : (prefixWord ++ tailWord_5348428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348428).length < 2 ^ (prefixWord ++ tailWord_5348428).sum := by decide
  have hdescent : baseEnd_5348428 < baseStart_5348428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348509 : List Nat := [1, 4, 2, 1, 1, 2, 5, 2, 5]
def baseStart_5348509 : Nat := 118140960795 + 5348509 * 2 ^ 59
def prefixEnd_5348509 : Nat := 4983230072969 + 3 ^ 40 * 5348509 * 2
def baseEnd_5348509 : Nat := 305150655766479963071129

theorem tailTrace_5348509 : CollatzResearch.WordTrace tailWord_5348509 prefixEnd_5348509 305150655766479963071129 := by
  unfold tailWord_5348509
  simp only [CollatzResearch.WordTrace]
  refine ⟨195076149380272820458632581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130050766253515213639088387 195076149380272820458632581)
  ·
    refine ⟨36576778008801153835993609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195076149380272820458632581 36576778008801153835993609)
    ·
      refine ⟨27432583506600865376995207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36576778008801153835993609 27432583506600865376995207)
      ·
        refine ⟨41148875259901298065492811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27432583506600865376995207 41148875259901298065492811)
        ·
          refine ⟨61723312889851947098239217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41148875259901298065492811 61723312889851947098239217)
          ·
            refine ⟨46292484667388960323679413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61723312889851947098239217 46292484667388960323679413)
            ·
              refine ⟨4339920437567715030344945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46292484667388960323679413 4339920437567715030344945)
              ·
                refine ⟨3254940328175786272758709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4339920437567715030344945 3254940328175786272758709)
                ·
                  refine ⟨305150655766479963071129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3254940328175786272758709 305150655766479963071129)
                  ·
                    rfl

theorem cell23_5348509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_5348509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348509 prefixEnd_5348509 := by exact prefixLift 5348509
  have htrace : WordTrace (prefixWord ++ tailWord_5348509) baseStart_5348509 baseEnd_5348509 := by
    simpa [prefixWord, tailWord_5348509, baseEnd_5348509] using wordTrace_append hprefix tailTrace_5348509
  have hstable : (prefixWord ++ tailWord_5348509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348509).length < 2 ^ (prefixWord ++ tailWord_5348509).sum := by decide
  have hdescent : baseEnd_5348509 < baseStart_5348509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348512 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 2, 5, 2]
def baseStart_5348512 : Nat := 118140960795 + 5348512 * 2 ^ 59
def prefixEnd_5348512 : Nat := 4983230072969 + 3 ^ 40 * 5348512 * 2
def baseEnd_5348512 : Nat := 2746357442340283155902647

theorem tailTrace_5348512 : CollatzResearch.WordTrace tailWord_5348512 prefixEnd_5348512 2746357442340283155902647 := by
  unfold tailWord_5348512
  simp only [CollatzResearch.WordTrace]
  refine ⟨97538129399630975985495895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130050839199507967980661193 97538129399630975985495895)
  ·
    refine ⟨146307194099446463978243843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97538129399630975985495895 146307194099446463978243843)
    ·
      refine ⟨219460791149169695967365765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146307194099446463978243843 219460791149169695967365765)
      ·
        refine ⟨41148898340469317993881081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 219460791149169695967365765 41148898340469317993881081)
        ·
          refine ⟨30861673755351988495410811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41148898340469317993881081 30861673755351988495410811)
          ·
            refine ⟨46292510633027982743116217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30861673755351988495410811 46292510633027982743116217)
            ·
              refine ⟨34719382974770987057337163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46292510633027982743116217 34719382974770987057337163)
              ·
                refine ⟨52079074462156480586005745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34719382974770987057337163 52079074462156480586005745)
                ·
                  refine ⟨39059305846617360439504309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52079074462156480586005745 39059305846617360439504309)
                  ·
                    refine ⟨3661809923120377541203529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39059305846617360439504309 3661809923120377541203529)
                    ·
                      refine ⟨2746357442340283155902647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3661809923120377541203529 2746357442340283155902647)
                      ·
                        rfl

theorem cell23_5348512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_5348512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348512 prefixEnd_5348512 := by exact prefixLift 5348512
  have htrace : WordTrace (prefixWord ++ tailWord_5348512) baseStart_5348512 baseEnd_5348512 := by
    simpa [prefixWord, tailWord_5348512, baseEnd_5348512] using wordTrace_append hprefix tailTrace_5348512
  have hstable : (prefixWord ++ tailWord_5348512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348512).length < 2 ^ (prefixWord ++ tailWord_5348512).sum := by decide
  have hdescent : baseEnd_5348512 < baseStart_5348512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348605 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 1, 6, 5]
def baseStart_5348605 : Nat := 118140960795 + 5348605 * 2 ^ 59
def prefixEnd_5348605 : Nat := 4983230072969 + 3 ^ 40 * 5348605 * 2
def baseEnd_5348605 : Nat := 2746405196041151292039719

theorem tailTrace_5348605 : CollatzResearch.WordTrace tailWord_5348605 prefixEnd_5348605 2746405196041151292039719 := by
  unfold tailWord_5348605
  simp only [CollatzResearch.WordTrace]
  refine ⟨195079650787925028854127269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130053100525283352569418179 195079650787925028854127269)
  ·
    refine ⟨36577434522735942910148863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195079650787925028854127269 36577434522735942910148863)
    ·
      refine ⟨54866151784103914365223295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36577434522735942910148863 54866151784103914365223295)
      ·
        refine ⟨82299227676155871547834943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54866151784103914365223295 82299227676155871547834943)
        ·
          refine ⟨123448841514233807321752415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82299227676155871547834943 123448841514233807321752415)
          ·
            refine ⟨185173262271350710982628623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123448841514233807321752415 185173262271350710982628623)
            ·
              refine ⟨277759893407026066473942935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185173262271350710982628623 277759893407026066473942935)
              ·
                refine ⟨416639840110539099710914403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277759893407026066473942935 416639840110539099710914403)
                ·
                  refine ⟨624959760165808649566371605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416639840110539099710914403 624959760165808649566371605)
                  ·
                    refine ⟨29294988757772280448423669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 624959760165808649566371605 29294988757772280448423669)
                    ·
                      refine ⟨2746405196041151292039719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29294988757772280448423669 2746405196041151292039719)
                      ·
                        rfl

theorem cell23_5348605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_5348605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348605 prefixEnd_5348605 := by exact prefixLift 5348605
  have htrace : WordTrace (prefixWord ++ tailWord_5348605) baseStart_5348605 baseEnd_5348605 := by
    simpa [prefixWord, tailWord_5348605, baseEnd_5348605] using wordTrace_append hprefix tailTrace_5348605
  have hstable : (prefixWord ++ tailWord_5348605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348605).length < 2 ^ (prefixWord ++ tailWord_5348605).sum := by decide
  have hdescent : baseEnd_5348605 < baseStart_5348605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348616 : List Nat := [2, 1, 3, 2, 5, 1, 1, 2, 6]
def baseStart_5348616 : Nat := 118140960795 + 5348616 * 2 ^ 59
def prefixEnd_5348616 : Nat := 4983230072969 + 3 ^ 40 * 5348616 * 2
def baseEnd_5348616 : Nat := 305156760480927861000241

theorem tailTrace_5348616 : CollatzResearch.WordTrace tailWord_5348616 prefixEnd_5348616 305156760480927861000241 := by
  unfold tailWord_5348616
  simp only [CollatzResearch.WordTrace]
  refine ⟨97540025995442588866388851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130053367993923451821851801 97540025995442588866388851)
  ·
    refine ⟨146310038993163883299583277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97540025995442588866388851 146310038993163883299583277)
    ·
      refine ⟨54866264622436456237343729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146310038993163883299583277 54866264622436456237343729)
      ·
        refine ⟨41149698466827342178007797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54866264622436456237343729 41149698466827342178007797)
        ·
          refine ⟨3857784231265063329188231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41149698466827342178007797 3857784231265063329188231)
          ·
            refine ⟨5786676346897594993782347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3857784231265063329188231 5786676346897594993782347)
            ·
              refine ⟨8680014520346392490673521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5786676346897594993782347 8680014520346392490673521)
              ·
                refine ⟨6510010890259794368005141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8680014520346392490673521 6510010890259794368005141)
                ·
                  refine ⟨305156760480927861000241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6510010890259794368005141 305156760480927861000241)
                  ·
                    rfl

theorem cell23_5348616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 6].length) (baseStart_5348616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348616 prefixEnd_5348616 := by exact prefixLift 5348616
  have htrace : WordTrace (prefixWord ++ tailWord_5348616) baseStart_5348616 baseEnd_5348616 := by
    simpa [prefixWord, tailWord_5348616, baseEnd_5348616] using wordTrace_append hprefix tailTrace_5348616
  have hstable : (prefixWord ++ tailWord_5348616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348616).length < 2 ^ (prefixWord ++ tailWord_5348616).sum := by decide
  have hdescent : baseEnd_5348616 < baseStart_5348616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348649 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 9, 2, 2]
def baseStart_5348649 : Nat := 118140960795 + 5348649 * 2 ^ 59
def prefixEnd_5348649 : Nat := 4983230072969 + 3 ^ 40 * 5348649 * 2
def baseEnd_5348649 : Nat := 2746427789189949119889517

theorem tailTrace_5348649 : CollatzResearch.WordTrace tailWord_5348649 prefixEnd_5348649 2746427789189949119889517 := by
  unfold tailWord_5348649
  simp only [CollatzResearch.WordTrace]
  refine ⟨195081255599765624368729001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130054170399843749579152667 195081255599765624368729001)
  ·
    refine ⟨146310941699824218276546751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195081255599765624368729001 146310941699824218276546751)
    ·
      refine ⟨219466412549736327414820127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146310941699824218276546751 219466412549736327414820127)
      ·
        refine ⟨329199618824604491122230191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219466412549736327414820127 329199618824604491122230191)
        ·
          refine ⟨493799428236906736683345287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329199618824604491122230191 493799428236906736683345287)
          ·
            refine ⟨740699142355360105025017931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493799428236906736683345287 740699142355360105025017931)
            ·
              refine ⟨1111048713533040157537526897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 740699142355360105025017931 1111048713533040157537526897)
              ·
                refine ⟨833286535149780118153145173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1111048713533040157537526897 833286535149780118153145173)
                ·
                  refine ⟨4882538291893242879803585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 833286535149780118153145173 4882538291893242879803585)
                  ·
                    refine ⟨3661903718919932159852689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4882538291893242879803585 3661903718919932159852689)
                    ·
                      refine ⟨2746427789189949119889517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3661903718919932159852689 2746427789189949119889517)
                      ·
                        rfl

theorem cell23_5348649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 9, 2, 2].length) (baseStart_5348649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348649 prefixEnd_5348649 := by exact prefixLift 5348649
  have htrace : WordTrace (prefixWord ++ tailWord_5348649) baseStart_5348649 baseEnd_5348649 := by
    simpa [prefixWord, tailWord_5348649, baseEnd_5348649] using wordTrace_append hprefix tailTrace_5348649
  have hstable : (prefixWord ++ tailWord_5348649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348649).length < 2 ^ (prefixWord ++ tailWord_5348649).sum := by decide
  have hdescent : baseEnd_5348649 < baseStart_5348649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348676 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_5348676 : Nat := 118140960795 + 5348676 * 2 ^ 59
def prefixEnd_5348676 : Nat := 4983230072969 + 3 ^ 40 * 5348676 * 2
def baseEnd_5348676 : Nat := 915480551055873504750631

theorem tailTrace_5348676 : CollatzResearch.WordTrace tailWord_5348676 prefixEnd_5348676 915480551055873504750631 := by
  unfold tailWord_5348676
  simp only [CollatzResearch.WordTrace]
  refine ⟨97541120185333903989980941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130054826913778538653307921 97541120185333903989980941)
  ·
    refine ⟨36577920069500213996242853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97541120185333903989980941 36577920069500213996242853)
    ·
      refine ⟨6858360013031290124295535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36577920069500213996242853 6858360013031290124295535)
      ·
        refine ⟨10287540019546935186443303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6858360013031290124295535 10287540019546935186443303)
        ·
          refine ⟨15431310029320402779664955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10287540019546935186443303 15431310029320402779664955)
          ·
            refine ⟨23146965043980604169497433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15431310029320402779664955 23146965043980604169497433)
            ·
              refine ⟨17360223782985453127123075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23146965043980604169497433 17360223782985453127123075)
              ·
                refine ⟨26040335674478179690684613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17360223782985453127123075 26040335674478179690684613)
                ·
                  refine ⟨4882562938964658692003365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26040335674478179690684613 4882562938964658692003365)
                  ·
                    refine ⟨915480551055873504750631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4882562938964658692003365 915480551055873504750631)
                    ·
                      rfl

theorem cell23_5348676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_5348676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348676 prefixEnd_5348676 := by exact prefixLift 5348676
  have htrace : WordTrace (prefixWord ++ tailWord_5348676) baseStart_5348676 baseEnd_5348676 := by
    simpa [prefixWord, tailWord_5348676, baseEnd_5348676] using wordTrace_append hprefix tailTrace_5348676
  have hstable : (prefixWord ++ tailWord_5348676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348676).length < 2 ^ (prefixWord ++ tailWord_5348676).sum := by decide
  have hdescent : baseEnd_5348676 < baseStart_5348676 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348692 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_5348692 : Nat := 118140960795 + 5348692 * 2 ^ 59
def prefixEnd_5348692 : Nat := 4983230072969 + 3 ^ 40 * 5348692 * 2
def baseEnd_5348692 : Nat := 2746449868858092451651819

theorem tailTrace_5348692 : CollatzResearch.WordTrace tailWord_5348692 prefixEnd_5348692 2746449868858092451651819 := by
  unfold tailWord_5348692
  simp only [CollatzResearch.WordTrace]
  refine ⟨97541411969304921356272165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130055215959073228475029553 97541411969304921356272165)
  ·
    refine ⟨18289014744244672754301031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97541411969304921356272165 18289014744244672754301031)
    ·
      refine ⟨27433522116367009131451547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18289014744244672754301031 27433522116367009131451547)
      ·
        refine ⟨41150283174550513697177321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27433522116367009131451547 41150283174550513697177321)
        ·
          refine ⟨30862712380912885272882991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41150283174550513697177321 30862712380912885272882991)
          ·
            refine ⟨46294068571369327909324487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30862712380912885272882991 46294068571369327909324487)
            ·
              refine ⟨69441102857053991863986731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46294068571369327909324487 69441102857053991863986731)
              ·
                refine ⟨104161654285580987795980097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69441102857053991863986731 104161654285580987795980097)
                ·
                  refine ⟨78121240714185740846985073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 104161654285580987795980097 78121240714185740846985073)
                  ·
                    refine ⟨58590930535639305635238805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 78121240714185740846985073 58590930535639305635238805)
                    ·
                      refine ⟨2746449868858092451651819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58590930535639305635238805 2746449868858092451651819)
                      ·
                        rfl

theorem cell23_5348692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_5348692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348692 prefixEnd_5348692 := by exact prefixLift 5348692
  have htrace : WordTrace (prefixWord ++ tailWord_5348692) baseStart_5348692 baseEnd_5348692 := by
    simpa [prefixWord, tailWord_5348692, baseEnd_5348692] using wordTrace_append hprefix tailTrace_5348692
  have hstable : (prefixWord ++ tailWord_5348692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348692).length < 2 ^ (prefixWord ++ tailWord_5348692).sum := by decide
  have hdescent : baseEnd_5348692 < baseStart_5348692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348693 : List Nat := [1, 3, 2, 2, 3, 3, 2, 1, 2, 4]
def baseStart_5348693 : Nat := 118140960795 + 5348693 * 2 ^ 59
def prefixEnd_5348693 : Nat := 4983230072969 + 3 ^ 40 * 5348693 * 2
def baseEnd_5348693 : Nat := 915483460779582315913105

theorem tailTrace_5348693 : CollatzResearch.WordTrace tailWord_5348693 prefixEnd_5348693 915483460779582315913105 := by
  unfold tailWord_5348693
  simp only [CollatzResearch.WordTrace]
  refine ⟨195082860411606219883330733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130055240274404146588887155 195082860411606219883330733)
  ·
    refine ⟨73156072654352332456249025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195082860411606219883330733 73156072654352332456249025)
    ·
      refine ⟨54867054490764249342186769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73156072654352332456249025 54867054490764249342186769)
      ·
        refine ⟨41150290868073187006640077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54867054490764249342186769 41150290868073187006640077)
        ·
          refine ⟨15431359075527445127490029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41150290868073187006640077 15431359075527445127490029)
          ·
            refine ⟨5786759653322791922808761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15431359075527445127490029 5786759653322791922808761)
            ·
              refine ⟨4340069739992093942106571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5786759653322791922808761 4340069739992093942106571)
              ·
                refine ⟨6510104609988140913159857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4340069739992093942106571 6510104609988140913159857)
                ·
                  refine ⟨4882578457491105684869893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6510104609988140913159857 4882578457491105684869893)
                  ·
                    refine ⟨915483460779582315913105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4882578457491105684869893 915483460779582315913105)
                    ·
                      rfl

theorem cell23_5348693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_5348693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348693 prefixEnd_5348693 := by exact prefixLift 5348693
  have htrace : WordTrace (prefixWord ++ tailWord_5348693) baseStart_5348693 baseEnd_5348693 := by
    simpa [prefixWord, tailWord_5348693, baseEnd_5348693] using wordTrace_append hprefix tailTrace_5348693
  have hstable : (prefixWord ++ tailWord_5348693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348693).length < 2 ^ (prefixWord ++ tailWord_5348693).sum := by decide
  have hdescent : baseEnd_5348693 < baseStart_5348693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348732 : List Nat := [2, 2, 2, 1, 1, 1, 4, 2, 2, 6]
def baseStart_5348732 : Nat := 118140960795 + 5348732 * 2 ^ 59
def prefixEnd_5348732 : Nat := 4983230072969 + 3 ^ 40 * 5348732 * 2
def baseEnd_5348732 : Nat := 915490136028090765050545

theorem tailTrace_5348732 : CollatzResearch.WordTrace tailWord_5348732 prefixEnd_5348732 915490136028090765050545 := by
  unfold tailWord_5348732
  simp only [CollatzResearch.WordTrace]
  refine ⟨97542141429232464772000225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130056188572309953029333633 97542141429232464772000225)
  ·
    refine ⟨73156606071924348579000169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97542141429232464772000225 73156606071924348579000169)
    ·
      refine ⟨54867454553943261434250127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73156606071924348579000169 54867454553943261434250127)
      ·
        refine ⟨82301181830914892151375191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54867454553943261434250127 82301181830914892151375191)
        ·
          refine ⟨123451772746372338227062787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82301181830914892151375191 123451772746372338227062787)
          ·
            refine ⟨185177659119558507340594181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123451772746372338227062787 185177659119558507340594181)
            ·
              refine ⟨34720811084917220126361409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 185177659119558507340594181 34720811084917220126361409)
              ·
                refine ⟨26040608313687915094771057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34720811084917220126361409 26040608313687915094771057)
                ·
                  refine ⟨19530456235265936321078293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26040608313687915094771057 19530456235265936321078293)
                  ·
                    refine ⟨915490136028090765050545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19530456235265936321078293 915490136028090765050545)
                    ·
                      rfl

theorem cell23_5348732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_5348732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348732 prefixEnd_5348732 := by exact prefixLift 5348732
  have htrace : WordTrace (prefixWord ++ tailWord_5348732) baseStart_5348732 baseEnd_5348732 := by
    simpa [prefixWord, tailWord_5348732, baseEnd_5348732] using wordTrace_append hprefix tailTrace_5348732
  have hstable : (prefixWord ++ tailWord_5348732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348732).length < 2 ^ (prefixWord ++ tailWord_5348732).sum := by decide
  have hdescent : baseEnd_5348732 < baseStart_5348732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348734 : List Nat := [4, 2, 3, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5348734 : Nat := 118140960795 + 5348734 * 2 ^ 59
def prefixEnd_5348734 : Nat := 4983230072969 + 3 ^ 40 * 5348734 * 2
def baseEnd_5348734 : Nat := 2746471435045581287326627

theorem tailTrace_5348734 : CollatzResearch.WordTrace tailWord_5348734 prefixEnd_5348734 2746471435045581287326627 := by
  unfold tailWord_5348734
  simp only [CollatzResearch.WordTrace]
  refine ⟨24385544475557210485696657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130056237202971789257048837 24385544475557210485696657)
  ·
    refine ⟨18289158356667907864272493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24385544475557210485696657 18289158356667907864272493)
    ·
      refine ⟨6858434383750465449102185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18289158356667907864272493 6858434383750465449102185)
      ·
        refine ⟨5143825787812849086826639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6858434383750465449102185 5143825787812849086826639)
        ·
          refine ⟨7715738681719273630239959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5143825787812849086826639 7715738681719273630239959)
          ·
            refine ⟨11573608022578910445359939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7715738681719273630239959 11573608022578910445359939)
            ·
              refine ⟨17360412033868365668039909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11573608022578910445359939 17360412033868365668039909)
              ·
                refine ⟨3255077256350318562757483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17360412033868365668039909 3255077256350318562757483)
                ·
                  refine ⟨4882615884525477844136225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255077256350318562757483 4882615884525477844136225)
                  ·
                    refine ⟨3661961913394108383102169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4882615884525477844136225 3661961913394108383102169)
                    ·
                      refine ⟨2746471435045581287326627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3661961913394108383102169 2746471435045581287326627)
                      ·
                        rfl

theorem cell23_5348734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5348734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348734 prefixEnd_5348734 := by exact prefixLift 5348734
  have htrace : WordTrace (prefixWord ++ tailWord_5348734) baseStart_5348734 baseEnd_5348734 := by
    simpa [prefixWord, tailWord_5348734, baseEnd_5348734] using wordTrace_append hprefix tailTrace_5348734
  have hstable : (prefixWord ++ tailWord_5348734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348734).length < 2 ^ (prefixWord ++ tailWord_5348734).sum := by decide
  have hdescent : baseEnd_5348734 < baseStart_5348734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348772 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_5348772 : Nat := 118140960795 + 5348772 * 2 ^ 59
def prefixEnd_5348772 : Nat := 4983230072969 + 3 ^ 40 * 5348772 * 2
def baseEnd_5348772 : Nat := 2746490947310452138651451

theorem tailTrace_5348772 : CollatzResearch.WordTrace tailWord_5348772 prefixEnd_5348772 2746490947310452138651451 := by
  unfold tailWord_5348772
  simp only [CollatzResearch.WordTrace]
  refine ⟨97542870889160008187728285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130057161185546677583637713 97542870889160008187728285)
  ·
    refine ⟨36578576583435003070398107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97542870889160008187728285 36578576583435003070398107)
    ·
      refine ⟨54867864875152504605597161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36578576583435003070398107 54867864875152504605597161)
      ·
        refine ⟨41150898656364378454197871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54867864875152504605597161 41150898656364378454197871)
        ·
          refine ⟨61726347984546567681296807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41150898656364378454197871 61726347984546567681296807)
          ·
            refine ⟨92589521976819851521945211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61726347984546567681296807 92589521976819851521945211)
            ·
              refine ⟨138884282965229777282917817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92589521976819851521945211 138884282965229777282917817)
              ·
                refine ⟨104163212223922332962188363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138884282965229777282917817 104163212223922332962188363)
                ·
                  refine ⟨156244818335883499443282545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104163212223922332962188363 156244818335883499443282545)
                  ·
                    refine ⟨117183613751912624582461909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 156244818335883499443282545 117183613751912624582461909)
                    ·
                      refine ⟨2746490947310452138651451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 117183613751912624582461909 2746490947310452138651451)
                      ·
                        rfl

theorem cell23_5348772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_5348772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348772 prefixEnd_5348772 := by exact prefixLift 5348772
  have htrace : WordTrace (prefixWord ++ tailWord_5348772) baseStart_5348772 baseEnd_5348772 := by
    simpa [prefixWord, tailWord_5348772, baseEnd_5348772] using wordTrace_append hprefix tailTrace_5348772
  have hstable : (prefixWord ++ tailWord_5348772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348772).length < 2 ^ (prefixWord ++ tailWord_5348772).sum := by decide
  have hdescent : baseEnd_5348772 < baseStart_5348772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348796 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 7]
def baseStart_5348796 : Nat := 118140960795 + 5348796 * 2 ^ 59
def prefixEnd_5348796 : Nat := 4983230072969 + 3 ^ 40 * 5348796 * 2
def baseEnd_5348796 : Nat := 305167030094017782750149

theorem tailTrace_5348796 : CollatzResearch.WordTrace tailWord_5348796 prefixEnd_5348796 305167030094017782750149 := by
  unfold tailWord_5348796
  simp only [CollatzResearch.WordTrace]
  refine ⟨97543308565116534237165121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130057744753488712316220161 97543308565116534237165121)
  ·
    refine ⟨73157481423837400677873841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97543308565116534237165121 73157481423837400677873841)
    ·
      refine ⟨54868111067878050508405381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73157481423837400677873841 54868111067878050508405381)
      ·
        refine ⟨10287770825227134470326009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54868111067878050508405381 10287770825227134470326009)
        ·
          refine ⟨7715828118920350852744507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10287770825227134470326009 7715828118920350852744507)
          ·
            refine ⟨11573742178380526279116761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7715828118920350852744507 11573742178380526279116761)
            ·
              refine ⟨8680306633785394709337571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11573742178380526279116761 8680306633785394709337571)
              ·
                refine ⟨13020459950678092064006357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8680306633785394709337571 13020459950678092064006357)
                ·
                  refine ⟨305167030094017782750149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13020459950678092064006357 305167030094017782750149)
                  ·
                    rfl

theorem cell23_5348796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 7].length) (baseStart_5348796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348796 prefixEnd_5348796 := by exact prefixLift 5348796
  have htrace : WordTrace (prefixWord ++ tailWord_5348796) baseStart_5348796 baseEnd_5348796 := by
    simpa [prefixWord, tailWord_5348796, baseEnd_5348796] using wordTrace_append hprefix tailTrace_5348796
  have hstable : (prefixWord ++ tailWord_5348796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348796).length < 2 ^ (prefixWord ++ tailWord_5348796).sum := by decide
  have hdescent : baseEnd_5348796 < baseStart_5348796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348799 : List Nat := [1, 1, 2, 2, 2, 1, 1, 3, 1, 7, 2]
def baseStart_5348799 : Nat := 118140960795 + 5348799 * 2 ^ 59
def prefixEnd_5348799 : Nat := 4983230072969 + 3 ^ 40 * 5348799 * 2
def baseEnd_5348799 : Nat := 2746504811288123533013827

theorem tailTrace_5348799 : CollatzResearch.WordTrace tailWord_5348799 prefixEnd_5348799 2746504811288123533013827 := by
  unfold tailWord_5348799
  simp only [CollatzResearch.WordTrace]
  refine ⟨195086726549222199986689451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130057817699481466657792967 195086726549222199986689451)
  ·
    refine ⟨292630089823833299980034177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195086726549222199986689451 292630089823833299980034177)
    ·
      refine ⟨219472567367874974985025633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292630089823833299980034177 219472567367874974985025633)
      ·
        refine ⟨164604425525906231238769225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219472567367874974985025633 164604425525906231238769225)
        ·
          refine ⟨123453319144429673429076919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164604425525906231238769225 123453319144429673429076919)
          ·
            refine ⟨185179978716644510143615379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123453319144429673429076919 185179978716644510143615379)
            ·
              refine ⟨277769968074966765215423069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185179978716644510143615379 277769968074966765215423069)
              ·
                refine ⟨104163738028112536955783651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 277769968074966765215423069 104163738028112536955783651)
                ·
                  refine ⟨156245607042168805433675477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104163738028112536955783651 156245607042168805433675477)
                  ·
                    refine ⟨3662006415050831377351769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 156245607042168805433675477 3662006415050831377351769)
                    ·
                      refine ⟨2746504811288123533013827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662006415050831377351769 2746504811288123533013827)
                      ·
                        rfl

theorem cell23_5348799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 7, 2].length) (baseStart_5348799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348799 prefixEnd_5348799 := by exact prefixLift 5348799
  have htrace : WordTrace (prefixWord ++ tailWord_5348799) baseStart_5348799 baseEnd_5348799 := by
    simpa [prefixWord, tailWord_5348799, baseEnd_5348799] using wordTrace_append hprefix tailTrace_5348799
  have hstable : (prefixWord ++ tailWord_5348799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348799).length < 2 ^ (prefixWord ++ tailWord_5348799).sum := by decide
  have hdescent : baseEnd_5348799 < baseStart_5348799 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348846 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_5348846 : Nat := 118140960795 + 5348846 * 2 ^ 59
def prefixEnd_5348846 : Nat := 4983230072969 + 3 ^ 40 * 5348846 * 2
def baseEnd_5348846 : Nat := 2746528944878884849126111

theorem tailTrace_5348846 : CollatzResearch.WordTrace tailWord_5348846 prefixEnd_5348846 2746528944878884849126111 := by
  unfold tailWord_5348846
  simp only [CollatzResearch.WordTrace]
  refine ⟨24386055097506490876706299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130058960520034618009100261 24386055097506490876706299)
  ·
    refine ⟨36579082646259736315059449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24386055097506490876706299 36579082646259736315059449)
    ·
      refine ⟨27434311984694802236294587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36579082646259736315059449 27434311984694802236294587)
      ·
        refine ⟨41151467977042203354441881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27434311984694802236294587 41151467977042203354441881)
        ·
          refine ⟨30863600982781652515831411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41151467977042203354441881 30863600982781652515831411)
          ·
            refine ⟨46295401474172478773747117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30863600982781652515831411 46295401474172478773747117)
            ·
              refine ⟨17360775552814679540155169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46295401474172478773747117 17360775552814679540155169)
              ·
                refine ⟨13020581664611009655116377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17360775552814679540155169 13020581664611009655116377)
                ·
                  refine ⟨9765436248458257241337283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13020581664611009655116377 9765436248458257241337283)
                  ·
                    refine ⟨14648154372687385862005925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9765436248458257241337283 14648154372687385862005925)
                    ·
                      refine ⟨2746528944878884849126111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14648154372687385862005925 2746528944878884849126111)
                      ·
                        rfl

theorem cell23_5348846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_5348846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348846 prefixEnd_5348846 := by exact prefixLift 5348846
  have htrace : WordTrace (prefixWord ++ tailWord_5348846) baseStart_5348846 baseEnd_5348846 := by
    simpa [prefixWord, tailWord_5348846, baseEnd_5348846] using wordTrace_append hprefix tailTrace_5348846
  have hstable : (prefixWord ++ tailWord_5348846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348846).length < 2 ^ (prefixWord ++ tailWord_5348846).sum := by decide
  have hdescent : baseEnd_5348846 < baseStart_5348846 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348856 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 3, 4]
def baseStart_5348856 : Nat := 118140960795 + 5348856 * 2 ^ 59
def prefixEnd_5348856 : Nat := 4983230072969 + 3 ^ 40 * 5348856 * 2
def baseEnd_5348856 : Nat := 915511359895143270000355

theorem tailTrace_5348856 : CollatzResearch.WordTrace tailWord_5348856 prefixEnd_5348856 915511359895143270000355 := by
  unfold tailWord_5348856
  simp only [CollatzResearch.WordTrace]
  refine ⟨97544402755007849360757211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130059203673343799147676281 97544402755007849360757211)
  ·
    refine ⟨146316604132511774041135817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97544402755007849360757211 146316604132511774041135817)
    ·
      refine ⟨109737453099383830530851863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146316604132511774041135817 109737453099383830530851863)
      ·
        refine ⟨164606179649075745796277795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109737453099383830530851863 164606179649075745796277795)
        ·
          refine ⟨246909269473613618694416693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164606179649075745796277795 246909269473613618694416693)
          ·
            refine ⟨23147744013151276752601565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 246909269473613618694416693 23147744013151276752601565)
            ·
              refine ⟨8680404004931728782225587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23147744013151276752601565 8680404004931728782225587)
              ·
                refine ⟨13020606007397593173338381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8680404004931728782225587 13020606007397593173338381)
                ·
                  refine ⟨4882727252774097440001893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13020606007397593173338381 4882727252774097440001893)
                  ·
                    refine ⟨915511359895143270000355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4882727252774097440001893 915511359895143270000355)
                    ·
                      rfl

theorem cell23_5348856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_5348856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348856 prefixEnd_5348856 := by exact prefixLift 5348856
  have htrace : WordTrace (prefixWord ++ tailWord_5348856) baseStart_5348856 baseEnd_5348856 := by
    simpa [prefixWord, tailWord_5348856, baseEnd_5348856] using wordTrace_append hprefix tailTrace_5348856
  have hstable : (prefixWord ++ tailWord_5348856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348856).length < 2 ^ (prefixWord ++ tailWord_5348856).sum := by decide
  have hdescent : baseEnd_5348856 < baseStart_5348856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348934 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3]
def baseStart_5348934 : Nat := 118140960795 + 5348934 * 2 ^ 59
def prefixEnd_5348934 : Nat := 4983230072969 + 3 ^ 40 * 5348934 * 2
def baseEnd_5348934 : Nat := 2746574131176480504825707

theorem tailTrace_5348934 : CollatzResearch.WordTrace tailWord_5348934 prefixEnd_5348934 2746574131176480504825707 := by
  unfold tailWord_5348934
  simp only [CollatzResearch.WordTrace]
  refine ⟨6096614075116659938839183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 130061100269155412028569237 6096614075116659938839183)
  ·
    refine ⟨9144921112674989908258775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6096614075116659938839183 9144921112674989908258775)
    ·
      refine ⟨13717381669012484862388163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9144921112674989908258775 13717381669012484862388163)
      ·
        refine ⟨20576072503518727293582245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13717381669012484862388163 20576072503518727293582245)
        ·
          refine ⟨3858013594409761367546671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20576072503518727293582245 3858013594409761367546671)
          ·
            refine ⟨5787020391614642051320007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3858013594409761367546671 5787020391614642051320007)
            ·
              refine ⟨8680530587421963076980011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5787020391614642051320007 8680530587421963076980011)
              ·
                refine ⟨13020795881132944615470017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8680530587421963076980011 13020795881132944615470017)
                ·
                  refine ⟨9765596910849708461602513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13020795881132944615470017 9765596910849708461602513)
                  ·
                    refine ⟨7324197683137281346201885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9765596910849708461602513 7324197683137281346201885)
                    ·
                      refine ⟨2746574131176480504825707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7324197683137281346201885 2746574131176480504825707)
                      ·
                        rfl

theorem cell23_5348934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_5348934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348934 prefixEnd_5348934 := by exact prefixLift 5348934
  have htrace : WordTrace (prefixWord ++ tailWord_5348934) baseStart_5348934 baseEnd_5348934 := by
    simpa [prefixWord, tailWord_5348934, baseEnd_5348934] using wordTrace_append hprefix tailTrace_5348934
  have hstable : (prefixWord ++ tailWord_5348934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348934).length < 2 ^ (prefixWord ++ tailWord_5348934).sum := by decide
  have hdescent : baseEnd_5348934 < baseStart_5348934 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348940 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 2, 3, 2]
def baseStart_5348940 : Nat := 118140960795 + 5348940 * 2 ^ 59
def prefixEnd_5348940 : Nat := 4983230072969 + 3 ^ 40 * 5348940 * 2
def baseEnd_5348940 : Nat := 2746577212060407481350679

theorem tailTrace_5348940 : CollatzResearch.WordTrace tailWord_5348940 prefixEnd_5348940 2746577212060407481350679 := by
  unfold tailWord_5348940
  simp only [CollatzResearch.WordTrace]
  refine ⟨97545934620855690533786137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130061246161140920711714849 97545934620855690533786137)
  ·
    refine ⟨73159450965641767900339603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97545934620855690533786137 73159450965641767900339603)
    ·
      refine ⟨109739176448462651850509405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73159450965641767900339603 109739176448462651850509405)
      ·
        refine ⟨41152191168173494443941027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109739176448462651850509405 41152191168173494443941027)
        ·
          refine ⟨61728286752260241665911541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41152191168173494443941027 61728286752260241665911541)
          ·
            refine ⟨5787026883024397656179207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 61728286752260241665911541 5787026883024397656179207)
            ·
              refine ⟨8680540324536596484268811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5787026883024397656179207 8680540324536596484268811)
              ·
                refine ⟨13020810486804894726403217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8680540324536596484268811 13020810486804894726403217)
                ·
                  refine ⟨9765607865103671044802413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13020810486804894726403217 9765607865103671044802413)
                  ·
                    refine ⟨3662102949413876641800905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9765607865103671044802413 3662102949413876641800905)
                    ·
                      refine ⟨2746577212060407481350679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662102949413876641800905 2746577212060407481350679)
                      ·
                        rfl

theorem cell23_5348940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_5348940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348940 prefixEnd_5348940 := by exact prefixLift 5348940
  have htrace : WordTrace (prefixWord ++ tailWord_5348940) baseStart_5348940 baseEnd_5348940 := by
    simpa [prefixWord, tailWord_5348940, baseEnd_5348940] using wordTrace_append hprefix tailTrace_5348940
  have hstable : (prefixWord ++ tailWord_5348940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348940).length < 2 ^ (prefixWord ++ tailWord_5348940).sum := by decide
  have hdescent : baseEnd_5348940 < baseStart_5348940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348946 : List Nat := [3, 2, 2, 1, 2, 2, 2, 2, 1, 6]
def baseStart_5348946 : Nat := 118140960795 + 5348946 * 2 ^ 59
def prefixEnd_5348946 : Nat := 4983230072969 + 3 ^ 40 * 5348946 * 2
def baseEnd_5348946 : Nat := 915526764314778152625217

theorem tailTrace_5348946 : CollatzResearch.WordTrace tailWord_5348946 prefixEnd_5348946 915526764314778152625217 := by
  unfold tailWord_5348946
  simp only [CollatzResearch.WordTrace]
  refine ⟨48773022019922411023072673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130061392053126429394860461 48773022019922411023072673)
  ·
    refine ⟨36579766514941808267304505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48773022019922411023072673 36579766514941808267304505)
    ·
      refine ⟨27434824886206356200478379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36579766514941808267304505 27434824886206356200478379)
      ·
        refine ⟨41152237329309534300717569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27434824886206356200478379 41152237329309534300717569)
        ·
          refine ⟨30864177996982150725538177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41152237329309534300717569 30864177996982150725538177)
          ·
            refine ⟨23148133497736613044153633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30864177996982150725538177 23148133497736613044153633)
            ·
              refine ⟨17361100123302459783115225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23148133497736613044153633 17361100123302459783115225)
              ·
                refine ⟨13020825092476844837336419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17361100123302459783115225 13020825092476844837336419)
                ·
                  refine ⟨19531237638715267256004629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13020825092476844837336419 19531237638715267256004629)
                  ·
                    refine ⟨915526764314778152625217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19531237638715267256004629 915526764314778152625217)
                    ·
                      rfl

theorem cell23_5348946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_5348946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348946 prefixEnd_5348946 := by exact prefixLift 5348946
  have htrace : WordTrace (prefixWord ++ tailWord_5348946) baseStart_5348946 baseEnd_5348946 := by
    simpa [prefixWord, tailWord_5348946, baseEnd_5348946] using wordTrace_append hprefix tailTrace_5348946
  have hstable : (prefixWord ++ tailWord_5348946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348946).length < 2 ^ (prefixWord ++ tailWord_5348946).sum := by decide
  have hdescent : baseEnd_5348946 < baseStart_5348946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348949 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_5348949 : Nat := 118140960795 + 5348949 * 2 ^ 59
def prefixEnd_5348949 : Nat := 4983230072969 + 3 ^ 40 * 5348949 * 2
def baseEnd_5348949 : Nat := 2746581833386297946138137

theorem tailTrace_5348949 : CollatzResearch.WordTrace tailWord_5348949 prefixEnd_5348949 2746581833386297946138137 := by
  unfold tailWord_5348949
  simp only [CollatzResearch.WordTrace]
  refine ⟨195092197498678775604649901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130061464999119183736433267 195092197498678775604649901)
  ·
    refine ⟨73159574062004540851743713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195092197498678775604649901 73159574062004540851743713)
    ·
      refine ⟨54869680546503405638807785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73159574062004540851743713 54869680546503405638807785)
      ·
        refine ⟨41152260409877554229105839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54869680546503405638807785 41152260409877554229105839)
        ·
          refine ⟨61728390614816331343658759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41152260409877554229105839 61728390614816331343658759)
          ·
            refine ⟨92592585922224497015488139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61728390614816331343658759 92592585922224497015488139)
            ·
              refine ⟨138888878883336745523232209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92592585922224497015488139 138888878883336745523232209)
              ·
                refine ⟨104166659162502559142424157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138888878883336745523232209 104166659162502559142424157)
                ·
                  refine ⟨39062497185938459678409059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104166659162502559142424157 39062497185938459678409059)
                  ·
                    refine ⟨58593745778907689517613589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39062497185938459678409059 58593745778907689517613589)
                    ·
                      refine ⟨2746581833386297946138137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 58593745778907689517613589 2746581833386297946138137)
                      ·
                        rfl

theorem cell23_5348949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_5348949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348949 prefixEnd_5348949 := by exact prefixLift 5348949
  have htrace : WordTrace (prefixWord ++ tailWord_5348949) baseStart_5348949 baseEnd_5348949 := by
    simpa [prefixWord, tailWord_5348949, baseEnd_5348949] using wordTrace_append hprefix tailTrace_5348949
  have hstable : (prefixWord ++ tailWord_5348949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348949).length < 2 ^ (prefixWord ++ tailWord_5348949).sum := by decide
  have hdescent : baseEnd_5348949 < baseStart_5348949 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348963 : List Nat := [1, 1, 1, 5, 1, 3, 3, 2, 2, 4]
def baseStart_5348963 : Nat := 118140960795 + 5348963 * 2 ^ 59
def prefixEnd_5348963 : Nat := 4983230072969 + 3 ^ 40 * 5348963 * 2
def baseEnd_5348963 : Nat := 915529674038486963787691

theorem tailTrace_5348963 : CollatzResearch.WordTrace tailWord_5348963 prefixEnd_5348963 915529674038486963787691 := by
  unfold tailWord_5348963
  simp only [CollatzResearch.WordTrace]
  refine ⟨195092708120628055995659543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130061805413752037330439695 195092708120628055995659543)
  ·
    refine ⟨292639062180942083993489315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195092708120628055995659543 292639062180942083993489315)
    ·
      refine ⟨438958593271413125990233973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292639062180942083993489315 438958593271413125990233973)
      ·
        refine ⟨41152368119194980561584435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 438958593271413125990233973 41152368119194980561584435)
        ·
          refine ⟨61728552178792470842376653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41152368119194980561584435 61728552178792470842376653)
          ·
            refine ⟨23148207067047176565891245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61728552178792470842376653 23148207067047176565891245)
            ·
              refine ⟨8680577650142691212209217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23148207067047176565891245 8680577650142691212209217)
              ·
                refine ⟨6510433237607018409156913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8680577650142691212209217 6510433237607018409156913)
                ·
                  refine ⟨4882824928205263806867685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6510433237607018409156913 4882824928205263806867685)
                  ·
                    refine ⟨915529674038486963787691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4882824928205263806867685 915529674038486963787691)
                    ·
                      rfl

theorem cell23_5348963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 2, 4].length) (baseStart_5348963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348963 prefixEnd_5348963 := by exact prefixLift 5348963
  have htrace : WordTrace (prefixWord ++ tailWord_5348963) baseStart_5348963 baseEnd_5348963 := by
    simpa [prefixWord, tailWord_5348963, baseEnd_5348963] using wordTrace_append hprefix tailTrace_5348963
  have hstable : (prefixWord ++ tailWord_5348963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348963).length < 2 ^ (prefixWord ++ tailWord_5348963).sum := by decide
  have hdescent : baseEnd_5348963 < baseStart_5348963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348970 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 3, 2, 2]
def baseStart_5348970 : Nat := 118140960795 + 5348970 * 2 ^ 59
def prefixEnd_5348970 : Nat := 4983230072969 + 3 ^ 40 * 5348970 * 2
def baseEnd_5348970 : Nat := 2746592616480042363975541

theorem tailTrace_5348970 : CollatzResearch.WordTrace tailWord_5348970 prefixEnd_5348970 2746592616480042363975541 := by
  unfold tailWord_5348970
  simp only [CollatzResearch.WordTrace]
  refine ⟨48773240857900674047791091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130061975621068464127442909 48773240857900674047791091)
  ·
    refine ⟨73159861286851011071686637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48773240857900674047791091 73159861286851011071686637)
    ·
      refine ⟨27434947982569129151882489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73159861286851011071686637 27434947982569129151882489)
      ·
        refine ⟨20576210986926846863911867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27434947982569129151882489 20576210986926846863911867)
        ·
          refine ⟨30864316480390270295867801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20576210986926846863911867 30864316480390270295867801)
          ·
            refine ⟨23148237360292702721900851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30864316480390270295867801 23148237360292702721900851)
            ·
              refine ⟨34722356040439054082851277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23148237360292702721900851 34722356040439054082851277)
              ·
                refine ⟨13020883515164645281069229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34722356040439054082851277 13020883515164645281069229)
                ·
                  refine ⟨4882831318186741980400961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13020883515164645281069229 4882831318186741980400961)
                  ·
                    refine ⟨3662123488640056485300721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4882831318186741980400961 3662123488640056485300721)
                    ·
                      refine ⟨2746592616480042363975541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662123488640056485300721 2746592616480042363975541)
                      ·
                        rfl

theorem cell23_5348970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_5348970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348970 prefixEnd_5348970 := by exact prefixLift 5348970
  have htrace : WordTrace (prefixWord ++ tailWord_5348970) baseStart_5348970 baseEnd_5348970 := by
    simpa [prefixWord, tailWord_5348970, baseEnd_5348970] using wordTrace_append hprefix tailTrace_5348970
  have hstable : (prefixWord ++ tailWord_5348970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348970).length < 2 ^ (prefixWord ++ tailWord_5348970).sum := by decide
  have hdescent : baseEnd_5348970 < baseStart_5348970 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348973 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_5348973 : Nat := 118140960795 + 5348973 * 2 ^ 59
def prefixEnd_5348973 : Nat := 4983230072969 + 3 ^ 40 * 5348973 * 2
def baseEnd_5348973 : Nat := 2746594156922005852238027

theorem tailTrace_5348973 : CollatzResearch.WordTrace tailWord_5348973 prefixEnd_5348973 2746594156922005852238027 := by
  unfold tailWord_5348973
  simp only [CollatzResearch.WordTrace]
  refine ⟨195093072850591827703523573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130062048567061218469015715 195093072850591827703523573)
  ·
    refine ⟨18289975579742983847205335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195093072850591827703523573 18289975579742983847205335)
    ·
      refine ⟨27434963369614475770808003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18289975579742983847205335 27434963369614475770808003)
      ·
        refine ⟨41152445054421713656212005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27434963369614475770808003 41152445054421713656212005)
        ·
          refine ⟨7716083447704071310539751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41152445054421713656212005 7716083447704071310539751)
          ·
            refine ⟨11574125171556106965809627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7716083447704071310539751 11574125171556106965809627)
            ·
              refine ⟨17361187757334160448714441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11574125171556106965809627 17361187757334160448714441)
              ·
                refine ⟨13020890818000620336535831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17361187757334160448714441 13020890818000620336535831)
                ·
                  refine ⟨19531336227000930504803747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13020890818000620336535831 19531336227000930504803747)
                  ·
                    refine ⟨29297004340501395757205621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19531336227000930504803747 29297004340501395757205621)
                    ·
                      refine ⟨2746594156922005852238027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29297004340501395757205621 2746594156922005852238027)
                      ·
                        rfl

theorem cell23_5348973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_5348973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348973 prefixEnd_5348973 := by exact prefixLift 5348973
  have htrace : WordTrace (prefixWord ++ tailWord_5348973) baseStart_5348973 baseEnd_5348973 := by
    simpa [prefixWord, tailWord_5348973, baseEnd_5348973] using wordTrace_append hprefix tailTrace_5348973
  have hstable : (prefixWord ++ tailWord_5348973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348973).length < 2 ^ (prefixWord ++ tailWord_5348973).sum := by decide
  have hdescent : baseEnd_5348973 < baseStart_5348973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348986 : List Nat := [3, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3]
def baseStart_5348986 : Nat := 118140960795 + 5348986 * 2 ^ 59
def prefixEnd_5348986 : Nat := 4983230072969 + 3 ^ 40 * 5348986 * 2
def baseEnd_5348986 : Nat := 2746600832170514301375467

theorem tailTrace_5348986 : CollatzResearch.WordTrace tailWord_5348986 prefixEnd_5348986 2746600832170514301375467 := by
  unfold tailWord_5348986
  simp only [CollatzResearch.WordTrace]
  refine ⟨48773386749886182730936703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130062364666363153949164541 48773386749886182730936703)
  ·
    refine ⟨73160080124829274096405055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48773386749886182730936703 73160080124829274096405055)
    ·
      refine ⟨109740120187243911144607583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73160080124829274096405055 109740120187243911144607583)
      ·
        refine ⟨164610180280865866716911375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109740120187243911144607583 164610180280865866716911375)
        ·
          refine ⟨246915270421298800075367063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164610180280865866716911375 246915270421298800075367063)
          ·
            refine ⟨370372905631948200113050595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246915270421298800075367063 370372905631948200113050595)
            ·
              refine ⟨555559358447922300169575893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370372905631948200113050595 555559358447922300169575893)
              ·
                refine ⟨13020922463623178910224435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 555559358447922300169575893 13020922463623178910224435)
                ·
                  refine ⟨19531383695434768365336653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13020922463623178910224435 19531383695434768365336653)
                  ·
                    refine ⟨7324268885788038137001245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19531383695434768365336653 7324268885788038137001245)
                    ·
                      refine ⟨2746600832170514301375467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7324268885788038137001245 2746600832170514301375467)
                      ·
                        rfl

theorem cell23_5348986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 7, 1, 3, 3].length) (baseStart_5348986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348986 prefixEnd_5348986 := by exact prefixLift 5348986
  have htrace : WordTrace (prefixWord ++ tailWord_5348986) baseStart_5348986 baseEnd_5348986 := by
    simpa [prefixWord, tailWord_5348986, baseEnd_5348986] using wordTrace_append hprefix tailTrace_5348986
  have hstable : (prefixWord ++ tailWord_5348986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348986).length < 2 ^ (prefixWord ++ tailWord_5348986).sum := by decide
  have hdescent : baseEnd_5348986 < baseStart_5348986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5348993 : List Nat := [1, 2, 4, 2, 1, 4, 2, 7]
def baseStart_5348993 : Nat := 118140960795 + 5348993 * 2 ^ 59
def prefixEnd_5348993 : Nat := 4983230072969 + 3 ^ 40 * 5348993 * 2
def baseEnd_5348993 : Nat := 101726089871670213851405

theorem tailTrace_5348993 : CollatzResearch.WordTrace tailWord_5348993 prefixEnd_5348993 101726089871670213851405 := by
  unfold tailWord_5348993
  simp only [CollatzResearch.WordTrace]
  refine ⟨195093802310519371119251633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130062534873679580746167755 195093802310519371119251633)
  ·
    refine ⟨146320351732889528339438725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195093802310519371119251633 146320351732889528339438725)
    ·
      refine ⟨27435065949916786563644761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 146320351732889528339438725 27435065949916786563644761)
      ·
        refine ⟨20576299462437589922733571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27435065949916786563644761 20576299462437589922733571)
        ·
          refine ⟨30864449193656384884100357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20576299462437589922733571 30864449193656384884100357)
          ·
            refine ⟨5787084223810572165768817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30864449193656384884100357 5787084223810572165768817)
            ·
              refine ⟨4340313167857929124326613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5787084223810572165768817 4340313167857929124326613)
              ·
                refine ⟨101726089871670213851405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4340313167857929124326613 101726089871670213851405)
                ·
                  rfl

theorem cell23_5348993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 2, 7].length) (baseStart_5348993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5348993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5348993 prefixEnd_5348993 := by exact prefixLift 5348993
  have htrace : WordTrace (prefixWord ++ tailWord_5348993) baseStart_5348993 baseEnd_5348993 := by
    simpa [prefixWord, tailWord_5348993, baseEnd_5348993] using wordTrace_append hprefix tailTrace_5348993
  have hstable : (prefixWord ++ tailWord_5348993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5348993).length < 2 ^ (prefixWord ++ tailWord_5348993).sum := by decide
  have hdescent : baseEnd_5348993 < baseStart_5348993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5348993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349043 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 1, 4, 2]
def baseStart_5349043 : Nat := 118140960795 + 5349043 * 2 ^ 59
def prefixEnd_5349043 : Nat := 4983230072969 + 3 ^ 40 * 5349043 * 2
def baseEnd_5349043 : Nat := 2746630100567820578362705

theorem tailTrace_5349043 : CollatzResearch.WordTrace tailWord_5349043 prefixEnd_5349043 2746630100567820578362705 := by
  unfold tailWord_5349043
  simp only [CollatzResearch.WordTrace]
  refine ⟨195095625960338229658571783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130063750640225486439047855 195095625960338229658571783)
  ·
    refine ⟨292643438940507344487857675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195095625960338229658571783 292643438940507344487857675)
    ·
      refine ⟨438965158410761016731786513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292643438940507344487857675 438965158410761016731786513)
      ·
        refine ⟨329223868808070762548839885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 438965158410761016731786513 329223868808070762548839885)
        ·
          refine ⟨123458950803026535955814957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 329223868808070762548839885 123458950803026535955814957)
          ·
            refine ⟨46297106551134950983430609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123458950803026535955814957 46297106551134950983430609)
            ·
              refine ⟨34722829913351213237572957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46297106551134950983430609 34722829913351213237572957)
              ·
                refine ⟨13021061217506704964089859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34722829913351213237572957 13021061217506704964089859)
                ·
                  refine ⟨19531591826260057446134789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13021061217506704964089859 19531591826260057446134789)
                  ·
                    refine ⟨3662173467423760771150273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19531591826260057446134789 3662173467423760771150273)
                    ·
                      refine ⟨2746630100567820578362705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662173467423760771150273 2746630100567820578362705)
                      ·
                        rfl

theorem cell23_5349043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 1, 4, 2].length) (baseStart_5349043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349043 prefixEnd_5349043 := by exact prefixLift 5349043
  have htrace : WordTrace (prefixWord ++ tailWord_5349043) baseStart_5349043 baseEnd_5349043 := by
    simpa [prefixWord, tailWord_5349043, baseEnd_5349043] using wordTrace_append hprefix tailTrace_5349043
  have hstable : (prefixWord ++ tailWord_5349043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349043).length < 2 ^ (prefixWord ++ tailWord_5349043).sum := by decide
  have hdescent : baseEnd_5349043 < baseStart_5349043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349047 : List Nat := [1, 1, 3, 1, 5, 3, 1, 2, 1, 3, 2]
def baseStart_5349047 : Nat := 118140960795 + 5349047 * 2 ^ 59
def prefixEnd_5349047 : Nat := 4983230072969 + 3 ^ 40 * 5349047 * 2
def baseEnd_5349047 : Nat := 2746632154490438562712687

theorem tailTrace_5349047 : CollatzResearch.WordTrace tailWord_5349047 prefixEnd_5349047 2746632154490438562712687 := by
  unfold tailWord_5349047
  simp only [CollatzResearch.WordTrace]
  refine ⟨195095771852323738341717395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130063847901549158894478263 195095771852323738341717395)
  ·
    refine ⟨292643657778485607512576093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195095771852323738341717395 292643657778485607512576093)
    ·
      refine ⟨109741371666932102817216035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292643657778485607512576093 109741371666932102817216035)
      ·
        refine ⟨164612057500398154225824053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109741371666932102817216035 164612057500398154225824053)
        ·
          refine ⟨15432380390662326958671005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 164612057500398154225824053 15432380390662326958671005)
          ·
            refine ⟨5787142646498372609501627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15432380390662326958671005 5787142646498372609501627)
            ·
              refine ⟨8680713969747558914252441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5787142646498372609501627 8680713969747558914252441)
              ·
                refine ⟨6510535477310669185689331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8680713969747558914252441 6510535477310669185689331)
                ·
                  refine ⟨9765803215966003778533997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6510535477310669185689331 9765803215966003778533997)
                  ·
                    refine ⟨3662176205987251416950249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9765803215966003778533997 3662176205987251416950249)
                    ·
                      refine ⟨2746632154490438562712687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662176205987251416950249 2746632154490438562712687)
                      ·
                        rfl

theorem cell23_5349047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 1, 3, 2].length) (baseStart_5349047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349047 prefixEnd_5349047 := by exact prefixLift 5349047
  have htrace : WordTrace (prefixWord ++ tailWord_5349047) baseStart_5349047 baseEnd_5349047 := by
    simpa [prefixWord, tailWord_5349047, baseEnd_5349047] using wordTrace_append hprefix tailTrace_5349047
  have hstable : (prefixWord ++ tailWord_5349047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349047).length < 2 ^ (prefixWord ++ tailWord_5349047).sum := by decide
  have hdescent : baseEnd_5349047 < baseStart_5349047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349060 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 1, 4, 2]
def baseStart_5349060 : Nat := 118140960795 + 5349060 * 2 ^ 59
def prefixEnd_5349060 : Nat := 4983230072969 + 3 ^ 40 * 5349060 * 2
def baseEnd_5349060 : Nat := 2746638829738947011850127

theorem tailTrace_5349060 : CollatzResearch.WordTrace tailWord_5349060 prefixEnd_5349060 2746638829738947011850127 := by
  unfold tailWord_5349060
  simp only [CollatzResearch.WordTrace]
  refine ⟨97548123000638320780970317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130064164000851094374627089 97548123000638320780970317)
  ·
    refine ⟨36580546125239370292863869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97548123000638320780970317 36580546125239370292863869)
    ·
      refine ⟨13717704796964763859823951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36580546125239370292863869 13717704796964763859823951)
      ·
        refine ⟨20576557195447145789735927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13717704796964763859823951 20576557195447145789735927)
        ·
          refine ⟨30864835793170718684603891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20576557195447145789735927 30864835793170718684603891)
          ·
            refine ⟨46297253689756078026905837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30864835793170718684603891 46297253689756078026905837)
            ·
              refine ⟨17361470133658529260089689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46297253689756078026905837 17361470133658529260089689)
              ·
                refine ⟨13021102600243896945067267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17361470133658529260089689 13021102600243896945067267)
                ·
                  refine ⟨19531653900365845417600901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13021102600243896945067267 19531653900365845417600901)
                  ·
                    refine ⟨3662185106318596015800169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19531653900365845417600901 3662185106318596015800169)
                    ·
                      refine ⟨2746638829738947011850127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662185106318596015800169 2746638829738947011850127)
                      ·
                        rfl

theorem cell23_5349060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_5349060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349060 prefixEnd_5349060 := by exact prefixLift 5349060
  have htrace : WordTrace (prefixWord ++ tailWord_5349060) baseStart_5349060 baseEnd_5349060 := by
    simpa [prefixWord, tailWord_5349060, baseEnd_5349060] using wordTrace_append hprefix tailTrace_5349060
  have hstable : (prefixWord ++ tailWord_5349060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349060).length < 2 ^ (prefixWord ++ tailWord_5349060).sum := by decide
  have hdescent : baseEnd_5349060 < baseStart_5349060 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349093 : List Nat := [1, 3, 1, 4, 1, 1, 3, 1, 2, 3, 3]
def baseStart_5349093 : Nat := 118140960795 + 5349093 * 2 ^ 59
def prefixEnd_5349093 : Nat := 4983230072969 + 3 ^ 40 * 5349093 * 2
def baseEnd_5349093 : Nat := 2746655774600545382737475

theorem tailTrace_5349093 : CollatzResearch.WordTrace tailWord_5349093 prefixEnd_5349093 2746655774600545382737475 := by
  unfold tailWord_5349093
  simp only [CollatzResearch.WordTrace]
  refine ⟨195097449610157088197891933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130064966406771392131927955 195097449610157088197891933)
  ·
    refine ⟨73161543603808908074209475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195097449610157088197891933 73161543603808908074209475)
    ·
      refine ⟨109742315405713362111314213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73161543603808908074209475 109742315405713362111314213)
      ·
        refine ⟨20576684138571255395871415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109742315405713362111314213 20576684138571255395871415)
        ·
          refine ⟨30865026207856883093807123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20576684138571255395871415 30865026207856883093807123)
          ·
            refine ⟨46297539311785324640710685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30865026207856883093807123 46297539311785324640710685)
            ·
              refine ⟨17361577241919496740266507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46297539311785324640710685 17361577241919496740266507)
              ·
                refine ⟨26042365862879245110399761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17361577241919496740266507 26042365862879245110399761)
                ·
                  refine ⟨19531774397159433832799821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26042365862879245110399761 19531774397159433832799821)
                  ·
                    refine ⟨7324415398934787687299933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19531774397159433832799821 7324415398934787687299933)
                    ·
                      refine ⟨2746655774600545382737475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7324415398934787687299933 2746655774600545382737475)
                      ·
                        rfl

theorem cell23_5349093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_5349093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349093 prefixEnd_5349093 := by exact prefixLift 5349093
  have htrace : WordTrace (prefixWord ++ tailWord_5349093) baseStart_5349093 baseEnd_5349093 := by
    simpa [prefixWord, tailWord_5349093, baseEnd_5349093] using wordTrace_append hprefix tailTrace_5349093
  have hstable : (prefixWord ++ tailWord_5349093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349093).length < 2 ^ (prefixWord ++ tailWord_5349093).sum := by decide
  have hdescent : baseEnd_5349093 < baseStart_5349093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349103 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 2, 5, 2]
def baseStart_5349103 : Nat := 118140960795 + 5349103 * 2 ^ 59
def prefixEnd_5349103 : Nat := 4983230072969 + 3 ^ 40 * 5349103 * 2
def baseEnd_5349103 : Nat := 2746660909407090343612429

theorem tailTrace_5349103 : CollatzResearch.WordTrace tailWord_5349103 prefixEnd_5349103 2746660909407090343612429 := by
  unfold tailWord_5349103
  simp only [CollatzResearch.WordTrace]
  refine ⟨195097814340120859905755963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130065209560080573270503975 195097814340120859905755963)
  ·
    refine ⟨292646721510181289858633945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195097814340120859905755963 292646721510181289858633945)
    ·
      refine ⟨219485041132635967393975459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292646721510181289858633945 219485041132635967393975459)
      ·
        refine ⟨329227561698953951090963189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219485041132635967393975459 329227561698953951090963189)
        ·
          refine ⟨30865083909276932914777799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 329227561698953951090963189 30865083909276932914777799)
          ·
            refine ⟨46297625863915399372166699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30865083909276932914777799 46297625863915399372166699)
            ·
              refine ⟨69446438795873099058250049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46297625863915399372166699 69446438795873099058250049)
              ·
                refine ⟨52084829096904824293687537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69446438795873099058250049 52084829096904824293687537)
                ·
                  refine ⟨39063621822678618220265653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52084829096904824293687537 39063621822678618220265653)
                  ·
                    refine ⟨3662214545876120458149905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39063621822678618220265653 3662214545876120458149905)
                    ·
                      refine ⟨2746660909407090343612429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662214545876120458149905 2746660909407090343612429)
                      ·
                        rfl

theorem cell23_5349103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 2, 5, 2].length) (baseStart_5349103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349103 prefixEnd_5349103 := by exact prefixLift 5349103
  have htrace : WordTrace (prefixWord ++ tailWord_5349103) baseStart_5349103 baseEnd_5349103 := by
    simpa [prefixWord, tailWord_5349103, baseEnd_5349103] using wordTrace_append hprefix tailTrace_5349103
  have hstable : (prefixWord ++ tailWord_5349103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349103).length < 2 ^ (prefixWord ++ tailWord_5349103).sum := by decide
  have hdescent : baseEnd_5349103 < baseStart_5349103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349153 : List Nat := [1, 2, 3, 2, 1, 3, 1, 2, 1, 4, 3]
def baseStart_5349153 : Nat := 118140960795 + 5349153 * 2 ^ 59
def prefixEnd_5349153 : Nat := 4983230072969 + 3 ^ 40 * 5349153 * 2
def baseEnd_5349153 : Nat := 2746686583439815147987199

theorem tailTrace_5349153 : CollatzResearch.WordTrace tailWord_5349153 prefixEnd_5349153 2746686583439815147987199 := by
  unfold tailWord_5349153
  simp only [CollatzResearch.WordTrace]
  refine ⟨195099637989939718445076113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130066425326626478963384075 195099637989939718445076113)
  ·
    refine ⟨146324728492454788833807085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195099637989939718445076113 146324728492454788833807085)
    ·
      refine ⟨54871773184670545812677657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146324728492454788833807085 54871773184670545812677657)
      ·
        refine ⟨41153829888502909359508243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54871773184670545812677657 41153829888502909359508243)
        ·
          refine ⟨61730744832754364039262365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41153829888502909359508243 61730744832754364039262365)
          ·
            refine ⟨23149029312282886514723387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61730744832754364039262365 23149029312282886514723387)
            ·
              refine ⟨34723543968424329772085081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23149029312282886514723387 34723543968424329772085081)
              ·
                refine ⟨26042657976318247329063811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34723543968424329772085081 26042657976318247329063811)
                ·
                  refine ⟨39063986964477370993595717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26042657976318247329063811 39063986964477370993595717)
                  ·
                    refine ⟨7324497555839507061299197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39063986964477370993595717 7324497555839507061299197)
                    ·
                      refine ⟨2746686583439815147987199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7324497555839507061299197 2746686583439815147987199)
                      ·
                        rfl

theorem cell23_5349153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_5349153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349153 prefixEnd_5349153 := by exact prefixLift 5349153
  have htrace : WordTrace (prefixWord ++ tailWord_5349153) baseStart_5349153 baseEnd_5349153 := by
    simpa [prefixWord, tailWord_5349153, baseEnd_5349153] using wordTrace_append hprefix tailTrace_5349153
  have hstable : (prefixWord ++ tailWord_5349153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349153).length < 2 ^ (prefixWord ++ tailWord_5349153).sum := by decide
  have hdescent : baseEnd_5349153 < baseStart_5349153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349160 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 3, 4]
def baseStart_5349160 : Nat := 118140960795 + 5349160 * 2 ^ 59
def prefixEnd_5349160 : Nat := 4983230072969 + 3 ^ 40 * 5349160 * 2
def baseEnd_5349160 : Nat := 915563392601465540199889

theorem tailTrace_5349160 : CollatzResearch.WordTrace tailWord_5349160 prefixEnd_5349160 915563392601465540199889 := by
  unfold tailWord_5349160
  simp only [CollatzResearch.WordTrace]
  refine ⟨97549946650457179320290467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130066595533942905760387289 97549946650457179320290467)
  ·
    refine ⟨146324919975685768980435701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97549946650457179320290467 146324919975685768980435701)
    ·
      refine ⟨13717961247720540841915847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 146324919975685768980435701 13717961247720540841915847)
      ·
        refine ⟨20576941871580811262873771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13717961247720540841915847 20576941871580811262873771)
        ·
          refine ⟨30865412807371216894310657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20576941871580811262873771 30865412807371216894310657)
          ·
            refine ⟨23149059605528412670732993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30865412807371216894310657 23149059605528412670732993)
            ·
              refine ⟨17361794704146309503049745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23149059605528412670732993 17361794704146309503049745)
              ·
                refine ⟨13021346028109732127287309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17361794704146309503049745 13021346028109732127287309)
                ·
                  refine ⟨4883004760541149547732741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13021346028109732127287309 4883004760541149547732741)
                  ·
                    refine ⟨915563392601465540199889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4883004760541149547732741 915563392601465540199889)
                    ·
                      rfl

theorem cell23_5349160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_5349160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349160 prefixEnd_5349160 := by exact prefixLift 5349160
  have htrace : WordTrace (prefixWord ++ tailWord_5349160) baseStart_5349160 baseEnd_5349160 := by
    simpa [prefixWord, tailWord_5349160, baseEnd_5349160] using wordTrace_append hprefix tailTrace_5349160
  have hstable : (prefixWord ++ tailWord_5349160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349160).length < 2 ^ (prefixWord ++ tailWord_5349160).sum := by decide
  have hdescent : baseEnd_5349160 < baseStart_5349160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349207 : List Nat := [1, 1, 3, 2, 5, 2, 2, 1, 6]
def baseStart_5349207 : Nat := 118140960795 + 5349207 * 2 ^ 59
def prefixEnd_5349207 : Nat := 4983230072969 + 3 ^ 40 * 5349207 * 2
def baseEnd_5349207 : Nat := 305190479043906437412439

theorem tailTrace_5349207 : CollatzResearch.WordTrace tailWord_5349207 prefixEnd_5349207 305190479043906437412439 := by
  unfold tailWord_5349207
  simp only [CollatzResearch.WordTrace]
  refine ⟨195101607531744085667541875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130067738354496057111694583 195101607531744085667541875)
  ·
    refine ⟨292652411297616128501312813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195101607531744085667541875 292652411297616128501312813)
    ·
      refine ⟨109744654236606048187992305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292652411297616128501312813 109744654236606048187992305)
      ·
        refine ⟨82308490677454536140994229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109744654236606048187992305 82308490677454536140994229)
        ·
          refine ⟨7716421001011362763218209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82308490677454536140994229 7716421001011362763218209)
          ·
            refine ⟨5787315750758522072413657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7716421001011362763218209 5787315750758522072413657)
            ·
              refine ⟨4340486813068891554310243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5787315750758522072413657 4340486813068891554310243)
              ·
                refine ⟨6510730219603337331465365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4340486813068891554310243 6510730219603337331465365)
                ·
                  refine ⟨305190479043906437412439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6510730219603337331465365 305190479043906437412439)
                  ·
                    rfl

theorem cell23_5349207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 6].length) (baseStart_5349207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349207 prefixEnd_5349207 := by exact prefixLift 5349207
  have htrace : WordTrace (prefixWord ++ tailWord_5349207) baseStart_5349207 baseEnd_5349207 := by
    simpa [prefixWord, tailWord_5349207, baseEnd_5349207] using wordTrace_append hprefix tailTrace_5349207
  have hstable : (prefixWord ++ tailWord_5349207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349207).length < 2 ^ (prefixWord ++ tailWord_5349207).sum := by decide
  have hdescent : baseEnd_5349207 < baseStart_5349207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349210 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2]
def baseStart_5349210 : Nat := 118140960795 + 5349210 * 2 ^ 59
def prefixEnd_5349210 : Nat := 4983230072969 + 3 ^ 40 * 5349210 * 2
def baseEnd_5349210 : Nat := 2746715851837121424974437

theorem tailTrace_5349210 : CollatzResearch.WordTrace tailWord_5349210 prefixEnd_5349210 2746715851837121424974437 := by
  unfold tailWord_5349210
  simp only [CollatzResearch.WordTrace]
  refine ⟨48775429237683304294975271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130067811300488811453267389 48775429237683304294975271)
  ·
    refine ⟨73163143856524956442462907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48775429237683304294975271 73163143856524956442462907)
    ·
      refine ⟨109744715784787434663694361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73163143856524956442462907 109744715784787434663694361)
      ·
        refine ⟨82308536838590575997770771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109744715784787434663694361 82308536838590575997770771)
        ·
          refine ⟨123462805257885863996656157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82308536838590575997770771 123462805257885863996656157)
          ·
            refine ⟨46298551971707198998746059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123462805257885863996656157 46298551971707198998746059)
            ·
              refine ⟨69447827957560798498119089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46298551971707198998746059 69447827957560798498119089)
              ·
                refine ⟨52085870968170598873589317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69447827957560798498119089 52085870968170598873589317)
                ·
                  refine ⟨9766100806531987288797997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52085870968170598873589317 9766100806531987288797997)
                  ·
                    refine ⟨3662287802449495233299249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9766100806531987288797997 3662287802449495233299249)
                    ·
                      refine ⟨2746715851837121424974437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662287802449495233299249 2746715851837121424974437)
                      ·
                        rfl

theorem cell23_5349210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_5349210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349210 prefixEnd_5349210 := by exact prefixLift 5349210
  have htrace : WordTrace (prefixWord ++ tailWord_5349210) baseStart_5349210 baseEnd_5349210 := by
    simpa [prefixWord, tailWord_5349210, baseEnd_5349210] using wordTrace_append hprefix tailTrace_5349210
  have hstable : (prefixWord ++ tailWord_5349210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349210).length < 2 ^ (prefixWord ++ tailWord_5349210).sum := by decide
  have hdescent : baseEnd_5349210 < baseStart_5349210 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349220 : List Nat := [2, 3, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_5349220 : Nat := 118140960795 + 5349220 * 2 ^ 59
def prefixEnd_5349220 : Nat := 4983230072969 + 3 ^ 40 * 5349220 * 2
def baseEnd_5349220 : Nat := 915573662214555461949797

theorem tailTrace_5349220 : CollatzResearch.WordTrace tailWord_5349220 prefixEnd_5349220 915573662214555461949797 := by
  unfold tailWord_5349220
  simp only [CollatzResearch.WordTrace]
  refine ⟨97551040840348494443882557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130068054453797992591843409 97551040840348494443882557)
  ·
    refine ⟨36581640315130685416455959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97551040840348494443882557 36581640315130685416455959)
    ·
      refine ⟨54872460472696028124683939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36581640315130685416455959 54872460472696028124683939)
      ·
        refine ⟨82308690709044042187025909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54872460472696028124683939 82308690709044042187025909)
        ·
          refine ⟨7716439753972878955033679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 82308690709044042187025909 7716439753972878955033679)
          ·
            refine ⟨11574659630959318432550519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7716439753972878955033679 11574659630959318432550519)
            ·
              refine ⟨17361989446438977648825779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11574659630959318432550519 17361989446438977648825779)
              ·
                refine ⟨26042984169658466473238669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17361989446438977648825779 26042984169658466473238669)
                ·
                  refine ⟨9766119063621924927464501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26042984169658466473238669 9766119063621924927464501)
                  ·
                    refine ⟨915573662214555461949797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9766119063621924927464501 915573662214555461949797)
                    ·
                      rfl

theorem cell23_5349220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_5349220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349220 prefixEnd_5349220 := by exact prefixLift 5349220
  have htrace : WordTrace (prefixWord ++ tailWord_5349220) baseStart_5349220 baseEnd_5349220 := by
    simpa [prefixWord, tailWord_5349220, baseEnd_5349220] using wordTrace_append hprefix tailTrace_5349220
  have hstable : (prefixWord ++ tailWord_5349220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349220).length < 2 ^ (prefixWord ++ tailWord_5349220).sum := by decide
  have hdescent : baseEnd_5349220 < baseStart_5349220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349233 : List Nat := [1, 2, 2, 2, 1, 3, 3, 2, 1, 6]
def baseStart_5349233 : Nat := 118140960795 + 5349233 * 2 ^ 59
def prefixEnd_5349233 : Nat := 4983230072969 + 3 ^ 40 * 5349233 * 2
def baseEnd_5349233 : Nat := 915575887297391611662277

theorem tailTrace_5349233 : CollatzResearch.WordTrace tailWord_5349233 prefixEnd_5349233 915575887297391611662277 := by
  unfold tailWord_5349233
  simp only [CollatzResearch.WordTrace]
  refine ⟨195102555829649892107988353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130068370553099928071992235 195102555829649892107988353)
  ·
    refine ⟨146326916872237419080991265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195102555829649892107988353 146326916872237419080991265)
    ·
      refine ⟨109745187654178064310743449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146326916872237419080991265 109745187654178064310743449)
      ·
        refine ⟨82308890740633548233057587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109745187654178064310743449 82308890740633548233057587)
        ·
          refine ⟨123463336110950322349586381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82308890740633548233057587 123463336110950322349586381)
          ·
            refine ⟨46298751041606370881094893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123463336110950322349586381 46298751041606370881094893)
            ·
              refine ⟨17362031640602389080410585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46298751041606370881094893 17362031640602389080410585)
              ·
                refine ⟨13021523730451791810307939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17362031640602389080410585 13021523730451791810307939)
                ·
                  refine ⟨19532285595677687715461909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13021523730451791810307939 19532285595677687715461909)
                  ·
                    refine ⟨915575887297391611662277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19532285595677687715461909 915575887297391611662277)
                    ·
                      rfl

theorem cell23_5349233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 2, 1, 6].length) (baseStart_5349233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349233 prefixEnd_5349233 := by exact prefixLift 5349233
  have htrace : WordTrace (prefixWord ++ tailWord_5349233) baseStart_5349233 baseEnd_5349233 := by
    simpa [prefixWord, tailWord_5349233, baseEnd_5349233] using wordTrace_append hprefix tailTrace_5349233
  have hstable : (prefixWord ++ tailWord_5349233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349233).length < 2 ^ (prefixWord ++ tailWord_5349233).sum := by decide
  have hdescent : baseEnd_5349233 < baseStart_5349233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349237 : List Nat := [1, 3, 4, 1, 1, 1, 5, 1, 1, 5]
def baseStart_5349237 : Nat := 118140960795 + 5349237 * 2 ^ 59
def prefixEnd_5349237 : Nat := 4983230072969 + 3 ^ 40 * 5349237 * 2
def baseEnd_5349237 : Nat := 915576571938264273112271

theorem tailTrace_5349237 : CollatzResearch.WordTrace tailWord_5349237 prefixEnd_5349237 915576571938264273112271 := by
  unfold tailWord_5349237
  simp only [CollatzResearch.WordTrace]
  refine ⟨195102701721635400791133965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130068467814423600527422643 195102701721635400791133965)
  ·
    refine ⟨73163513145613275296675237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195102701721635400791133965 73163513145613275296675237)
    ·
      refine ⟨13718158714802489118126607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73163513145613275296675237 13718158714802489118126607)
      ·
        refine ⟨20577238072203733677189911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13718158714802489118126607 20577238072203733677189911)
        ·
          refine ⟨30865857108305600515784867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20577238072203733677189911 30865857108305600515784867)
          ·
            refine ⟨46298785662458400773677301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30865857108305600515784867 46298785662458400773677301)
            ·
              refine ⟨4340511155855475072532247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46298785662458400773677301 4340511155855475072532247)
              ·
                refine ⟨6510766733783212608798371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4340511155855475072532247 6510766733783212608798371)
                ·
                  refine ⟨9766150100674818913197557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6510766733783212608798371 9766150100674818913197557)
                  ·
                    refine ⟨915576571938264273112271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9766150100674818913197557 915576571938264273112271)
                    ·
                      rfl

theorem cell23_5349237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_5349237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349237 prefixEnd_5349237 := by exact prefixLift 5349237
  have htrace : WordTrace (prefixWord ++ tailWord_5349237) baseStart_5349237 baseEnd_5349237 := by
    simpa [prefixWord, tailWord_5349237, baseEnd_5349237] using wordTrace_append hprefix tailTrace_5349237
  have hstable : (prefixWord ++ tailWord_5349237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349237).length < 2 ^ (prefixWord ++ tailWord_5349237).sum := by decide
  have hdescent : baseEnd_5349237 < baseStart_5349237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349251 : List Nat := [1, 1, 1, 3, 4, 4, 2, 2, 1, 1, 3]
def baseStart_5349251 : Nat := 118140960795 + 5349251 * 2 ^ 59
def prefixEnd_5349251 : Nat := 4983230072969 + 3 ^ 40 * 5349251 * 2
def baseEnd_5349251 : Nat := 2746736904543955764561749

theorem tailTrace_5349251 : CollatzResearch.WordTrace tailWord_5349251 prefixEnd_5349251 2746736904543955764561749 := by
  unfold tailWord_5349251
  simp only [CollatzResearch.WordTrace]
  refine ⟨195103212343584681182143607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130068808229056454121429071 195103212343584681182143607)
  ·
    refine ⟨292654818515377021773215411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195103212343584681182143607 292654818515377021773215411)
    ·
      refine ⟨438982227773065532659823117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292654818515377021773215411 438982227773065532659823117)
      ·
        refine ⟨164618335414899574747433669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 438982227773065532659823117 164618335414899574747433669)
        ·
          refine ⟨30865937890293670265143813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164618335414899574747433669 30865937890293670265143813)
          ·
            refine ⟨5787363354430063174714465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30865937890293670265143813 5787363354430063174714465)
            ·
              refine ⟨4340522515822547381035849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5787363354430063174714465 4340522515822547381035849)
              ·
                refine ⟨3255391886866910535776887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4340522515822547381035849 3255391886866910535776887)
                ·
                  refine ⟨4883087830300365803665331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255391886866910535776887 4883087830300365803665331)
                  ·
                    refine ⟨7324631745450548705497997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4883087830300365803665331 7324631745450548705497997)
                    ·
                      refine ⟨2746736904543955764561749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7324631745450548705497997 2746736904543955764561749)
                      ·
                        rfl

theorem cell23_5349251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 2, 2, 1, 1, 3].length) (baseStart_5349251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349251 prefixEnd_5349251 := by exact prefixLift 5349251
  have htrace : WordTrace (prefixWord ++ tailWord_5349251) baseStart_5349251 baseEnd_5349251 := by
    simpa [prefixWord, tailWord_5349251, baseEnd_5349251] using wordTrace_append hprefix tailTrace_5349251
  have hstable : (prefixWord ++ tailWord_5349251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349251).length < 2 ^ (prefixWord ++ tailWord_5349251).sum := by decide
  have hdescent : baseEnd_5349251 < baseStart_5349251 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349253 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 3, 2, 4]
def baseStart_5349253 : Nat := 118140960795 + 5349253 * 2 ^ 59
def prefixEnd_5349253 : Nat := 4983230072969 + 3 ^ 40 * 5349253 * 2
def baseEnd_5349253 : Nat := 2746737931505264756736739

theorem tailTrace_5349253 : CollatzResearch.WordTrace tailWord_5349253 prefixEnd_5349253 2746737931505264756736739 := by
  unfold tailWord_5349253
  simp only [CollatzResearch.WordTrace]
  refine ⟨195103285289577435523716413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130068856859718290349144275 195103285289577435523716413)
  ·
    refine ⟨73163731983591538321393655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195103285289577435523716413 73163731983591538321393655)
    ·
      refine ⟨109745597975387307482090483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73163731983591538321393655 109745597975387307482090483)
      ·
        refine ⟨164618396963080961223135725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109745597975387307482090483 164618396963080961223135725)
        ·
          refine ⟨61731898861155360458675897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164618396963080961223135725 61731898861155360458675897)
          ·
            refine ⟨46298924145866520344006923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61731898861155360458675897 46298924145866520344006923)
            ·
              refine ⟨69448386218799780516010385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46298924145866520344006923 69448386218799780516010385)
              ·
                refine ⟨52086289664099835387007789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69448386218799780516010385 52086289664099835387007789)
                ·
                  refine ⟨19532358624037438270127921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52086289664099835387007789 19532358624037438270127921)
                  ·
                    refine ⟨14649268968028078702595941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19532358624037438270127921 14649268968028078702595941)
                    ·
                      refine ⟨2746737931505264756736739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14649268968028078702595941 2746737931505264756736739)
                      ·
                        rfl

theorem cell23_5349253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 2, 4].length) (baseStart_5349253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349253 prefixEnd_5349253 := by exact prefixLift 5349253
  have htrace : WordTrace (prefixWord ++ tailWord_5349253) baseStart_5349253 baseEnd_5349253 := by
    simpa [prefixWord, tailWord_5349253, baseEnd_5349253] using wordTrace_append hprefix tailTrace_5349253
  have hstable : (prefixWord ++ tailWord_5349253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349253).length < 2 ^ (prefixWord ++ tailWord_5349253).sum := by decide
  have hdescent : baseEnd_5349253 < baseStart_5349253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349257 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 3, 2, 2]
def baseStart_5349257 : Nat := 118140960795 + 5349257 * 2 ^ 59
def prefixEnd_5349257 : Nat := 4983230072969 + 3 ^ 40 * 5349257 * 2
def baseEnd_5349257 : Nat := 2746739985427882741086721

theorem tailTrace_5349257 : CollatzResearch.WordTrace tailWord_5349257 prefixEnd_5349257 2746739985427882741086721 := by
  unfold tailWord_5349257
  simp only [CollatzResearch.WordTrace]
  refine ⟨195103431181562944206862025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130068954121041962804574683 195103431181562944206862025)
  ·
    refine ⟨146327573386172208155146519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195103431181562944206862025 146327573386172208155146519)
    ·
      refine ⟨219491360079258312232719779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146327573386172208155146519 219491360079258312232719779)
      ·
        refine ⟨329237040118887468349079669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219491360079258312232719779 329237040118887468349079669)
        ·
          refine ⟨30865972511145700157726219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 329237040118887468349079669 30865972511145700157726219)
          ·
            refine ⟨46298958766718550236589329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30865972511145700157726219 46298958766718550236589329)
            ·
              refine ⟨34724219075038912677441997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46298958766718550236589329 34724219075038912677441997)
              ·
                refine ⟨13021582153139592254040749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34724219075038912677441997 13021582153139592254040749)
                ·
                  refine ⟨4883093307427347095265281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13021582153139592254040749 4883093307427347095265281)
                  ·
                    refine ⟨3662319980570510321448961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4883093307427347095265281 3662319980570510321448961)
                    ·
                      refine ⟨2746739985427882741086721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662319980570510321448961 2746739985427882741086721)
                      ·
                        rfl

theorem cell23_5349257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 3, 2, 2].length) (baseStart_5349257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349257 prefixEnd_5349257 := by exact prefixLift 5349257
  have htrace : WordTrace (prefixWord ++ tailWord_5349257) baseStart_5349257 baseEnd_5349257 := by
    simpa [prefixWord, tailWord_5349257, baseEnd_5349257] using wordTrace_append hprefix tailTrace_5349257
  have hstable : (prefixWord ++ tailWord_5349257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349257).length < 2 ^ (prefixWord ++ tailWord_5349257).sum := by decide
  have hdescent : baseEnd_5349257 < baseStart_5349257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349274 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2]
def baseStart_5349274 : Nat := 118140960795 + 5349274 * 2 ^ 59
def prefixEnd_5349274 : Nat := 4983230072969 + 3 ^ 40 * 5349274 * 2
def baseEnd_5349274 : Nat := 2746748714599009174574143

theorem tailTrace_5349274 : CollatzResearch.WordTrace tailWord_5349274 prefixEnd_5349274 2746748714599009174574143 := by
  unfold tailWord_5349274
  simp only [CollatzResearch.WordTrace]
  refine ⟨48776012805625339027557719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130069367481667570740153917 48776012805625339027557719)
  ·
    refine ⟨73164019208438008541336579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48776012805625339027557719 73164019208438008541336579)
    ·
      refine ⟨109746028812657012812004869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73164019208438008541336579 109746028812657012812004869)
      ·
        refine ⟨20577380402373189902250913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 109746028812657012812004869 20577380402373189902250913)
        ·
          refine ⟨15433035301779892426688185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20577380402373189902250913 15433035301779892426688185)
          ·
            refine ⟨11574776476334919320016139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15433035301779892426688185 11574776476334919320016139)
            ·
              refine ⟨17362164714502378980024209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11574776476334919320016139 17362164714502378980024209)
              ·
                refine ⟨13021623535876784235018157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17362164714502378980024209 13021623535876784235018157)
                ·
                  refine ⟨4883108825953794088131809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13021623535876784235018157 4883108825953794088131809)
                  ·
                    refine ⟨3662331619465345566098857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4883108825953794088131809 3662331619465345566098857)
                    ·
                      refine ⟨2746748714599009174574143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662331619465345566098857 2746748714599009174574143)
                      ·
                        rfl

theorem cell23_5349274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_5349274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349274 prefixEnd_5349274 := by exact prefixLift 5349274
  have htrace : WordTrace (prefixWord ++ tailWord_5349274) baseStart_5349274 baseEnd_5349274 := by
    simpa [prefixWord, tailWord_5349274, baseEnd_5349274] using wordTrace_append hprefix tailTrace_5349274
  have hstable : (prefixWord ++ tailWord_5349274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349274).length < 2 ^ (prefixWord ++ tailWord_5349274).sum := by decide
  have hdescent : baseEnd_5349274 < baseStart_5349274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349278 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 2, 3, 2]
def baseStart_5349278 : Nat := 118140960795 + 5349278 * 2 ^ 59
def prefixEnd_5349278 : Nat := 4983230072969 + 3 ^ 40 * 5349278 * 2
def baseEnd_5349278 : Nat := 2746750768521627158924125

theorem tailTrace_5349278 : CollatzResearch.WordTrace tailWord_5349278 prefixEnd_5349278 2746750768521627158924125 := by
  unfold tailWord_5349278
  simp only [CollatzResearch.WordTrace]
  refine ⟨24388024639310858099172061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130069464742991243195584325 24388024639310858099172061)
  ·
    refine ⟨9145509239741571787189523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24388024639310858099172061 9145509239741571787189523)
    ·
      refine ⟨13718263859612357680784285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9145509239741571787189523 13718263859612357680784285)
      ·
        refine ⟨5144348947354634130294107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13718263859612357680784285 5144348947354634130294107)
        ·
          refine ⟨7716523421031951195441161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5144348947354634130294107 7716523421031951195441161)
          ·
            refine ⟨5787392565773963396580871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7716523421031951195441161 5787392565773963396580871)
            ·
              refine ⟨8681088848660945094871307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5787392565773963396580871 8681088848660945094871307)
              ·
                refine ⟨13021633272991417642306961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8681088848660945094871307 13021633272991417642306961)
                ·
                  refine ⟨9766224954743563231730221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13021633272991417642306961 9766224954743563231730221)
                  ·
                    refine ⟨3662334358028836211898833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9766224954743563231730221 3662334358028836211898833)
                    ·
                      refine ⟨2746750768521627158924125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662334358028836211898833 2746750768521627158924125)
                      ·
                        rfl

theorem cell23_5349278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_5349278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349278 prefixEnd_5349278 := by exact prefixLift 5349278
  have htrace : WordTrace (prefixWord ++ tailWord_5349278) baseStart_5349278 baseEnd_5349278 := by
    simpa [prefixWord, tailWord_5349278, baseEnd_5349278] using wordTrace_append hprefix tailTrace_5349278
  have hstable : (prefixWord ++ tailWord_5349278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349278).length < 2 ^ (prefixWord ++ tailWord_5349278).sum := by decide
  have hdescent : baseEnd_5349278 < baseStart_5349278 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349288 : List Nat := [2, 1, 6, 2, 2, 1, 2, 1, 1, 5]
def baseStart_5349288 : Nat := 118140960795 + 5349288 * 2 ^ 59
def prefixEnd_5349288 : Nat := 4983230072969 + 3 ^ 40 * 5349288 * 2
def baseEnd_5349288 : Nat := 915585301109390706599693

theorem tailTrace_5349288 : CollatzResearch.WordTrace tailWord_5349288 prefixEnd_5349288 915585301109390706599693 := by
  unfold tailWord_5349288
  simp only [CollatzResearch.WordTrace]
  refine ⟨97552280922225318250620259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130069707896300424334160345 97552280922225318250620259)
  ·
    refine ⟨146328421383337977375930389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97552280922225318250620259 146328421383337977375930389)
    ·
      refine ⟨6859144752343967689496737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 146328421383337977375930389 6859144752343967689496737)
      ·
        refine ⟨5144358564257975767122553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6859144752343967689496737 5144358564257975767122553)
        ·
          refine ⟨3858268923193481825341915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5144358564257975767122553 3858268923193481825341915)
          ·
            refine ⟨5787403384790222738012873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3858268923193481825341915 5787403384790222738012873)
            ·
              refine ⟨4340552538592667053509655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5787403384790222738012873 4340552538592667053509655)
              ·
                refine ⟨6510828807889000580264483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4340552538592667053509655 6510828807889000580264483)
                ·
                  refine ⟨9766243211833500870396725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6510828807889000580264483 9766243211833500870396725)
                  ·
                    refine ⟨915585301109390706599693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9766243211833500870396725 915585301109390706599693)
                    ·
                      rfl

theorem cell23_5349288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_5349288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349288 prefixEnd_5349288 := by exact prefixLift 5349288
  have htrace : WordTrace (prefixWord ++ tailWord_5349288) baseStart_5349288 baseEnd_5349288 := by
    simpa [prefixWord, tailWord_5349288, baseEnd_5349288] using wordTrace_append hprefix tailTrace_5349288
  have hstable : (prefixWord ++ tailWord_5349288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349288).length < 2 ^ (prefixWord ++ tailWord_5349288).sum := by decide
  have hdescent : baseEnd_5349288 < baseStart_5349288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349323 : List Nat := [1, 1, 1, 1, 3, 4, 1, 3, 2, 6]
def baseStart_5349323 : Nat := 118140960795 + 5349323 * 2 ^ 59
def prefixEnd_5349323 : Nat := 4983230072969 + 3 ^ 40 * 5349323 * 2
def baseEnd_5349323 : Nat := 915591291717026494287139

theorem tailTrace_5349323 : CollatzResearch.WordTrace tailWord_5349323 prefixEnd_5349323 915591291717026494287139 := by
  unfold tailWord_5349323
  simp only [CollatzResearch.WordTrace]
  refine ⟨195105838399323837478764623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130070558932882558319176415 195105838399323837478764623)
  ·
    refine ⟨292658757598985756218146935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195105838399323837478764623 292658757598985756218146935)
    ·
      refine ⟨438988136398478634327220403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292658757598985756218146935 438988136398478634327220403)
      ·
        refine ⟨658482204597717951490830605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 438988136398478634327220403 658482204597717951490830605)
        ·
          refine ⟨246930826724144231809061477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 658482204597717951490830605 246930826724144231809061477)
          ·
            refine ⟨46299530010777043464199027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 246930826724144231809061477 46299530010777043464199027)
            ·
              refine ⟨69449295016165565196298541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46299530010777043464199027 69449295016165565196298541)
              ·
                refine ⟨26043485631062086948611953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69449295016165565196298541 26043485631062086948611953)
                ·
                  refine ⟨19532614223296565211458965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26043485631062086948611953 19532614223296565211458965)
                  ·
                    refine ⟨915591291717026494287139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19532614223296565211458965 915591291717026494287139)
                    ·
                      rfl

theorem cell23_5349323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 6].length) (baseStart_5349323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349323 prefixEnd_5349323 := by exact prefixLift 5349323
  have htrace : WordTrace (prefixWord ++ tailWord_5349323) baseStart_5349323 baseEnd_5349323 := by
    simpa [prefixWord, tailWord_5349323, baseEnd_5349323] using wordTrace_append hprefix tailTrace_5349323
  have hstable : (prefixWord ++ tailWord_5349323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349323).length < 2 ^ (prefixWord ++ tailWord_5349323).sum := by decide
  have hdescent : baseEnd_5349323 < baseStart_5349323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349381 : List Nat := [1, 3, 1, 1, 2, 4, 4, 1, 2, 2, 2]
def baseStart_5349381 : Nat := 118140960795 + 5349381 * 2 ^ 59
def prefixEnd_5349381 : Nat := 4983230072969 + 3 ^ 40 * 5349381 * 2
def baseEnd_5349381 : Nat := 2746803657029040255936151

theorem tailTrace_5349381 : CollatzResearch.WordTrace tailWord_5349381 prefixEnd_5349381 2746803657029040255936151 := by
  unfold tailWord_5349381
  simp only [CollatzResearch.WordTrace]
  refine ⟨195107953833113713384375997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130071969222075808922917331 195107953833113713384375997)
  ·
    refine ⟨73165482687417642519140999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195107953833113713384375997 73165482687417642519140999)
    ·
      refine ⟨109748224031126463778711499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73165482687417642519140999 109748224031126463778711499)
      ·
        refine ⟨164622336046689695668067249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109748224031126463778711499 164622336046689695668067249)
        ·
          refine ⟨123466752035017271751050437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164622336046689695668067249 123466752035017271751050437)
          ·
            refine ⟨23150016006565738453321957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123466752035017271751050437 23150016006565738453321957)
            ·
              refine ⟨4340628001231075959997867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23150016006565738453321957 4340628001231075959997867)
              ·
                refine ⟨6510942001846613939996801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4340628001231075959997867 6510942001846613939996801)
                ·
                  refine ⟨4883206501384960454997601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6510942001846613939996801 4883206501384960454997601)
                  ·
                    refine ⟨3662404876038720341248201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4883206501384960454997601 3662404876038720341248201)
                    ·
                      refine ⟨2746803657029040255936151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662404876038720341248201 2746803657029040255936151)
                      ·
                        rfl

theorem cell23_5349381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 1, 2, 2, 2].length) (baseStart_5349381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349381 prefixEnd_5349381 := by exact prefixLift 5349381
  have htrace : WordTrace (prefixWord ++ tailWord_5349381) baseStart_5349381 baseEnd_5349381 := by
    simpa [prefixWord, tailWord_5349381, baseEnd_5349381] using wordTrace_append hprefix tailTrace_5349381
  have hstable : (prefixWord ++ tailWord_5349381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349381).length < 2 ^ (prefixWord ++ tailWord_5349381).sum := by decide
  have hdescent : baseEnd_5349381 < baseStart_5349381 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349410 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 3, 2, 5]
def baseStart_5349410 : Nat := 118140960795 + 5349410 * 2 ^ 59
def prefixEnd_5349410 : Nat := 4983230072969 + 3 ^ 40 * 5349410 * 2
def baseEnd_5349410 : Nat := 2746818547968020642473517

theorem tailTrace_5349410 : CollatzResearch.WordTrace tailWord_5349410 prefixEnd_5349410 2746818547968020642473517 := by
  unfold tailWord_5349410
  simp only [CollatzResearch.WordTrace]
  refine ⟨48777252887502162834295421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130072674366672434224787789 48777252887502162834295421)
  ·
    refine ⟨18291469832813311062860783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48777252887502162834295421 18291469832813311062860783)
    ·
      refine ⟨27437204749219966594291175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18291469832813311062860783 27437204749219966594291175)
      ·
        refine ⟨41155807123829949891436763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27437204749219966594291175 41155807123829949891436763)
        ·
          refine ⟨61733710685744924837155145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41155807123829949891436763 61733710685744924837155145)
          ·
            refine ⟨46300283014308693627866359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61733710685744924837155145 46300283014308693627866359)
            ·
              refine ⟨69450424521463040441799539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46300283014308693627866359 69450424521463040441799539)
              ·
                refine ⟨104175636782194560662699309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69450424521463040441799539 104175636782194560662699309)
                ·
                  refine ⟨39065863793322960248512241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104175636782194560662699309 39065863793322960248512241)
                  ·
                    refine ⟨29299397844992220186384181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39065863793322960248512241 29299397844992220186384181)
                    ·
                      refine ⟨2746818547968020642473517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29299397844992220186384181 2746818547968020642473517)
                      ·
                        rfl

theorem cell23_5349410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_5349410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349410 prefixEnd_5349410 := by exact prefixLift 5349410
  have htrace : WordTrace (prefixWord ++ tailWord_5349410) baseStart_5349410 baseEnd_5349410 := by
    simpa [prefixWord, tailWord_5349410, baseEnd_5349410] using wordTrace_append hprefix tailTrace_5349410
  have hstable : (prefixWord ++ tailWord_5349410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349410).length < 2 ^ (prefixWord ++ tailWord_5349410).sum := by decide
  have hdescent : baseEnd_5349410 < baseStart_5349410 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349420 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 4]
def baseStart_5349420 : Nat := 118140960795 + 5349420 * 2 ^ 59
def prefixEnd_5349420 : Nat := 4983230072969 + 3 ^ 40 * 5349420 * 2
def baseEnd_5349420 : Nat := 2746823682774565603348471

theorem tailTrace_5349420 : CollatzResearch.WordTrace tailWord_5349420 prefixEnd_5349420 2746823682774565603348471 := by
  unfold tailWord_5349420
  simp only [CollatzResearch.WordTrace]
  refine ⟨97554688139986211522522857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130072917519981615363363809 97554688139986211522522857)
  ·
    refine ⟨73166016104989658641892143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97554688139986211522522857 73166016104989658641892143)
    ·
      refine ⟨109749024157484487962838215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73166016104989658641892143 109749024157484487962838215)
      ·
        refine ⟨164623536236226731944257323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109749024157484487962838215 164623536236226731944257323)
        ·
          refine ⟨246935304354340097916385985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164623536236226731944257323 246935304354340097916385985)
          ·
            refine ⟨185201478265755073437289489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 246935304354340097916385985 185201478265755073437289489)
            ·
              refine ⟨138901108699316305077967117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185201478265755073437289489 138901108699316305077967117)
              ·
                refine ⟨52087915762243614404237669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138901108699316305077967117 52087915762243614404237669)
                ·
                  refine ⟨9766484205420677700794563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52087915762243614404237669 9766484205420677700794563)
                  ·
                    refine ⟨14649726308131016551191845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9766484205420677700794563 14649726308131016551191845)
                    ·
                      refine ⟨2746823682774565603348471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14649726308131016551191845 2746823682774565603348471)
                      ·
                        rfl

theorem cell23_5349420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_5349420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349420 prefixEnd_5349420 := by exact prefixLift 5349420
  have htrace : WordTrace (prefixWord ++ tailWord_5349420) baseStart_5349420 baseEnd_5349420 := by
    simpa [prefixWord, tailWord_5349420, baseEnd_5349420] using wordTrace_append hprefix tailTrace_5349420
  have hstable : (prefixWord ++ tailWord_5349420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349420).length < 2 ^ (prefixWord ++ tailWord_5349420).sum := by decide
  have hdescent : baseEnd_5349420 < baseStart_5349420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349447 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 3, 4]
def baseStart_5349447 : Nat := 118140960795 + 5349447 * 2 ^ 59
def prefixEnd_5349447 : Nat := 4983230072969 + 3 ^ 40 * 5349447 * 2
def baseEnd_5349447 : Nat := 915612515584078999236949

theorem tailTrace_5349447 : CollatzResearch.WordTrace tailWord_5349447 prefixEnd_5349447 915612515584078999236949 := by
  unfold tailWord_5349447
  simp only [CollatzResearch.WordTrace]
  refine ⟨195110361050874606656278595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130073574033916404437519063 195110361050874606656278595)
  ·
    refine ⟨292665541576311909984417893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195110361050874606656278595 292665541576311909984417893)
    ·
      refine ⟨54874789045558483122078355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 292665541576311909984417893 54874789045558483122078355)
      ·
        refine ⟨82312183568337724683117533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54874789045558483122078355 82312183568337724683117533)
        ·
          refine ⟨30867068838126646756169075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82312183568337724683117533 30867068838126646756169075)
          ·
            refine ⟨46300603257189970134253613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30867068838126646756169075 46300603257189970134253613)
            ·
              refine ⟨17362726221446238800345105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46300603257189970134253613 17362726221446238800345105)
              ·
                refine ⟨13022044666084679100258829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17362726221446238800345105 13022044666084679100258829)
                ·
                  refine ⟨4883266749781754662597061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13022044666084679100258829 4883266749781754662597061)
                  ·
                    refine ⟨915612515584078999236949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4883266749781754662597061 915612515584078999236949)
                    ·
                      rfl

theorem cell23_5349447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_5349447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349447 prefixEnd_5349447 := by exact prefixLift 5349447
  have htrace : WordTrace (prefixWord ++ tailWord_5349447) baseStart_5349447 baseEnd_5349447 := by
    simpa [prefixWord, tailWord_5349447, baseEnd_5349447] using wordTrace_append hprefix tailTrace_5349447
  have hstable : (prefixWord ++ tailWord_5349447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349447).length < 2 ^ (prefixWord ++ tailWord_5349447).sum := by decide
  have hdescent : baseEnd_5349447 < baseStart_5349447 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349454 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4]
def baseStart_5349454 : Nat := 118140960795 + 5349454 * 2 ^ 59
def prefixEnd_5349454 : Nat := 4983230072969 + 3 ^ 40 * 5349454 * 2
def baseEnd_5349454 : Nat := 2746841141116818470323315

theorem tailTrace_5349454 : CollatzResearch.WordTrace tailWord_5349454 prefixEnd_5349454 2746841141116818470323315 := by
  unfold tailWord_5349454
  simp only [CollatzResearch.WordTrace]
  refine ⟨24388827045231155856472927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130073744241232831234522277 24388827045231155856472927)
  ·
    refine ⟨36583240567846733784709391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24388827045231155856472927 36583240567846733784709391)
    ·
      refine ⟨54874860851770100677064087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36583240567846733784709391 54874860851770100677064087)
      ·
        refine ⟨82312291277655151015596131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54874860851770100677064087 82312291277655151015596131)
        ·
          refine ⟨123468436916482726523394197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82312291277655151015596131 123468436916482726523394197)
          ·
            refine ⟨5787582980460127805784103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 123468436916482726523394197 5787582980460127805784103)
            ·
              refine ⟨8681374470690191708676155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5787582980460127805784103 8681374470690191708676155)
              ·
                refine ⟨13022061706035287563014233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8681374470690191708676155 13022061706035287563014233)
                ·
                  refine ⟨9766546279526465672260675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13022061706035287563014233 9766546279526465672260675)
                  ·
                    refine ⟨14649819419289698508391013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9766546279526465672260675 14649819419289698508391013)
                    ·
                      refine ⟨2746841141116818470323315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14649819419289698508391013 2746841141116818470323315)
                      ·
                        rfl

theorem cell23_5349454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_5349454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349454 prefixEnd_5349454 := by exact prefixLift 5349454
  have htrace : WordTrace (prefixWord ++ tailWord_5349454) baseStart_5349454 baseEnd_5349454 := by
    simpa [prefixWord, tailWord_5349454, baseEnd_5349454] using wordTrace_append hprefix tailTrace_5349454
  have hstable : (prefixWord ++ tailWord_5349454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349454).length < 2 ^ (prefixWord ++ tailWord_5349454).sum := by decide
  have hdescent : baseEnd_5349454 < baseStart_5349454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349460 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 8]
def baseStart_5349460 : Nat := 118140960795 + 5349460 * 2 ^ 59
def prefixEnd_5349460 : Nat := 4983230072969 + 3 ^ 40 * 5349460 * 2
def baseEnd_5349460 : Nat := 305204913555638382983143

theorem tailTrace_5349460 : CollatzResearch.WordTrace tailWord_5349460 prefixEnd_5349460 305204913555638382983143 := by
  unfold tailWord_5349460
  simp only [CollatzResearch.WordTrace]
  refine ⟨97555417599913754938250917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130073890133218339917667889 97555417599913754938250917)
  ·
    refine ⟨18291640799983829050922047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97555417599913754938250917 18291640799983829050922047)
    ·
      refine ⟨27437461199975743576383071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18291640799983829050922047 27437461199975743576383071)
      ·
        refine ⟨41156191799963615364574607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27437461199975743576383071 41156191799963615364574607)
        ·
          refine ⟨61734287699945423046861911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41156191799963615364574607 61734287699945423046861911)
          ·
            refine ⟨92601431549918134570292867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61734287699945423046861911 92601431549918134570292867)
            ·
              refine ⟨138902147324877201855439301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92601431549918134570292867 138902147324877201855439301)
              ·
                refine ⟨26044152623414475347894869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138902147324877201855439301 26044152623414475347894869)
                ·
                  refine ⟨305204913555638382983143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26044152623414475347894869 305204913555638382983143)
                  ·
                    rfl

theorem cell23_5349460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_5349460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349460 prefixEnd_5349460 := by exact prefixLift 5349460
  have htrace : WordTrace (prefixWord ++ tailWord_5349460) baseStart_5349460 baseEnd_5349460 := by
    simpa [prefixWord, tailWord_5349460, baseEnd_5349460] using wordTrace_append hprefix tailTrace_5349460
  have hstable : (prefixWord ++ tailWord_5349460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349460).length < 2 ^ (prefixWord ++ tailWord_5349460).sum := by decide
  have hdescent : baseEnd_5349460 < baseStart_5349460 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349464 : List Nat := [2, 1, 2, 2, 1, 4, 1, 5, 1, 4]
def baseStart_5349464 : Nat := 118140960795 + 5349464 * 2 ^ 59
def prefixEnd_5349464 : Nat := 4983230072969 + 3 ^ 40 * 5349464 * 2
def baseEnd_5349464 : Nat := 915615425307787810399423

theorem tailTrace_5349464 : CollatzResearch.WordTrace tailWord_5349464 prefixEnd_5349464 915615425307787810399423 := by
  unfold tailWord_5349464
  simp only [CollatzResearch.WordTrace]
  refine ⟨97555490545906509279823723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130073987394542012373098297 97555490545906509279823723)
  ·
    refine ⟨146333235818859763919735585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97555490545906509279823723 146333235818859763919735585)
    ·
      refine ⟨109749926864144822939801689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146333235818859763919735585 109749926864144822939801689)
      ·
        refine ⟨82312445148108617204851267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109749926864144822939801689 82312445148108617204851267)
        ·
          refine ⟨123468667722162925807276901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82312445148108617204851267 123468667722162925807276901)
          ·
            refine ⟨23150375197905548588864419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 123468667722162925807276901 23150375197905548588864419)
            ·
              refine ⟨34725562796858322883296629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23150375197905548588864419 34725562796858322883296629)
              ·
                refine ⟨3255521512205467770309059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34725562796858322883296629 3255521512205467770309059)
                ·
                  refine ⟨4883282268308201655463589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255521512205467770309059 4883282268308201655463589)
                  ·
                    refine ⟨915615425307787810399423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4883282268308201655463589 915615425307787810399423)
                    ·
                      rfl

theorem cell23_5349464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_5349464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349464 prefixEnd_5349464 := by exact prefixLift 5349464
  have htrace : WordTrace (prefixWord ++ tailWord_5349464) baseStart_5349464 baseEnd_5349464 := by
    simpa [prefixWord, tailWord_5349464, baseEnd_5349464] using wordTrace_append hprefix tailTrace_5349464
  have hstable : (prefixWord ++ tailWord_5349464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349464).length < 2 ^ (prefixWord ++ tailWord_5349464).sum := by decide
  have hdescent : baseEnd_5349464 < baseStart_5349464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349477 : List Nat := [1, 3, 1, 3, 2, 2, 3, 2, 6]
def baseStart_5349477 : Nat := 118140960795 + 5349477 * 2 ^ 59
def prefixEnd_5349477 : Nat := 4983230072969 + 3 ^ 40 * 5349477 * 2
def baseEnd_5349477 : Nat := 305205883463541320037301

theorem tailTrace_5349477 : CollatzResearch.WordTrace tailWord_5349477 prefixEnd_5349477 305205883463541320037301 := by
  unfold tailWord_5349477
  simp only [CollatzResearch.WordTrace]
  refine ⟨195111455240765921779870685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130074303493843947853247123 195111455240765921779870685)
  ·
    refine ⟨73166795715287220667451507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195111455240765921779870685 73166795715287220667451507)
    ·
      refine ⟨109750193572930831001177261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73166795715287220667451507 109750193572930831001177261)
      ·
        refine ⟨41156322589849061625441473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109750193572930831001177261 41156322589849061625441473)
        ·
          refine ⟨30867241942386796219081105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41156322589849061625441473 30867241942386796219081105)
          ·
            refine ⟨23150431456790097164310829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30867241942386796219081105 23150431456790097164310829)
            ·
              refine ⟨8681411796296286436616561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23150431456790097164310829 8681411796296286436616561)
              ·
                refine ⟨6511058847222214827462421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8681411796296286436616561 6511058847222214827462421)
                ·
                  refine ⟨305205883463541320037301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6511058847222214827462421 305205883463541320037301)
                  ·
                    rfl

theorem cell23_5349477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 6].length) (baseStart_5349477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349477 prefixEnd_5349477 := by exact prefixLift 5349477
  have htrace : WordTrace (prefixWord ++ tailWord_5349477) baseStart_5349477 baseEnd_5349477 := by
    simpa [prefixWord, tailWord_5349477, baseEnd_5349477] using wordTrace_append hprefix tailTrace_5349477
  have hstable : (prefixWord ++ tailWord_5349477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349477).length < 2 ^ (prefixWord ++ tailWord_5349477).sum := by decide
  have hdescent : baseEnd_5349477 < baseStart_5349477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349507 : List Nat := [1, 1, 1, 3, 3, 3, 1, 4, 1, 5]
def baseStart_5349507 : Nat := 118140960795 + 5349507 * 2 ^ 59
def prefixEnd_5349507 : Nat := 4983230072969 + 3 ^ 40 * 5349507 * 2
def baseEnd_5349507 : Nat := 915622785197168920986857

theorem tailTrace_5349507 : CollatzResearch.WordTrace tailWord_5349507 prefixEnd_5349507 915622785197168920986857 := by
  unfold tailWord_5349507
  simp only [CollatzResearch.WordTrace]
  refine ⟨195112549430657236903462775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130075032953771491268975183 195112549430657236903462775)
  ·
    refine ⟨292668824145985855355194163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195112549430657236903462775 292668824145985855355194163)
    ·
      refine ⟨439003236218978783032791245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292668824145985855355194163 439003236218978783032791245)
      ·
        refine ⟨164626213582117043637296717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 439003236218978783032791245 164626213582117043637296717)
        ·
          refine ⟨61734830093293891363986269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164626213582117043637296717 61734830093293891363986269)
          ·
            refine ⟨23150561284985209261494851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 61734830093293891363986269 23150561284985209261494851)
            ·
              refine ⟨34725841927477813892242277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23150561284985209261494851 34725841927477813892242277)
              ·
                refine ⟨6511095361402090104795427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34725841927477813892242277 6511095361402090104795427)
                ·
                  refine ⟨9766643042103135157193141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6511095361402090104795427 9766643042103135157193141)
                  ·
                    refine ⟨915622785197168920986857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9766643042103135157193141 915622785197168920986857)
                    ·
                      rfl

theorem cell23_5349507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 5].length) (baseStart_5349507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349507 prefixEnd_5349507 := by exact prefixLift 5349507
  have htrace : WordTrace (prefixWord ++ tailWord_5349507) baseStart_5349507 baseEnd_5349507 := by
    simpa [prefixWord, tailWord_5349507, baseEnd_5349507] using wordTrace_append hprefix tailTrace_5349507
  have hstable : (prefixWord ++ tailWord_5349507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349507).length < 2 ^ (prefixWord ++ tailWord_5349507).sum := by decide
  have hdescent : baseEnd_5349507 < baseStart_5349507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349514 : List Nat := [3, 1, 2, 3, 1, 2, 2, 1, 1, 5, 2]
def baseStart_5349514 : Nat := 118140960795 + 5349514 * 2 ^ 59
def prefixEnd_5349514 : Nat := 4983230072969 + 3 ^ 40 * 5349514 * 2
def baseEnd_5349514 : Nat := 2746871949956088235573039

theorem tailTrace_5349514 : CollatzResearch.WordTrace tailWord_5349514 prefixEnd_5349514 2746871949956088235573039 := by
  unfold tailWord_5349514
  simp only [CollatzResearch.WordTrace]
  refine ⟨48778201185407969274741899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130075203161087918065978397 48778201185407969274741899)
  ·
    refine ⟨73167301778111953912112849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48778201185407969274741899 73167301778111953912112849)
    ·
      refine ⟨54875476333583965434084637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73167301778111953912112849 54875476333583965434084637)
      ·
        refine ⟨20578303625093987037781739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54875476333583965434084637 20578303625093987037781739)
        ·
          refine ⟨30867455437640980556672609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20578303625093987037781739 30867455437640980556672609)
          ·
            refine ⟨23150591578230735417504457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30867455437640980556672609 23150591578230735417504457)
            ·
              refine ⟨17362943683673051563128343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23150591578230735417504457 17362943683673051563128343)
              ·
                refine ⟨26044415525509577344692515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17362943683673051563128343 26044415525509577344692515)
                ·
                  refine ⟨39066623288264366017038773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26044415525509577344692515 39066623288264366017038773)
                  ·
                    refine ⟨3662495933274784314097385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39066623288264366017038773 3662495933274784314097385)
                    ·
                      refine ⟨2746871949956088235573039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662495933274784314097385 2746871949956088235573039)
                      ·
                        rfl

theorem cell23_5349514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_5349514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349514 prefixEnd_5349514 := by exact prefixLift 5349514
  have htrace : WordTrace (prefixWord ++ tailWord_5349514) baseStart_5349514 baseEnd_5349514 := by
    simpa [prefixWord, tailWord_5349514, baseEnd_5349514] using wordTrace_append hprefix tailTrace_5349514
  have hstable : (prefixWord ++ tailWord_5349514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349514).length < 2 ^ (prefixWord ++ tailWord_5349514).sum := by decide
  have hdescent : baseEnd_5349514 < baseStart_5349514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349520 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 3, 6]
def baseStart_5349520 : Nat := 118140960795 + 5349520 * 2 ^ 59
def prefixEnd_5349520 : Nat := 4983230072969 + 3 ^ 40 * 5349520 * 2
def baseEnd_5349520 : Nat := 915625010280005070699337

theorem tailTrace_5349520 : CollatzResearch.WordTrace tailWord_5349520 prefixEnd_5349520 915625010280005070699337 := by
  unfold tailWord_5349520
  simp only [CollatzResearch.WordTrace]
  refine ⟨97556511789805070061843007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130075349053073426749124009 97556511789805070061843007)
  ·
    refine ⟨146334767684707605092764511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97556511789805070061843007 146334767684707605092764511)
    ·
      refine ⟨219502151527061407639146767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146334767684707605092764511 219502151527061407639146767)
      ·
        refine ⟨329253227290592111458720151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219502151527061407639146767 329253227290592111458720151)
        ·
          refine ⟨493879840935888167188080227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329253227290592111458720151 493879840935888167188080227)
          ·
            refine ⟨740819761403832250782120341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493879840935888167188080227 740819761403832250782120341)
            ·
              refine ⟨34725926315804636755411891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 740819761403832250782120341 34725926315804636755411891)
              ·
                refine ⟨52088889473706955133117837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34725926315804636755411891 52088889473706955133117837)
                ·
                  refine ⟨19533333552640108174919189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52088889473706955133117837 19533333552640108174919189)
                  ·
                    refine ⟨915625010280005070699337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19533333552640108174919189 915625010280005070699337)
                    ·
                      rfl

theorem cell23_5349520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 3, 6].length) (baseStart_5349520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349520 prefixEnd_5349520 := by exact prefixLift 5349520
  have htrace : WordTrace (prefixWord ++ tailWord_5349520) baseStart_5349520 baseEnd_5349520 := by
    simpa [prefixWord, tailWord_5349520, baseEnd_5349520] using wordTrace_append hprefix tailTrace_5349520
  have hstable : (prefixWord ++ tailWord_5349520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349520).length < 2 ^ (prefixWord ++ tailWord_5349520).sum := by decide
  have hdescent : baseEnd_5349520 < baseStart_5349520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349538 : List Nat := [3, 3, 1, 3, 1, 3, 1, 1, 3, 1, 3]
def baseStart_5349538 : Nat := 118140960795 + 5349538 * 2 ^ 59
def prefixEnd_5349538 : Nat := 4983230072969 + 3 ^ 40 * 5349538 * 2
def baseEnd_5349538 : Nat := 2746884273491796141672929

theorem tailTrace_5349538 : CollatzResearch.WordTrace tailWord_5349538 prefixEnd_5349538 2746884273491796141672929 := by
  unfold tailWord_5349538
  simp only [CollatzResearch.WordTrace]
  refine ⟨48778420023386232299460317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130075786729029952798560845 48778420023386232299460317)
  ·
    refine ⟨18291907508769837112297619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48778420023386232299460317 18291907508769837112297619)
    ·
      refine ⟨27437861263154755668446429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18291907508769837112297619 27437861263154755668446429)
      ·
        refine ⟨10289197973683033375667411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27437861263154755668446429 10289197973683033375667411)
        ·
          refine ⟨15433796960524550063501117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10289197973683033375667411 15433796960524550063501117)
          ·
            refine ⟨5787673860196706273812919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15433796960524550063501117 5787673860196706273812919)
            ·
              refine ⟨8681510790295059410719379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5787673860196706273812919 8681510790295059410719379)
              ·
                refine ⟨13022266185442589116079069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8681510790295059410719379 13022266185442589116079069)
                ·
                  refine ⟨4883349819540970918529651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13022266185442589116079069 4883349819540970918529651)
                  ·
                    refine ⟨7325024729311456377794477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4883349819540970918529651 7325024729311456377794477)
                    ·
                      refine ⟨2746884273491796141672929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7325024729311456377794477 2746884273491796141672929)
                      ·
                        rfl

theorem cell23_5349538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_5349538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349538 prefixEnd_5349538 := by exact prefixLift 5349538
  have htrace : WordTrace (prefixWord ++ tailWord_5349538) baseStart_5349538 baseEnd_5349538 := by
    simpa [prefixWord, tailWord_5349538, baseEnd_5349538] using wordTrace_append hprefix tailTrace_5349538
  have hstable : (prefixWord ++ tailWord_5349538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349538).length < 2 ^ (prefixWord ++ tailWord_5349538).sum := by decide
  have hdescent : baseEnd_5349538 < baseStart_5349538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349554 : List Nat := [3, 2, 1, 1, 1, 3, 3, 3, 2, 4]
def baseStart_5349554 : Nat := 118140960795 + 5349554 * 2 ^ 59
def prefixEnd_5349554 : Nat := 4983230072969 + 3 ^ 40 * 5349554 * 2
def baseEnd_5349554 : Nat := 915630829727422693024285

theorem tailTrace_5349554 : CollatzResearch.WordTrace tailWord_5349554 prefixEnd_5349554 915630829727422693024285 := by
  unfold tailWord_5349554
  simp only [CollatzResearch.WordTrace]
  refine ⟨48778565915371740982605929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130076175774324642620282477 48778565915371740982605929)
  ·
    refine ⟨36583924436528805736954447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48778565915371740982605929 36583924436528805736954447)
    ·
      refine ⟨54875886654793208605431671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36583924436528805736954447 54875886654793208605431671)
      ·
        refine ⟨82313829982189812908147507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54875886654793208605431671 82313829982189812908147507)
        ·
          refine ⟨123470744973284719362221261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82313829982189812908147507 123470744973284719362221261)
          ·
            refine ⟨46301529364981769760832973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 123470744973284719362221261 46301529364981769760832973)
            ·
              refine ⟨17363073511868163660312365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46301529364981769760832973 17363073511868163660312365)
              ·
                refine ⟨6511152566950561372617137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17363073511868163660312365 6511152566950561372617137)
                ·
                  refine ⟨4883364425212921029462853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6511152566950561372617137 4883364425212921029462853)
                  ·
                    refine ⟨915630829727422693024285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4883364425212921029462853 915630829727422693024285)
                    ·
                      rfl

theorem cell23_5349554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_5349554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349554 prefixEnd_5349554 := by exact prefixLift 5349554
  have htrace : WordTrace (prefixWord ++ tailWord_5349554) baseStart_5349554 baseEnd_5349554 := by
    simpa [prefixWord, tailWord_5349554, baseEnd_5349554] using wordTrace_append hprefix tailTrace_5349554
  have hstable : (prefixWord ++ tailWord_5349554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349554).length < 2 ^ (prefixWord ++ tailWord_5349554).sum := by decide
  have hdescent : baseEnd_5349554 < baseStart_5349554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349578 : List Nat := [3, 1, 2, 1, 3, 1, 2, 5, 1, 2, 2]
def baseStart_5349578 : Nat := 118140960795 + 5349578 * 2 ^ 59
def prefixEnd_5349578 : Nat := 4983230072969 + 3 ^ 40 * 5349578 * 2
def baseEnd_5349578 : Nat := 2746904812717975985172745

theorem tailTrace_5349578 : CollatzResearch.WordTrace tailWord_5349578 prefixEnd_5349578 2746904812717975985172745 := by
  unfold tailWord_5349578
  simp only [CollatzResearch.WordTrace]
  refine ⟨48778784753350004007324347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130076759342266677352864925 48778784753350004007324347)
  ·
    refine ⟨73168177130025006010986521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48778784753350004007324347 73168177130025006010986521)
    ·
      refine ⟨54876132847518754508239891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73168177130025006010986521 54876132847518754508239891)
      ·
        refine ⟨82314199271278131762359837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54876132847518754508239891 82314199271278131762359837)
        ·
          refine ⟨30867824726729299410884939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 82314199271278131762359837 30867824726729299410884939)
          ·
            refine ⟨46301737090093949116327409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30867824726729299410884939 46301737090093949116327409)
            ·
              refine ⟨34726302817570461837245557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46301737090093949116327409 34726302817570461837245557)
              ·
                refine ⟨3255590889147230797241771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34726302817570461837245557 3255590889147230797241771)
                ·
                  refine ⟨4883386333720846195862657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255590889147230797241771 4883386333720846195862657)
                  ·
                    refine ⟨3662539750290634646896993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4883386333720846195862657 3662539750290634646896993)
                    ·
                      refine ⟨2746904812717975985172745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662539750290634646896993 2746904812717975985172745)
                      ·
                        rfl

theorem cell23_5349578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 5, 1, 2, 2].length) (baseStart_5349578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349578 prefixEnd_5349578 := by exact prefixLift 5349578
  have htrace : WordTrace (prefixWord ++ tailWord_5349578) baseStart_5349578 baseEnd_5349578 := by
    simpa [prefixWord, tailWord_5349578, baseEnd_5349578] using wordTrace_append hprefix tailTrace_5349578
  have hstable : (prefixWord ++ tailWord_5349578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349578).length < 2 ^ (prefixWord ++ tailWord_5349578).sum := by decide
  have hdescent : baseEnd_5349578 < baseStart_5349578 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349594 : List Nat := [3, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3]
def baseStart_5349594 : Nat := 118140960795 + 5349594 * 2 ^ 59
def prefixEnd_5349594 : Nat := 4983230072969 + 3 ^ 40 * 5349594 * 2
def baseEnd_5349594 : Nat := 2746913028408447922572671

theorem tailTrace_5349594 : CollatzResearch.WordTrace tailWord_5349594 prefixEnd_5349594 2746913028408447922572671 := by
  unfold tailWord_5349594
  simp only [CollatzResearch.WordTrace]
  refine ⟨48778930645335512690469959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130077148387561367174586557 48778930645335512690469959)
  ·
    refine ⟨73168395968003269035704939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48778930645335512690469959 73168395968003269035704939)
    ·
      refine ⟨109752593952004903553557409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73168395968003269035704939 109752593952004903553557409)
      ·
        refine ⟨82314445464003677665168057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109752593952004903553557409 82314445464003677665168057)
        ·
          refine ⟨61735834098002758248876043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82314445464003677665168057 61735834098002758248876043)
          ·
            refine ⟨92603751147004137373314065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61735834098002758248876043 92603751147004137373314065)
            ·
              refine ⟨69452813360253103029985549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 92603751147004137373314065 69452813360253103029985549)
              ·
                refine ⟨26044805010094913636244581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 69452813360253103029985549 26044805010094913636244581)
                ·
                  refine ⟨4883400939392796306795859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26044805010094913636244581 4883400939392796306795859)
                  ·
                    refine ⟨7325101409089194460193789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4883400939392796306795859 7325101409089194460193789)
                    ·
                      refine ⟨2746913028408447922572671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7325101409089194460193789 2746913028408447922572671)
                      ·
                        rfl

theorem cell23_5349594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_5349594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349594 prefixEnd_5349594 := by exact prefixLift 5349594
  have htrace : WordTrace (prefixWord ++ tailWord_5349594) baseStart_5349594 baseEnd_5349594 := by
    simpa [prefixWord, tailWord_5349594, baseEnd_5349594] using wordTrace_append hprefix tailTrace_5349594
  have hstable : (prefixWord ++ tailWord_5349594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349594).length < 2 ^ (prefixWord ++ tailWord_5349594).sum := by decide
  have hdescent : baseEnd_5349594 < baseStart_5349594 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349637 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 1, 6, 3]
def baseStart_5349637 : Nat := 118140960795 + 5349637 * 2 ^ 59
def prefixEnd_5349637 : Nat := 4983230072969 + 3 ^ 40 * 5349637 * 2
def baseEnd_5349637 : Nat := 2746935108076591254334973

theorem tailTrace_5349637 : CollatzResearch.WordTrace tailWord_5349637 prefixEnd_5349637 2746935108076591254334973 := by
  unfold tailWord_5349637
  simp only [CollatzResearch.WordTrace]
  refine ⟨195117290920186269105695165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130078193946790846070463443 195117290920186269105695165)
  ·
    refine ⟨73168984095069850914635687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195117290920186269105695165 73168984095069850914635687)
    ·
      refine ⟨109753476142604776371953531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73168984095069850914635687 109753476142604776371953531)
      ·
        refine ⟨164630214213907164557930297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109753476142604776371953531 164630214213907164557930297)
        ·
          refine ⟨123472660660430373418447723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164630214213907164557930297 123472660660430373418447723)
          ·
            refine ⟨185208990990645560127671585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123472660660430373418447723 185208990990645560127671585)
            ·
              refine ⟨138906743242984170095753689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185208990990645560127671585 138906743242984170095753689)
              ·
                refine ⟨104180057432238127571815267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138906743242984170095753689 104180057432238127571815267)
                ·
                  refine ⟨156270086148357191357722901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104180057432238127571815267 156270086148357191357722901)
                  ·
                    refine ⟨7325160288204243344893261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 156270086148357191357722901 7325160288204243344893261)
                    ·
                      refine ⟨2746935108076591254334973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7325160288204243344893261 2746935108076591254334973)
                      ·
                        rfl

theorem cell23_5349637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_5349637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349637 prefixEnd_5349637 := by exact prefixLift 5349637
  have htrace : WordTrace (prefixWord ++ tailWord_5349637) baseStart_5349637 baseEnd_5349637 := by
    simpa [prefixWord, tailWord_5349637, baseEnd_5349637] using wordTrace_append hprefix tailTrace_5349637
  have hstable : (prefixWord ++ tailWord_5349637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349637).length < 2 ^ (prefixWord ++ tailWord_5349637).sum := by decide
  have hdescent : baseEnd_5349637 < baseStart_5349637 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349662 : List Nat := [4, 3, 2, 1, 1, 2, 3, 1, 2, 1, 3]
def baseStart_5349662 : Nat := 118140960795 + 5349662 * 2 ^ 59
def prefixEnd_5349662 : Nat := 4983230072969 + 3 ^ 40 * 5349662 * 2
def baseEnd_5349662 : Nat := 2746947945092953656522359

theorem tailTrace_5349662 : CollatzResearch.WordTrace tailWord_5349662 prefixEnd_5349662 2746947945092953656522359 := by
  unfold tailWord_5349662
  simp only [CollatzResearch.WordTrace]
  refine ⟨24389775343136962296919405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 130078801830063798916903493 24389775343136962296919405)
  ·
    refine ⟨9146165753676360861344777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24389775343136962296919405 9146165753676360861344777)
    ·
      refine ⟨6859624315257270646008583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9146165753676360861344777 6859624315257270646008583)
      ·
        refine ⟨10289436472885905969012875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6859624315257270646008583 10289436472885905969012875)
        ·
          refine ⟨15434154709328858953519313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10289436472885905969012875 15434154709328858953519313)
          ·
            refine ⟨11575616031996644215139485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15434154709328858953519313 11575616031996644215139485)
            ·
              refine ⟨4340856011998741580677307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11575616031996644215139485 4340856011998741580677307)
              ·
                refine ⟨6511284017998112371015961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4340856011998741580677307 6511284017998112371015961)
                ·
                  refine ⟨4883463013498584278261971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6511284017998112371015961 4883463013498584278261971)
                  ·
                    refine ⟨7325194520247876417392957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4883463013498584278261971 7325194520247876417392957)
                    ·
                      refine ⟨2746947945092953656522359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7325194520247876417392957 2746947945092953656522359)
                      ·
                        rfl

theorem cell23_5349662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_5349662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349662 prefixEnd_5349662 := by exact prefixLift 5349662
  have htrace : WordTrace (prefixWord ++ tailWord_5349662) baseStart_5349662 baseEnd_5349662 := by
    simpa [prefixWord, tailWord_5349662, baseEnd_5349662] using wordTrace_append hprefix tailTrace_5349662
  have hstable : (prefixWord ++ tailWord_5349662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349662).length < 2 ^ (prefixWord ++ tailWord_5349662).sum := by decide
  have hdescent : baseEnd_5349662 < baseStart_5349662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349664 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 4]
def baseStart_5349664 : Nat := 118140960795 + 5349664 * 2 ^ 59
def prefixEnd_5349664 : Nat := 4983230072969 + 3 ^ 40 * 5349664 * 2
def baseEnd_5349664 : Nat := 2746948972054262648697349

theorem tailTrace_5349664 : CollatzResearch.WordTrace tailWord_5349664 prefixEnd_5349664 2746948972054262648697349 := by
  unfold tailWord_5349664
  simp only [CollatzResearch.WordTrace]
  refine ⟨97559137845544226358464023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130078850460725635144618697 97559137845544226358464023)
  ·
    refine ⟨146338706768316339537696035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97559137845544226358464023 146338706768316339537696035)
    ·
      refine ⟨219508060152474509306544053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146338706768316339537696035 219508060152474509306544053)
      ·
        refine ⟨20578880639294485247488505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 219508060152474509306544053 20578880639294485247488505)
        ·
          refine ⟨15434160479470863935616379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20578880639294485247488505 15434160479470863935616379)
          ·
            refine ⟨23151240719206295903424569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15434160479470863935616379 23151240719206295903424569)
            ·
              refine ⟨17363430539404721927568427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23151240719206295903424569 17363430539404721927568427)
              ·
                refine ⟨26045145809107082891352641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17363430539404721927568427 26045145809107082891352641)
                ·
                  refine ⟨19533859356830312168514481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26045145809107082891352641 19533859356830312168514481)
                  ·
                    refine ⟨14650394517622734126385861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19533859356830312168514481 14650394517622734126385861)
                    ·
                      refine ⟨2746948972054262648697349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14650394517622734126385861 2746948972054262648697349)
                      ·
                        rfl

theorem cell23_5349664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_5349664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349664 prefixEnd_5349664 := by exact prefixLift 5349664
  have htrace : WordTrace (prefixWord ++ tailWord_5349664) baseStart_5349664 baseEnd_5349664 := by
    simpa [prefixWord, tailWord_5349664, baseEnd_5349664] using wordTrace_append hprefix tailTrace_5349664
  have hstable : (prefixWord ++ tailWord_5349664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349664).length < 2 ^ (prefixWord ++ tailWord_5349664).sum := by decide
  have hdescent : baseEnd_5349664 < baseStart_5349664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349668 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 1, 4, 2]
def baseStart_5349668 : Nat := 118140960795 + 5349668 * 2 ^ 59
def prefixEnd_5349668 : Nat := 4983230072969 + 3 ^ 40 * 5349668 * 2
def baseEnd_5349668 : Nat := 2746951025976880633047331

theorem tailTrace_5349668 : CollatzResearch.WordTrace tailWord_5349668 prefixEnd_5349668 2746951025976880633047331 := by
  unfold tailWord_5349668
  simp only [CollatzResearch.WordTrace]
  refine ⟨97559210791536980700036829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130078947722049307600049105 97559210791536980700036829)
  ·
    refine ⟨36584704046826367762513811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97559210791536980700036829 36584704046826367762513811)
    ·
      refine ⟨54877056070239551643770717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36584704046826367762513811 54877056070239551643770717)
      ·
        refine ⟨20578896026339831866414019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54877056070239551643770717 20578896026339831866414019)
        ·
          refine ⟨30868344039509747799621029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20578896026339831866414019 30868344039509747799621029)
          ·
            refine ⟨5787814507408077712428943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30868344039509747799621029 5787814507408077712428943)
            ·
              refine ⟨8681721761112116568643415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5787814507408077712428943 8681721761112116568643415)
              ·
                refine ⟨13022582641668174852965123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8681721761112116568643415 13022582641668174852965123)
                ·
                  refine ⟨19533873962502262279447685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13022582641668174852965123 19533873962502262279447685)
                  ·
                    refine ⟨3662601367969174177396441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19533873962502262279447685 3662601367969174177396441)
                    ·
                      refine ⟨2746951025976880633047331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662601367969174177396441 2746951025976880633047331)
                      ·
                        rfl

theorem cell23_5349668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 1, 4, 2].length) (baseStart_5349668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349668 prefixEnd_5349668 := by exact prefixLift 5349668
  have htrace : WordTrace (prefixWord ++ tailWord_5349668) baseStart_5349668 baseEnd_5349668 := by
    simpa [prefixWord, tailWord_5349668, baseEnd_5349668] using wordTrace_append hprefix tailTrace_5349668
  have hstable : (prefixWord ++ tailWord_5349668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349668).length < 2 ^ (prefixWord ++ tailWord_5349668).sum := by decide
  have hdescent : baseEnd_5349668 < baseStart_5349668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349687 : List Nat := [1, 1, 3, 1, 2, 1, 1, 2, 6, 5]
def baseStart_5349687 : Nat := 118140960795 + 5349687 * 2 ^ 59
def prefixEnd_5349687 : Nat := 4983230072969 + 3 ^ 40 * 5349687 * 2
def baseEnd_5349687 : Nat := 915653594036438686236581

theorem tailTrace_5349687 : CollatzResearch.WordTrace tailWord_5349687 prefixEnd_5349687 915653594036438686236581 := by
  unfold tailWord_5349687
  simp only [CollatzResearch.WordTrace]
  refine ⟨195119114570005127645015315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130079409713336751763343543 195119114570005127645015315)
  ·
    refine ⟨292678671855007691467522973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195119114570005127645015315 292678671855007691467522973)
    ·
      refine ⟨109754501945627884300321115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 292678671855007691467522973 109754501945627884300321115)
      ·
        refine ⟨164631752918441826450481673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109754501945627884300321115 164631752918441826450481673)
        ·
          refine ⟨123473814688831369837861255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164631752918441826450481673 123473814688831369837861255)
          ·
            refine ⟨185210722033247054756791883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123473814688831369837861255 185210722033247054756791883)
            ·
              refine ⟨277816083049870582135187825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185210722033247054756791883 277816083049870582135187825)
              ·
                refine ⟨208362062287402936601390869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277816083049870582135187825 208362062287402936601390869)
                ·
                  refine ⟨9766971669722012653190197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 208362062287402936601390869 9766971669722012653190197)
                  ·
                    refine ⟨915653594036438686236581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9766971669722012653190197 915653594036438686236581)
                    ·
                      rfl

theorem cell23_5349687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_5349687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349687 prefixEnd_5349687 := by exact prefixLift 5349687
  have htrace : WordTrace (prefixWord ++ tailWord_5349687) baseStart_5349687 baseEnd_5349687 := by
    simpa [prefixWord, tailWord_5349687, baseEnd_5349687] using wordTrace_append hprefix tailTrace_5349687
  have hstable : (prefixWord ++ tailWord_5349687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349687).length < 2 ^ (prefixWord ++ tailWord_5349687).sum := by decide
  have hdescent : baseEnd_5349687 < baseStart_5349687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349707 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 4]
def baseStart_5349707 : Nat := 118140960795 + 5349707 * 2 ^ 59
def prefixEnd_5349707 : Nat := 4983230072969 + 3 ^ 40 * 5349707 * 2
def baseEnd_5349707 : Nat := 2746971051722405980459651

theorem tailTrace_5349707 : CollatzResearch.WordTrace tailWord_5349707 prefixEnd_5349707 2746971051722405980459651 := by
  unfold tailWord_5349707
  simp only [CollatzResearch.WordTrace]
  refine ⟨195119844029932671060743375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130079896019955114040495583 195119844029932671060743375)
  ·
    refine ⟨292679766044899006591115063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195119844029932671060743375 292679766044899006591115063)
    ·
      refine ⟨439019649067348509886672595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292679766044899006591115063 439019649067348509886672595)
      ·
        refine ⟨658529473601022764830008893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439019649067348509886672595 658529473601022764830008893)
        ·
          refine ⟨246948552600383536811253335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 658529473601022764830008893 246948552600383536811253335)
          ·
            refine ⟨370422828900575305216880003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246948552600383536811253335 370422828900575305216880003)
            ·
              refine ⟨555634243350862957825320005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370422828900575305216880003 555634243350862957825320005)
              ·
                refine ⟨104181420628286804592247501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 555634243350862957825320005 104181420628286804592247501)
                ·
                  refine ⟨39068032735607551722092813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 104181420628286804592247501 39068032735607551722092813)
                  ·
                    refine ⟨14650512275852831895784805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39068032735607551722092813 14650512275852831895784805)
                    ·
                      refine ⟨2746971051722405980459651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14650512275852831895784805 2746971051722405980459651)
                      ·
                        rfl

theorem cell23_5349707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 4].length) (baseStart_5349707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349707 prefixEnd_5349707 := by exact prefixLift 5349707
  have htrace : WordTrace (prefixWord ++ tailWord_5349707) baseStart_5349707 baseEnd_5349707 := by
    simpa [prefixWord, tailWord_5349707, baseEnd_5349707] using wordTrace_append hprefix tailTrace_5349707
  have hstable : (prefixWord ++ tailWord_5349707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349707).length < 2 ^ (prefixWord ++ tailWord_5349707).sum := by decide
  have hdescent : baseEnd_5349707 < baseStart_5349707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349741 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_5349741 : Nat := 118140960795 + 5349741 * 2 ^ 59
def prefixEnd_5349741 : Nat := 4983230072969 + 3 ^ 40 * 5349741 * 2
def baseEnd_5349741 : Nat := 2746988510064658847434495

theorem tailTrace_5349741 : CollatzResearch.WordTrace tailWord_5349741 prefixEnd_5349741 2746988510064658847434495 := by
  unfold tailWord_5349741
  simp only [CollatzResearch.WordTrace]
  refine ⟨195121084111809494867481077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130080722741206329911654051 195121084111809494867481077)
  ·
    refine ⟨18292601635482140143826351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195121084111809494867481077 18292601635482140143826351)
    ·
      refine ⟨27438902453223210215739527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18292601635482140143826351 27438902453223210215739527)
      ·
        refine ⟨41158353679834815323609291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27438902453223210215739527 41158353679834815323609291)
        ·
          refine ⟨61737530519752222985413937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41158353679834815323609291 61737530519752222985413937)
          ·
            refine ⟨46303147889814167239060453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61737530519752222985413937 46303147889814167239060453)
            ·
              refine ⟨8681840229340156357323835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46303147889814167239060453 8681840229340156357323835)
              ·
                refine ⟨13022760344010234535985753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8681840229340156357323835 13022760344010234535985753)
                ·
                  refine ⟨9767070258007675901989315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13022760344010234535985753 9767070258007675901989315)
                  ·
                    refine ⟨14650605387011513852983973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9767070258007675901989315 14650605387011513852983973)
                    ·
                      refine ⟨2746988510064658847434495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14650605387011513852983973 2746988510064658847434495)
                      ·
                        rfl

theorem cell23_5349741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_5349741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349741 prefixEnd_5349741 := by exact prefixLift 5349741
  have htrace : WordTrace (prefixWord ++ tailWord_5349741) baseStart_5349741 baseEnd_5349741 := by
    simpa [prefixWord, tailWord_5349741, baseEnd_5349741] using wordTrace_append hprefix tailTrace_5349741
  have hstable : (prefixWord ++ tailWord_5349741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349741).length < 2 ^ (prefixWord ++ tailWord_5349741).sum := by decide
  have hdescent : baseEnd_5349741 < baseStart_5349741 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349768 : List Nat := [2, 1, 3, 3, 1, 1, 3, 4, 1, 4]
def baseStart_5349768 : Nat := 118140960795 + 5349768 * 2 ^ 59
def prefixEnd_5349768 : Nat := 4983230072969 + 3 ^ 40 * 5349768 * 2
def baseEnd_5349768 : Nat := 915667458014110080598957

theorem tailTrace_5349768 : CollatzResearch.WordTrace tailWord_5349768 prefixEnd_5349768 915667458014110080598957 := by
  unfold tailWord_5349768
  simp only [CollatzResearch.WordTrace]
  refine ⟨97561034441355839239356979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130081379255141118985809305 97561034441355839239356979)
  ·
    refine ⟨146341551662033758859035469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97561034441355839239356979 146341551662033758859035469)
    ·
      refine ⟨54878081873262659572138301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146341551662033758859035469 54878081873262659572138301)
      ·
        refine ⟨20579280702473497339551863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54878081873262659572138301 20579280702473497339551863)
        ·
          refine ⟨30868921053710246009327795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20579280702473497339551863 30868921053710246009327795)
          ·
            refine ⟨46303381580565369013991693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30868921053710246009327795 46303381580565369013991693)
            ·
              refine ⟨17363768092712013380246885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46303381580565369013991693 17363768092712013380246885)
              ·
                refine ⟨3255706517383502508796291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17363768092712013380246885 3255706517383502508796291)
                ·
                  refine ⟨4883559776075253763194437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255706517383502508796291 4883559776075253763194437)
                  ·
                    refine ⟨915667458014110080598957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4883559776075253763194437 915667458014110080598957)
                    ·
                      rfl

theorem cell23_5349768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 4, 1, 4].length) (baseStart_5349768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349768 prefixEnd_5349768 := by exact prefixLift 5349768
  have htrace : WordTrace (prefixWord ++ tailWord_5349768) baseStart_5349768 baseEnd_5349768 := by
    simpa [prefixWord, tailWord_5349768, baseEnd_5349768] using wordTrace_append hprefix tailTrace_5349768
  have hstable : (prefixWord ++ tailWord_5349768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349768).length < 2 ^ (prefixWord ++ tailWord_5349768).sum := by decide
  have hdescent : baseEnd_5349768 < baseStart_5349768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349777 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 1, 11]
def baseStart_5349777 : Nat := 118140960795 + 5349777 * 2 ^ 59
def prefixEnd_5349777 : Nat := 4983230072969 + 3 ^ 40 * 5349777 * 2
def baseEnd_5349777 : Nat := 915668998456073568861443

theorem tailTrace_5349777 : CollatzResearch.WordTrace tailWord_5349777 prefixEnd_5349777 915668998456073568861443 := by
  unfold tailWord_5349777
  simp only [CollatzResearch.WordTrace]
  refine ⟨195122397139679073015791585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130081598093119382010527723 195122397139679073015791585)
  ·
    refine ⟨146341797854759304761843689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195122397139679073015791585 146341797854759304761843689)
    ·
      refine ⟨109756348391069478571382767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146341797854759304761843689 109756348391069478571382767)
      ·
        refine ⟨164634522586604217857074151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109756348391069478571382767 164634522586604217857074151)
        ·
          refine ⟨246951783879906326785611227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164634522586604217857074151 246951783879906326785611227)
          ·
            refine ⟨370427675819859490178416841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246951783879906326785611227 370427675819859490178416841)
            ·
              refine ⟨277820756864894617633812631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370427675819859490178416841 277820756864894617633812631)
              ·
                refine ⟨416731135297341926450718947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277820756864894617633812631 416731135297341926450718947)
                ·
                  refine ⟨625096702946012889676078421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 416731135297341926450718947 625096702946012889676078421)
                  ·
                    refine ⟨915668998456073568861443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 625096702946012889676078421 915668998456073568861443)
                    ·
                      rfl

theorem cell23_5349777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_5349777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349777 prefixEnd_5349777 := by exact prefixLift 5349777
  have htrace : WordTrace (prefixWord ++ tailWord_5349777) baseStart_5349777 baseEnd_5349777 := by
    simpa [prefixWord, tailWord_5349777, baseEnd_5349777] using wordTrace_append hprefix tailTrace_5349777
  have hstable : (prefixWord ++ tailWord_5349777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349777).length < 2 ^ (prefixWord ++ tailWord_5349777).sum := by decide
  have hdescent : baseEnd_5349777 < baseStart_5349777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349841 : List Nat := [1, 2, 2, 1, 2, 1, 1, 7, 2, 4]
def baseStart_5349841 : Nat := 118140960795 + 5349841 * 2 ^ 59
def prefixEnd_5349841 : Nat := 4983230072969 + 3 ^ 40 * 5349841 * 2
def baseEnd_5349841 : Nat := 915679952710036152061345

theorem tailTrace_5349841 : CollatzResearch.WordTrace tailWord_5349841 prefixEnd_5349841 915679952710036152061345 := by
  unfold tailWord_5349841
  simp only [CollatzResearch.WordTrace]
  refine ⟨195124731411447211946121377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130083154274298141297414251 195124731411447211946121377)
  ·
    refine ⟨146343548558585408959591033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195124731411447211946121377 146343548558585408959591033)
    ·
      refine ⟨109757661418939056719693275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146343548558585408959591033 109757661418939056719693275)
      ·
        refine ⟨164636492128408585079539913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109757661418939056719693275 164636492128408585079539913)
        ·
          refine ⟨123477369096306438809654935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164636492128408585079539913 123477369096306438809654935)
          ·
            refine ⟨185216053644459658214482403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123477369096306438809654935 185216053644459658214482403)
            ·
              refine ⟨277824080466689487321723605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 185216053644459658214482403 277824080466689487321723605)
              ·
                refine ⟨6511501885938034859102897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 277824080466689487321723605 6511501885938034859102897)
                ·
                  refine ⟨4883626414453526144327173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6511501885938034859102897 4883626414453526144327173)
                  ·
                    refine ⟨915679952710036152061345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4883626414453526144327173 915679952710036152061345)
                    ·
                      rfl

theorem cell23_5349841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_5349841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349841 prefixEnd_5349841 := by exact prefixLift 5349841
  have htrace : WordTrace (prefixWord ++ tailWord_5349841) baseStart_5349841 baseEnd_5349841 := by
    simpa [prefixWord, tailWord_5349841, baseEnd_5349841] using wordTrace_append hprefix tailTrace_5349841
  have hstable : (prefixWord ++ tailWord_5349841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349841).length < 2 ^ (prefixWord ++ tailWord_5349841).sum := by decide
  have hdescent : baseEnd_5349841 < baseStart_5349841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349859 : List Nat := [1, 1, 1, 6, 4, 1, 1, 3, 1, 1, 3]
def baseStart_5349859 : Nat := 118140960795 + 5349859 * 2 ^ 59
def prefixEnd_5349859 : Nat := 4983230072969 + 3 ^ 40 * 5349859 * 2
def baseEnd_5349859 : Nat := 2747049100781889385758953

theorem tailTrace_5349859 : CollatzResearch.WordTrace tailWord_5349859 prefixEnd_5349859 2747049100781889385758953 := by
  unfold tailWord_5349859
  simp only [CollatzResearch.WordTrace]
  refine ⟨195125387925382001020276631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130083591950254667346851087 195125387925382001020276631)
  ·
    refine ⟨292688081888073001530414947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195125387925382001020276631 292688081888073001530414947)
    ·
      refine ⟨439032122832109502295622421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292688081888073001530414947 439032122832109502295622421)
      ·
        refine ⟨20579630757755132920107301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 439032122832109502295622421 20579630757755132920107301)
        ·
          refine ⟨3858680767079087422520119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20579630757755132920107301 3858680767079087422520119)
          ·
            refine ⟨5788021150618631133780179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3858680767079087422520119 5788021150618631133780179)
            ·
              refine ⟨8682031725927946700670269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5788021150618631133780179 8682031725927946700670269)
              ·
                refine ⟨3255761897222980012751351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8682031725927946700670269 3255761897222980012751351)
                ·
                  refine ⟨4883642845834470019127027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255761897222980012751351 4883642845834470019127027)
                  ·
                    refine ⟨7325464268751705028690541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4883642845834470019127027 7325464268751705028690541)
                    ·
                      refine ⟨2747049100781889385758953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7325464268751705028690541 2747049100781889385758953)
                      ·
                        rfl

theorem cell23_5349859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_5349859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349859 prefixEnd_5349859 := by exact prefixLift 5349859
  have htrace : WordTrace (prefixWord ++ tailWord_5349859) baseStart_5349859 baseEnd_5349859 := by
    simpa [prefixWord, tailWord_5349859, baseEnd_5349859] using wordTrace_append hprefix tailTrace_5349859
  have hstable : (prefixWord ++ tailWord_5349859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349859).length < 2 ^ (prefixWord ++ tailWord_5349859).sum := by decide
  have hdescent : baseEnd_5349859 < baseStart_5349859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349865 : List Nat := [1, 2, 1, 1, 1, 2, 1, 9, 1, 2, 2]
def baseStart_5349865 : Nat := 118140960795 + 5349865 * 2 ^ 59
def prefixEnd_5349865 : Nat := 4983230072969 + 3 ^ 40 * 5349865 * 2
def baseEnd_5349865 : Nat := 2747052181665816362283925

theorem tailTrace_5349865 : CollatzResearch.WordTrace tailWord_5349865 prefixEnd_5349865 2747052181665816362283925 := by
  unfold tailWord_5349865
  simp only [CollatzResearch.WordTrace]
  refine ⟨195125606763360264044995049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130083737842240176029996699 195125606763360264044995049)
  ·
    refine ⟨146344205072520198033746287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195125606763360264044995049 146344205072520198033746287)
    ·
      refine ⟨219516307608780297050619431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146344205072520198033746287 219516307608780297050619431)
      ·
        refine ⟨329274461413170445575929147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219516307608780297050619431 329274461413170445575929147)
        ·
          refine ⟨493911692119755668363893721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329274461413170445575929147 493911692119755668363893721)
          ·
            refine ⟨370433769089816751272920291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 493911692119755668363893721 370433769089816751272920291)
            ·
              refine ⟨555650653634725126909380437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370433769089816751272920291 555650653634725126909380437)
              ·
                refine ⟨3255765548640967540484651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 555650653634725126909380437 3255765548640967540484651)
                ·
                  refine ⟨4883648322961451310726977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255765548640967540484651 4883648322961451310726977)
                  ·
                    refine ⟨3662736242221088483045233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4883648322961451310726977 3662736242221088483045233)
                    ·
                      refine ⟨2747052181665816362283925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662736242221088483045233 2747052181665816362283925)
                      ·
                        rfl

theorem cell23_5349865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 1, 2, 2].length) (baseStart_5349865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349865 prefixEnd_5349865 := by exact prefixLift 5349865
  have htrace : WordTrace (prefixWord ++ tailWord_5349865) baseStart_5349865 baseEnd_5349865 := by
    simpa [prefixWord, tailWord_5349865, baseEnd_5349865] using wordTrace_append hprefix tailTrace_5349865
  have hstable : (prefixWord ++ tailWord_5349865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349865).length < 2 ^ (prefixWord ++ tailWord_5349865).sum := by decide
  have hdescent : baseEnd_5349865 < baseStart_5349865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349884 : List Nat := [2, 2, 2, 1, 2, 1, 1, 3, 2, 7]
def baseStart_5349884 : Nat := 118140960795 + 5349884 * 2 ^ 59
def prefixEnd_5349884 : Nat := 4983230072969 + 3 ^ 40 * 5349884 * 2
def baseEnd_5349884 : Nat := 915687312599417262648779

theorem tailTrace_5349884 : CollatzResearch.WordTrace tailWord_5349884 prefixEnd_5349884 915687312599417262648779 := by
  unfold tailWord_5349884
  simp only [CollatzResearch.WordTrace]
  refine ⟨97563149875145715144968353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130084199833527620193291137 97563149875145715144968353)
  ·
    refine ⟨73172362406359286358726265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97563149875145715144968353 73172362406359286358726265)
    ·
      refine ⟨54879271804769464769044699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73172362406359286358726265 54879271804769464769044699)
      ·
        refine ⟨82318907707154197153567049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54879271804769464769044699 82318907707154197153567049)
        ·
          refine ⟨61739180780365647865175287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 82318907707154197153567049 61739180780365647865175287)
          ·
            refine ⟨92608771170548471797762931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61739180780365647865175287 92608771170548471797762931)
            ·
              refine ⟨138913156755822707696644397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92608771170548471797762931 138913156755822707696644397)
              ·
                refine ⟨52092433783433515386241649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138913156755822707696644397 52092433783433515386241649)
                ·
                  refine ⟨39069325337575136539681237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52092433783433515386241649 39069325337575136539681237)
                  ·
                    refine ⟨915687312599417262648779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39069325337575136539681237 915687312599417262648779)
                    ·
                      rfl

theorem cell23_5349884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_5349884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349884 prefixEnd_5349884 := by exact prefixLift 5349884
  have htrace : WordTrace (prefixWord ++ tailWord_5349884) baseStart_5349884 baseEnd_5349884 := by
    simpa [prefixWord, tailWord_5349884, baseEnd_5349884] using wordTrace_append hprefix tailTrace_5349884
  have hstable : (prefixWord ++ tailWord_5349884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349884).length < 2 ^ (prefixWord ++ tailWord_5349884).sum := by decide
  have hdescent : baseEnd_5349884 < baseStart_5349884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349892 : List Nat := [2, 3, 2, 3, 1, 3, 2, 1, 2, 4]
def baseStart_5349892 : Nat := 118140960795 + 5349892 * 2 ^ 59
def prefixEnd_5349892 : Nat := 4983230072969 + 3 ^ 40 * 5349892 * 2
def baseEnd_5349892 : Nat := 915688681881162585548767

theorem tailTrace_5349892 : CollatzResearch.WordTrace tailWord_5349892 prefixEnd_5349892 915688681881162585548767 := by
  unfold tailWord_5349892
  simp only [CollatzResearch.WordTrace]
  refine ⟨97563295767131223828113965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130084394356174965104151953 97563295767131223828113965)
  ·
    refine ⟨36586235912674208935542737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97563295767131223828113965 36586235912674208935542737)
    ·
      refine ⟨27439676934505656701657053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36586235912674208935542737 27439676934505656701657053)
      ·
        refine ⟨10289878850439621263121395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27439676934505656701657053 10289878850439621263121395)
        ·
          refine ⟨15434818275659431894682093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10289878850439621263121395 15434818275659431894682093)
          ·
            refine ⟨5788056853372286960505785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15434818275659431894682093 5788056853372286960505785)
            ·
              refine ⟨4341042640029215220379339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5788056853372286960505785 4341042640029215220379339)
              ·
                refine ⟨6511563960043822830569009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4341042640029215220379339 6511563960043822830569009)
                ·
                  refine ⟨4883672970032867122926757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6511563960043822830569009 4883672970032867122926757)
                  ·
                    refine ⟨915688681881162585548767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4883672970032867122926757 915688681881162585548767)
                    ·
                      rfl

theorem cell23_5349892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_5349892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349892 prefixEnd_5349892 := by exact prefixLift 5349892
  have htrace : WordTrace (prefixWord ++ tailWord_5349892) baseStart_5349892 baseEnd_5349892 := by
    simpa [prefixWord, tailWord_5349892, baseEnd_5349892] using wordTrace_append hprefix tailTrace_5349892
  have hstable : (prefixWord ++ tailWord_5349892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349892).length < 2 ^ (prefixWord ++ tailWord_5349892).sum := by decide
  have hdescent : baseEnd_5349892 < baseStart_5349892 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349933 : List Nat := [1, 5, 4, 1, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5349933 : Nat := 118140960795 + 5349933 * 2 ^ 59
def prefixEnd_5349933 : Nat := 4983230072969 + 3 ^ 40 * 5349933 * 2
def baseEnd_5349933 : Nat := 2747087098350322096233613

theorem tailTrace_5349933 : CollatzResearch.WordTrace tailWord_5349933 prefixEnd_5349933 2747087098350322096233613 := by
  unfold tailWord_5349933
  simp only [CollatzResearch.WordTrace]
  refine ⟨195128086927113911658470453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130085391284742607772313635 195128086927113911658470453)
  ·
    refine ⟨18293258149416929217981605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 195128086927113911658470453 18293258149416929217981605)
    ·
      refine ⟨3429985903015674228371551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18293258149416929217981605 3429985903015674228371551)
      ·
        refine ⟨5144978854523511342557327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3429985903015674228371551 5144978854523511342557327)
        ·
          refine ⟨7717468281785267013835991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5144978854523511342557327 7717468281785267013835991)
          ·
            refine ⟨11576202422677900520753987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7717468281785267013835991 11576202422677900520753987)
            ·
              refine ⟨17364303634016850781130981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11576202422677900520753987 17364303634016850781130981)
              ·
                refine ⟨3255806931378159521462059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17364303634016850781130981 3255806931378159521462059)
                ·
                  refine ⟨4883710397067239282193089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255806931378159521462059 4883710397067239282193089)
                  ·
                    refine ⟨3662782797800429461644817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4883710397067239282193089 3662782797800429461644817)
                    ·
                      refine ⟨2747087098350322096233613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662782797800429461644817 2747087098350322096233613)
                      ·
                        rfl

theorem cell23_5349933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5349933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349933 prefixEnd_5349933 := by exact prefixLift 5349933
  have htrace : WordTrace (prefixWord ++ tailWord_5349933) baseStart_5349933 baseEnd_5349933 := by
    simpa [prefixWord, tailWord_5349933, baseEnd_5349933] using wordTrace_append hprefix tailTrace_5349933
  have hstable : (prefixWord ++ tailWord_5349933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349933).length < 2 ^ (prefixWord ++ tailWord_5349933).sum := by decide
  have hdescent : baseEnd_5349933 < baseStart_5349933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349941 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_5349941 : Nat := 118140960795 + 5349941 * 2 ^ 59
def prefixEnd_5349941 : Nat := 4983230072969 + 3 ^ 40 * 5349941 * 2
def baseEnd_5349941 : Nat := 2747091206195558064933575

theorem tailTrace_5349941 : CollatzResearch.WordTrace tailWord_5349941 prefixEnd_5349941 2747091206195558064933575 := by
  unfold tailWord_5349941
  simp only [CollatzResearch.WordTrace]
  refine ⟨195128378711084929024761677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130085585807389952683174451 195128378711084929024761677)
  ·
    refine ⟨73173142016656848384285629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195128378711084929024761677 73173142016656848384285629)
    ·
      refine ⟨27439928256246318144107111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73173142016656848384285629 27439928256246318144107111)
      ·
        refine ⟨41159892384369477216160667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27439928256246318144107111 41159892384369477216160667)
        ·
          refine ⟨61739838576554215824241001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41159892384369477216160667 61739838576554215824241001)
          ·
            refine ⟨46304878932415661868180751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61739838576554215824241001 46304878932415661868180751)
            ·
              refine ⟨69457318398623492802271127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46304878932415661868180751 69457318398623492802271127)
              ·
                refine ⟨104185977597935239203406691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 69457318398623492802271127 104185977597935239203406691)
                ·
                  refine ⟨156278966396902858805110037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 104185977597935239203406691 156278966396902858805110037)
                  ·
                    refine ⟨7325576549854821506489533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 156278966396902858805110037 7325576549854821506489533)
                    ·
                      refine ⟨2747091206195558064933575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7325576549854821506489533 2747091206195558064933575)
                      ·
                        rfl

theorem cell23_5349941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_5349941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349941 prefixEnd_5349941 := by exact prefixLift 5349941
  have htrace : WordTrace (prefixWord ++ tailWord_5349941) baseStart_5349941 baseEnd_5349941 := by
    simpa [prefixWord, tailWord_5349941, baseEnd_5349941] using wordTrace_append hprefix tailTrace_5349941
  have hstable : (prefixWord ++ tailWord_5349941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349941).length < 2 ^ (prefixWord ++ tailWord_5349941).sum := by decide
  have hdescent : baseEnd_5349941 < baseStart_5349941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349951 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 4]
def baseStart_5349951 : Nat := 118140960795 + 5349951 * 2 ^ 59
def prefixEnd_5349951 : Nat := 4983230072969 + 3 ^ 40 * 5349951 * 2
def baseEnd_5349951 : Nat := 2747096341002103025808529

theorem tailTrace_5349951 : CollatzResearch.WordTrace tailWord_5349951 prefixEnd_5349951 2747096341002103025808529 := by
  unfold tailWord_5349951
  simp only [CollatzResearch.WordTrace]
  refine ⟨195128743441048700732625707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130085828960699133821750471 195128743441048700732625707)
  ·
    refine ⟨292693115161573051098938561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195128743441048700732625707 292693115161573051098938561)
    ·
      refine ⟨219519836371179788324203921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 292693115161573051098938561 219519836371179788324203921)
      ·
        refine ⟨164639877278384841243152941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219519836371179788324203921 164639877278384841243152941)
        ·
          refine ⟨61739953979394315466182353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164639877278384841243152941 61739953979394315466182353)
          ·
            refine ⟨46304965484545736599636765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61739953979394315466182353 46304965484545736599636765)
            ·
              refine ⟨17364362056704651224863787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46304965484545736599636765 17364362056704651224863787)
              ·
                refine ⟨26046543085056976837295681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17364362056704651224863787 26046543085056976837295681)
                ·
                  refine ⟨19534907313792732627971761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26046543085056976837295681 19534907313792732627971761)
                  ·
                    refine ⟨14651180485344549470978821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19534907313792732627971761 14651180485344549470978821)
                    ·
                      refine ⟨2747096341002103025808529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14651180485344549470978821 2747096341002103025808529)
                      ·
                        rfl

theorem cell23_5349951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_5349951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349951 prefixEnd_5349951 := by exact prefixLift 5349951
  have htrace : WordTrace (prefixWord ++ tailWord_5349951) baseStart_5349951 baseEnd_5349951 := by
    simpa [prefixWord, tailWord_5349951, baseEnd_5349951] using wordTrace_append hprefix tailTrace_5349951
  have hstable : (prefixWord ++ tailWord_5349951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349951).length < 2 ^ (prefixWord ++ tailWord_5349951).sum := by decide
  have hdescent : baseEnd_5349951 < baseStart_5349951 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349989 : List Nat := [1, 3, 1, 3, 4, 2, 1, 2, 2, 2, 2]
def baseStart_5349989 : Nat := 118140960795 + 5349989 * 2 ^ 59
def prefixEnd_5349989 : Nat := 4983230072969 + 3 ^ 40 * 5349989 * 2
def baseEnd_5349989 : Nat := 2747115853266973877133355

theorem tailTrace_5349989 : CollatzResearch.WordTrace tailWord_5349989 prefixEnd_5349989 2747115853266973877133355 := by
  unfold tailWord_5349989
  simp only [CollatzResearch.WordTrace]
  refine ⟨195130129414911033222509021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130086752943274022148339347 195130129414911033222509021)
  ·
    refine ⟨73173798530591637458440883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195130129414911033222509021 73173798530591637458440883)
    ·
      refine ⟨109760697795887456187661325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73173798530591637458440883 109760697795887456187661325)
      ·
        refine ⟨41160261673457796070372997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109760697795887456187661325 41160261673457796070372997)
        ·
          refine ⟨7717549063773336763194937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41160261673457796070372997 7717549063773336763194937)
          ·
            refine ⟨5788161797830002572396203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7717549063773336763194937 5788161797830002572396203)
            ·
              refine ⟨8682242696745003858594305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5788161797830002572396203 8682242696745003858594305)
              ·
                refine ⟨6511682022558752893945729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8682242696745003858594305 6511682022558752893945729)
                ·
                  refine ⟨4883761516919064670459297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6511682022558752893945729 4883761516919064670459297)
                  ·
                    refine ⟨3662821137689298502844473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4883761516919064670459297 3662821137689298502844473)
                    ·
                      refine ⟨2747115853266973877133355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662821137689298502844473 2747115853266973877133355)
                      ·
                        rfl

theorem cell23_5349989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 2, 2, 2, 2].length) (baseStart_5349989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349989 prefixEnd_5349989 := by exact prefixLift 5349989
  have htrace : WordTrace (prefixWord ++ tailWord_5349989) baseStart_5349989 baseEnd_5349989 := by
    simpa [prefixWord, tailWord_5349989, baseEnd_5349989] using wordTrace_append hprefix tailTrace_5349989
  have hstable : (prefixWord ++ tailWord_5349989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349989).length < 2 ^ (prefixWord ++ tailWord_5349989).sum := by decide
  have hdescent : baseEnd_5349989 < baseStart_5349989 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5349991 : List Nat := [1, 1, 5, 1, 1, 1, 1, 3, 4, 5]
def baseStart_5349991 : Nat := 118140960795 + 5349991 * 2 ^ 59
def prefixEnd_5349991 : Nat := 4983230072969 + 3 ^ 40 * 5349991 * 2
def baseEnd_5349991 : Nat := 915705626742760956436115

theorem tailTrace_5349991 : CollatzResearch.WordTrace tailWord_5349991 prefixEnd_5349991 915705626742760956436115 := by
  unfold tailWord_5349991
  simp only [CollatzResearch.WordTrace]
  refine ⟨195130202360903787564081827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130086801573935858376054551 195130202360903787564081827)
  ·
    refine ⟨292695303541355681346122741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195130202360903787564081827 292695303541355681346122741)
    ·
      refine ⟨27440184707002095126199007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 292695303541355681346122741 27440184707002095126199007)
      ·
        refine ⟨41160277060503142689298511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27440184707002095126199007 41160277060503142689298511)
        ·
          refine ⟨61740415590754714033947767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41160277060503142689298511 61740415590754714033947767)
          ·
            refine ⟨92610623386132071050921651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 61740415590754714033947767 92610623386132071050921651)
            ·
              refine ⟨138915935079198106576382477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 92610623386132071050921651 138915935079198106576382477)
              ·
                refine ⟨52093475654699289966143429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 138915935079198106576382477 52093475654699289966143429)
                ·
                  refine ⟨9767526685256116868651893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52093475654699289966143429 9767526685256116868651893)
                  ·
                    refine ⟨915705626742760956436115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9767526685256116868651893 915705626742760956436115)
                    ·
                      rfl

theorem cell23_5349991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_5349991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5349991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5349991 prefixEnd_5349991 := by exact prefixLift 5349991
  have htrace : WordTrace (prefixWord ++ tailWord_5349991) baseStart_5349991 baseEnd_5349991 := by
    simpa [prefixWord, tailWord_5349991, baseEnd_5349991] using wordTrace_append hprefix tailTrace_5349991
  have hstable : (prefixWord ++ tailWord_5349991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5349991).length < 2 ^ (prefixWord ++ tailWord_5349991).sum := by decide
  have hdescent : baseEnd_5349991 < baseStart_5349991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5349991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350006 : List Nat := [5, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2]
def baseStart_5350006 : Nat := 118140960795 + 5350006 * 2 ^ 59
def prefixEnd_5350006 : Nat := 4983230072969 + 3 ^ 40 * 5350006 * 2
def baseEnd_5350006 : Nat := 2747124582438100310620777

theorem tailTrace_5350006 : CollatzResearch.WordTrace tailWord_5350006 prefixEnd_5350006 2747124582438100310620777 := by
  unfold tailWord_5350006
  simp only [CollatzResearch.WordTrace]
  refine ⟨12195671840990590320367367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130087166303899630083918581 12195671840990590320367367)
  ·
    refine ⟨18293507761485885480551051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12195671840990590320367367 18293507761485885480551051)
    ·
      refine ⟨27440261642228828220826577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18293507761485885480551051 27440261642228828220826577)
      ·
        refine ⟨20580196231671621165619933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27440261642228828220826577 20580196231671621165619933)
        ·
          refine ⟨7717573586876857937107475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20580196231671621165619933 7717573586876857937107475)
          ·
            refine ⟨11576360380315286905661213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7717573586876857937107475 11576360380315286905661213)
            ·
              refine ⟨4341135142618232589622955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11576360380315286905661213 4341135142618232589622955)
              ·
                refine ⟨6511702713927348884434433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4341135142618232589622955 6511702713927348884434433)
                ·
                  refine ⟨4883777035445511663325825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6511702713927348884434433 4883777035445511663325825)
                  ·
                    refine ⟨3662832776584133747494369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4883777035445511663325825 3662832776584133747494369)
                    ·
                      refine ⟨2747124582438100310620777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662832776584133747494369 2747124582438100310620777)
                      ·
                        rfl

theorem cell23_5350006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_5350006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350006 prefixEnd_5350006 := by exact prefixLift 5350006
  have htrace : WordTrace (prefixWord ++ tailWord_5350006) baseStart_5350006 baseEnd_5350006 := by
    simpa [prefixWord, tailWord_5350006, baseEnd_5350006] using wordTrace_append hprefix tailTrace_5350006
  have hstable : (prefixWord ++ tailWord_5350006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350006).length < 2 ^ (prefixWord ++ tailWord_5350006).sum := by decide
  have hdescent : baseEnd_5350006 < baseStart_5350006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350011 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 4]
def baseStart_5350011 : Nat := 118140960795 + 5350011 * 2 ^ 59
def prefixEnd_5350011 : Nat := 4983230072969 + 3 ^ 40 * 5350011 * 2
def baseEnd_5350011 : Nat := 2747127149841372791058253

theorem tailTrace_5350011 : CollatzResearch.WordTrace tailWord_5350011 prefixEnd_5350011 2747127149841372791058253 := by
  unfold tailWord_5350011
  simp only [CollatzResearch.WordTrace]
  refine ⟨195130931820831330979809887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130087287880554220653206591 195130931820831330979809887)
  ·
    refine ⟨292696397731246996469714831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195130931820831330979809887 292696397731246996469714831)
    ·
      refine ⟨439044596596870494704572247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292696397731246996469714831 439044596596870494704572247)
      ·
        refine ⟨658566894895305742056858371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439044596596870494704572247 658566894895305742056858371)
        ·
          refine ⟨987850342342958613085287557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658566894895305742056858371 987850342342958613085287557)
          ·
            refine ⟨185221939189304739953491417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 987850342342958613085287557 185221939189304739953491417)
            ·
              refine ⟨138916454391978554965118563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185221939189304739953491417 138916454391978554965118563)
              ·
                refine ⟨208374681587967832447677845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 138916454391978554965118563 208374681587967832447677845)
                ·
                  refine ⟨9767563199435992145984899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 208374681587967832447677845 9767563199435992145984899)
                  ·
                    refine ⟨14651344799153988218977349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9767563199435992145984899 14651344799153988218977349)
                    ·
                      refine ⟨2747127149841372791058253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14651344799153988218977349 2747127149841372791058253)
                      ·
                        rfl

theorem cell23_5350011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 4].length) (baseStart_5350011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350011 prefixEnd_5350011 := by exact prefixLift 5350011
  have htrace : WordTrace (prefixWord ++ tailWord_5350011) baseStart_5350011 baseEnd_5350011 := by
    simpa [prefixWord, tailWord_5350011, baseEnd_5350011] using wordTrace_append hprefix tailTrace_5350011
  have hstable : (prefixWord ++ tailWord_5350011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350011).length < 2 ^ (prefixWord ++ tailWord_5350011).sum := by decide
  have hdescent : baseEnd_5350011 < baseStart_5350011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350028 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 4, 4, 2]
def baseStart_5350028 : Nat := 118140960795 + 5350028 * 2 ^ 59
def prefixEnd_5350028 : Nat := 4983230072969 + 3 ^ 40 * 5350028 * 2
def baseEnd_5350028 : Nat := 2747135879012499224545675

theorem tailTrace_5350028 : CollatzResearch.WordTrace tailWord_5350028 prefixEnd_5350028 2747135879012499224545675 := by
  unfold tailWord_5350028
  simp only [CollatzResearch.WordTrace]
  refine ⟨97565775930884871441589369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130087701241179828588785825 97565775930884871441589369)
  ·
    refine ⟨73174331948163653581192027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97565775930884871441589369 73174331948163653581192027)
    ·
      refine ⟨109761497922245480371788041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73174331948163653581192027 109761497922245480371788041)
      ·
        refine ⟨82321123441684110278841031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 109761497922245480371788041 82321123441684110278841031)
        ·
          refine ⟨123481685162526165418261547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82321123441684110278841031 123481685162526165418261547)
          ·
            refine ⟨185222527743789248127392321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123481685162526165418261547 185222527743789248127392321)
            ·
              refine ⟨138916895807841936095544241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185222527743789248127392321 138916895807841936095544241)
              ·
                refine ⟨104187671855881452071658181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 138916895807841936095544241 104187671855881452071658181)
                ·
                  refine ⟨19535188472977772263435909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 104187671855881452071658181 19535188472977772263435909)
                  ·
                    refine ⟨3662847838683332299394233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19535188472977772263435909 3662847838683332299394233)
                    ·
                      refine ⟨2747135879012499224545675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662847838683332299394233 2747135879012499224545675)
                      ·
                        rfl

theorem cell23_5350028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 4, 4, 2].length) (baseStart_5350028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350028 prefixEnd_5350028 := by exact prefixLift 5350028
  have htrace : WordTrace (prefixWord ++ tailWord_5350028) baseStart_5350028 baseEnd_5350028 := by
    simpa [prefixWord, tailWord_5350028, baseEnd_5350028] using wordTrace_append hprefix tailTrace_5350028
  have hstable : (prefixWord ++ tailWord_5350028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350028).length < 2 ^ (prefixWord ++ tailWord_5350028).sum := by decide
  have hdescent : baseEnd_5350028 < baseStart_5350028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350105 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 2, 3, 2]
def baseStart_5350105 : Nat := 118140960795 + 5350105 * 2 ^ 59
def prefixEnd_5350105 : Nat := 4983230072969 + 3 ^ 40 * 5350105 * 2
def baseEnd_5350105 : Nat := 2747175417022895423282821

theorem tailTrace_5350105 : CollatzResearch.WordTrace tailWord_5350105 prefixEnd_5350105 2747175417022895423282821 := by
  unfold tailWord_5350105
  simp only [CollatzResearch.WordTrace]
  refine ⟨195134360282490785033731769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130089573521660523355821179 195134360282490785033731769)
  ·
    refine ⟨146350770211868088775298827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195134360282490785033731769 146350770211868088775298827)
    ·
      refine ⟨219526155317802133162948241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146350770211868088775298827 219526155317802133162948241)
      ·
        refine ⟨164644616488351599872211181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219526155317802133162948241 164644616488351599872211181)
        ·
          refine ⟨61741731183131849952079193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 164644616488351599872211181 61741731183131849952079193)
          ·
            refine ⟨46306298387348887464059395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61741731183131849952079193 46306298387348887464059395)
            ·
              refine ⟨69459447581023331196089093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46306298387348887464059395 69459447581023331196089093)
              ·
                refine ⟨13023646421441874599266705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 69459447581023331196089093 13023646421441874599266705)
                ·
                  refine ⟨9767734816081405949450029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13023646421441874599266705 9767734816081405949450029)
                  ·
                    refine ⟨3662900556030527231043761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9767734816081405949450029 3662900556030527231043761)
                    ·
                      refine ⟨2747175417022895423282821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3662900556030527231043761 2747175417022895423282821)
                      ·
                        rfl

theorem cell23_5350105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 2, 3, 2].length) (baseStart_5350105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350105 prefixEnd_5350105 := by exact prefixLift 5350105
  have htrace : WordTrace (prefixWord ++ tailWord_5350105) baseStart_5350105 baseEnd_5350105 := by
    simpa [prefixWord, tailWord_5350105, baseEnd_5350105] using wordTrace_append hprefix tailTrace_5350105
  have hstable : (prefixWord ++ tailWord_5350105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350105).length < 2 ^ (prefixWord ++ tailWord_5350105).sum := by decide
  have hdescent : baseEnd_5350105 < baseStart_5350105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350128 : List Nat := [2, 1, 1, 1, 3, 1, 6, 1, 1, 6]
def baseStart_5350128 : Nat := 118140960795 + 5350128 * 2 ^ 59
def prefixEnd_5350128 : Nat := 4983230072969 + 3 ^ 40 * 5350128 * 2
def baseEnd_5350128 : Nat := 915729075692649611098405

theorem tailTrace_5350128 : CollatzResearch.WordTrace tailWord_5350128 prefixEnd_5350128 915729075692649611098405 := by
  unfold tailWord_5350128
  simp only [CollatzResearch.WordTrace]
  refine ⟨97567599580703729980909519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130090132774271639974546025 97567599580703729980909519)
  ·
    refine ⟨146351399371055594971364279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97567599580703729980909519 146351399371055594971364279)
    ·
      refine ⟨219527099056583392457046419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146351399371055594971364279 219527099056583392457046419)
      ·
        refine ⟨329290648584875088685569629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219527099056583392457046419 329290648584875088685569629)
        ·
          refine ⟨123483993219328158257088611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 329290648584875088685569629 123483993219328158257088611)
          ·
            refine ⟨185225989828992237385632917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123483993219328158257088611 185225989828992237385632917)
            ·
              refine ⟨8682468273234011127451543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 185225989828992237385632917 8682468273234011127451543)
              ·
                refine ⟨13023702409851016691177315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8682468273234011127451543 13023702409851016691177315)
                ·
                  refine ⟨19535553614776525036765973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13023702409851016691177315 19535553614776525036765973)
                  ·
                    refine ⟨915729075692649611098405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19535553614776525036765973 915729075692649611098405)
                    ·
                      rfl

theorem cell23_5350128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 6, 1, 1, 6].length) (baseStart_5350128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350128 prefixEnd_5350128 := by exact prefixLift 5350128
  have htrace : WordTrace (prefixWord ++ tailWord_5350128) baseStart_5350128 baseEnd_5350128 := by
    simpa [prefixWord, tailWord_5350128, baseEnd_5350128] using wordTrace_append hprefix tailTrace_5350128
  have hstable : (prefixWord ++ tailWord_5350128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350128).length < 2 ^ (prefixWord ++ tailWord_5350128).sum := by decide
  have hdescent : baseEnd_5350128 < baseStart_5350128 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350133 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5350133 : Nat := 118140960795 + 5350133 * 2 ^ 59
def prefixEnd_5350133 : Nat := 4983230072969 + 3 ^ 40 * 5350133 * 2
def baseEnd_5350133 : Nat := 2747189794481221313732693

theorem tailTrace_5350133 : CollatzResearch.WordTrace tailWord_5350133 prefixEnd_5350133 2747189794481221313732693 := by
  unfold tailWord_5350133
  simp only [CollatzResearch.WordTrace]
  refine ⟨195135381526389345815751053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130090254350926230543834035 195135381526389345815751053)
  ·
    refine ⟨73175768072396004680906645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195135381526389345815751053 73175768072396004680906645)
    ·
      refine ⟨3430114128393562719417499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 73175768072396004680906645 3430114128393562719417499)
      ·
        refine ⟨5145171192590344079126249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3430114128393562719417499 5145171192590344079126249)
        ·
          refine ⟨3858878394442758059344687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5145171192590344079126249 3858878394442758059344687)
          ·
            refine ⟨5788317591664137089017031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3858878394442758059344687 5788317591664137089017031)
            ·
              refine ⟨8682476387496205633525547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5788317591664137089017031 8682476387496205633525547)
              ·
                refine ⟨13023714581244308450288321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8682476387496205633525547 13023714581244308450288321)
                ·
                  refine ⟨9767785935933231337716241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13023714581244308450288321 9767785935933231337716241)
                  ·
                    refine ⟨7325839451949923503287181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9767785935933231337716241 7325839451949923503287181)
                    ·
                      refine ⟨2747189794481221313732693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7325839451949923503287181 2747189794481221313732693)
                      ·
                        rfl

theorem cell23_5350133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5350133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350133 prefixEnd_5350133 := by exact prefixLift 5350133
  have htrace : WordTrace (prefixWord ++ tailWord_5350133) baseStart_5350133 baseEnd_5350133 := by
    simpa [prefixWord, tailWord_5350133, baseEnd_5350133] using wordTrace_append hprefix tailTrace_5350133
  have hstable : (prefixWord ++ tailWord_5350133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350133).length < 2 ^ (prefixWord ++ tailWord_5350133).sum := by decide
  have hdescent : baseEnd_5350133 < baseStart_5350133 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350146 : List Nat := [3, 4, 1, 1, 1, 3, 2, 3, 1, 1, 3]
def baseStart_5350146 : Nat := 118140960795 + 5350146 * 2 ^ 59
def prefixEnd_5350146 : Nat := 4983230072969 + 3 ^ 40 * 5350146 * 2
def baseEnd_5350146 : Nat := 2747196469729729762870133

theorem tailTrace_5350146 : CollatzResearch.WordTrace tailWord_5350146 prefixEnd_5350146 2747196469729729762870133 := by
  unfold tailWord_5350146
  simp only [CollatzResearch.WordTrace]
  refine ⟨48783963918835562258993573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130090570450228166023982861 48783963918835562258993573)
  ·
    refine ⟨9146993234781667923561295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48783963918835562258993573 9146993234781667923561295)
    ·
      refine ⟨13720489852172501885341943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9146993234781667923561295 13720489852172501885341943)
      ·
        refine ⟨20580734778258752828012915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13720489852172501885341943 20580734778258752828012915)
        ·
          refine ⟨30871102167388129242019373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20580734778258752828012915 30871102167388129242019373)
          ·
            refine ⟨11576663312770548465757265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30871102167388129242019373 11576663312770548465757265)
            ·
              refine ⟨8682497484577911349317949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11576663312770548465757265 8682497484577911349317949)
              ·
                refine ⟨3255936556716716755994231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8682497484577911349317949 3255936556716716755994231)
                ·
                  refine ⟨4883904835075075133991347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3255936556716716755994231 4883904835075075133991347)
                  ·
                    refine ⟨7325857252612612700987021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4883904835075075133991347 7325857252612612700987021)
                    ·
                      refine ⟨2747196469729729762870133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7325857252612612700987021 2747196469729729762870133)
                      ·
                        rfl

theorem cell23_5350146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_5350146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350146 prefixEnd_5350146 := by exact prefixLift 5350146
  have htrace : WordTrace (prefixWord ++ tailWord_5350146) baseStart_5350146 baseEnd_5350146 := by
    simpa [prefixWord, tailWord_5350146, baseEnd_5350146] using wordTrace_append hprefix tailTrace_5350146
  have hstable : (prefixWord ++ tailWord_5350146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350146).length < 2 ^ (prefixWord ++ tailWord_5350146).sum := by decide
  have hdescent : baseEnd_5350146 < baseStart_5350146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350152 : List Nat := [2, 1, 3, 2, 2, 2, 4, 1, 1, 1, 4]
def baseStart_5350152 : Nat := 118140960795 + 5350152 * 2 ^ 59
def prefixEnd_5350152 : Nat := 4983230072969 + 3 ^ 40 * 5350152 * 2
def baseEnd_5350152 : Nat := 2747199550613656739395105

theorem tailTrace_5350152 : CollatzResearch.WordTrace tailWord_5350152 prefixEnd_5350152 2747199550613656739395105 := by
  unfold tailWord_5350152
  simp only [CollatzResearch.WordTrace]
  refine ⟨97568037256660256030346355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130090716342213674707128473 97568037256660256030346355)
  ·
    refine ⟨146352055884990384045519533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97568037256660256030346355 146352055884990384045519533)
    ·
      refine ⟨54882020956871394017069825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 146352055884990384045519533 54882020956871394017069825)
      ·
        refine ⟨41161515717653545512802369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54882020956871394017069825 41161515717653545512802369)
        ·
          refine ⟨30871136788240159134601777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41161515717653545512802369 30871136788240159134601777)
          ·
            refine ⟨23153352591180119350951333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30871136788240159134601777 23153352591180119350951333)
            ·
              refine ⟨4341253610846272378303375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23153352591180119350951333 4341253610846272378303375)
              ·
                refine ⟨6511880416269408567455063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4341253610846272378303375 6511880416269408567455063)
                ·
                  refine ⟨9767820624404112851182595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6511880416269408567455063 9767820624404112851182595)
                  ·
                    refine ⟨14651730936606169276773893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9767820624404112851182595 14651730936606169276773893)
                    ·
                      refine ⟨2747199550613656739395105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14651730936606169276773893 2747199550613656739395105)
                      ·
                        rfl

theorem cell23_5350152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_5350152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350152 prefixEnd_5350152 := by exact prefixLift 5350152
  have htrace : WordTrace (prefixWord ++ tailWord_5350152) baseStart_5350152 baseEnd_5350152 := by
    simpa [prefixWord, tailWord_5350152, baseEnd_5350152] using wordTrace_append hprefix tailTrace_5350152
  have hstable : (prefixWord ++ tailWord_5350152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350152).length < 2 ^ (prefixWord ++ tailWord_5350152).sum := by decide
  have hdescent : baseEnd_5350152 < baseStart_5350152 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350218 : List Nat := [3, 1, 2, 1, 1, 1, 2, 4, 2, 6]
def baseStart_5350218 : Nat := 118140960795 + 5350218 * 2 ^ 59
def prefixEnd_5350218 : Nat := 4983230072969 + 3 ^ 40 * 5350218 * 2
def baseEnd_5350218 : Nat := 915744480112284493723267

theorem tailTrace_5350218 : CollatzResearch.WordTrace tailWord_5350218 prefixEnd_5350218 915744480112284493723267 := by
  unfold tailWord_5350218
  simp only [CollatzResearch.WordTrace]
  refine ⟨48784620432770351333148827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130092321154054270221730205 48784620432770351333148827)
  ·
    refine ⟨73176930649155526999723241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48784620432770351333148827 73176930649155526999723241)
    ·
      refine ⟨54882697986866645249792431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73176930649155526999723241 54882697986866645249792431)
      ·
        refine ⟨82324046980299967874688647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54882697986866645249792431 82324046980299967874688647)
        ·
          refine ⟨123486070470449951812032971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 82324046980299967874688647 123486070470449951812032971)
          ·
            refine ⟨185229105705674927718049457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 123486070470449951812032971 185229105705674927718049457)
            ·
              refine ⟨138921829279256195788537093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 185229105705674927718049457 138921829279256195788537093)
              ·
                refine ⟨26047842989860536710350705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 138921829279256195788537093 26047842989860536710350705)
                ·
                  refine ⟨19535882242395402532763029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26047842989860536710350705 19535882242395402532763029)
                  ·
                    refine ⟨915744480112284493723267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19535882242395402532763029 915744480112284493723267)
                    ·
                      rfl

theorem cell23_5350218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 4, 2, 6].length) (baseStart_5350218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350218 prefixEnd_5350218 := by exact prefixLift 5350218
  have htrace : WordTrace (prefixWord ++ tailWord_5350218) baseStart_5350218 baseEnd_5350218 := by
    simpa [prefixWord, tailWord_5350218, baseEnd_5350218] using wordTrace_append hprefix tailTrace_5350218
  have hstable : (prefixWord ++ tailWord_5350218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350218).length < 2 ^ (prefixWord ++ tailWord_5350218).sum := by decide
  have hdescent : baseEnd_5350218 < baseStart_5350218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350236 : List Nat := [2, 2, 4, 2, 1, 1, 4, 1, 2, 1, 3]
def baseStart_5350236 : Nat := 118140960795 + 5350236 * 2 ^ 59
def prefixEnd_5350236 : Nat := 4983230072969 + 3 ^ 40 * 5350236 * 2
def baseEnd_5350236 : Nat := 2747242682988634410744719

theorem tailTrace_5350236 : CollatzResearch.WordTrace tailWord_5350236 prefixEnd_5350236 2747242682988634410744719 := by
  unfold tailWord_5350236
  simp only [CollatzResearch.WordTrace]
  refine ⟨97569569122508097203375281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130092758830010796271167041 97569569122508097203375281)
  ·
    refine ⟨73177176841881072902531461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97569569122508097203375281 73177176841881072902531461)
    ·
      refine ⟨13720720657852701169224649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73177176841881072902531461 13720720657852701169224649)
      ·
        refine ⟨10290540493389525876918487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13720720657852701169224649 10290540493389525876918487)
        ·
          refine ⟨15435810740084288815377731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10290540493389525876918487 15435810740084288815377731)
          ·
            refine ⟨23153716110126433223066597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15435810740084288815377731 23153716110126433223066597)
            ·
              refine ⟨4341321770648706229324987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23153716110126433223066597 4341321770648706229324987)
              ·
                refine ⟨6511982655973059343987481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4341321770648706229324987 6511982655973059343987481)
                ·
                  refine ⟨4883986991979794507990611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6511982655973059343987481 4883986991979794507990611)
                  ·
                    refine ⟨7325980487969691761985917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4883986991979794507990611 7325980487969691761985917)
                    ·
                      refine ⟨2747242682988634410744719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7325980487969691761985917 2747242682988634410744719)
                      ·
                        rfl

theorem cell23_5350236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_5350236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350236 prefixEnd_5350236 := by exact prefixLift 5350236
  have htrace : WordTrace (prefixWord ++ tailWord_5350236) baseStart_5350236 baseEnd_5350236 := by
    simpa [prefixWord, tailWord_5350236, baseEnd_5350236] using wordTrace_append hprefix tailTrace_5350236
  have hstable : (prefixWord ++ tailWord_5350236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350236).length < 2 ^ (prefixWord ++ tailWord_5350236).sum := by decide
  have hdescent : baseEnd_5350236 < baseStart_5350236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350262 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5]
def baseStart_5350262 : Nat := 118140960795 + 5350262 * 2 ^ 59
def prefixEnd_5350262 : Nat := 4983230072969 + 3 ^ 40 * 5350262 * 2
def baseEnd_5350262 : Nat := 2747256033485651309019599

theorem tailTrace_5350262 : CollatzResearch.WordTrace tailWord_5350262 prefixEnd_5350262 2747256033485651309019599 := by
  unfold tailWord_5350262
  simp only [CollatzResearch.WordTrace]
  refine ⟨12196255408932625052949815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 130093391028614667231464693 12196255408932625052949815)
  ·
    refine ⟨18294383113398937579424723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12196255408932625052949815 18294383113398937579424723)
    ·
      refine ⟨27441574670098406369137085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18294383113398937579424723 27441574670098406369137085)
      ·
        refine ⟨10290590501286902388426407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27441574670098406369137085 10290590501286902388426407)
        ·
          refine ⟨15435885751930353582639611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10290590501286902388426407 15435885751930353582639611)
          ·
            refine ⟨23153828627895530373959417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15435885751930353582639611 23153828627895530373959417)
            ·
              refine ⟨17365371470921647780469563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23153828627895530373959417 17365371470921647780469563)
              ·
                refine ⟨26048057206382471670704345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17365371470921647780469563 26048057206382471670704345)
                ·
                  refine ⟨19536042904786853753028259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26048057206382471670704345 19536042904786853753028259)
                  ·
                    refine ⟨29304064357180280629542389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19536042904786853753028259 29304064357180280629542389)
                    ·
                      refine ⟨2747256033485651309019599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29304064357180280629542389 2747256033485651309019599)
                      ·
                        rfl

theorem cell23_5350262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_5350262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350262 prefixEnd_5350262 := by exact prefixLift 5350262
  have htrace : WordTrace (prefixWord ++ tailWord_5350262) baseStart_5350262 baseEnd_5350262 := by
    simpa [prefixWord, tailWord_5350262, baseEnd_5350262] using wordTrace_append hprefix tailTrace_5350262
  have hstable : (prefixWord ++ tailWord_5350262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350262).length < 2 ^ (prefixWord ++ tailWord_5350262).sum := by decide
  have hdescent : baseEnd_5350262 < baseStart_5350262 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350275 : List Nat := [1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 3]
def baseStart_5350275 : Nat := 118140960795 + 5350275 * 2 ^ 59
def prefixEnd_5350275 : Nat := 4983230072969 + 3 ^ 40 * 5350275 * 2
def baseEnd_5350275 : Nat := 2747262708734159758157039

theorem tailTrace_5350275 : CollatzResearch.WordTrace tailWord_5350275 prefixEnd_5350275 2747262708734159758157039 := by
  unfold tailWord_5350275
  simp only [CollatzResearch.WordTrace]
  refine ⟨195140560691874904067420279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130093707127916602711613519 195140560691874904067420279)
  ·
    refine ⟨292710841037812356101130419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 195140560691874904067420279 292710841037812356101130419)
    ·
      refine ⟨439066261556718534151695629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292710841037812356101130419 439066261556718534151695629)
      ·
        refine ⟨164649848083769450306885861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 439066261556718534151695629 164649848083769450306885861)
        ·
          refine ⟨30871846515706771932541099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 164649848083769450306885861 30871846515706771932541099)
          ·
            refine ⟨46307769773560157898811649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30871846515706771932541099 46307769773560157898811649)
            ·
              refine ⟨34730827330170118424108737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46307769773560157898811649 34730827330170118424108737)
              ·
                refine ⟨26048120497627588818081553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34730827330170118424108737 26048120497627588818081553)
                ·
                  refine ⟨19536090373220691613561165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26048120497627588818081553 19536090373220691613561165)
                  ·
                    refine ⟨7326033889957759355085437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19536090373220691613561165 7326033889957759355085437)
                    ·
                      refine ⟨2747262708734159758157039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7326033889957759355085437 2747262708734159758157039)
                      ·
                        rfl

theorem cell23_5350275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_5350275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350275 prefixEnd_5350275 := by exact prefixLift 5350275
  have htrace : WordTrace (prefixWord ++ tailWord_5350275) baseStart_5350275 baseEnd_5350275 := by
    simpa [prefixWord, tailWord_5350275, baseEnd_5350275] using wordTrace_append hprefix tailTrace_5350275
  have hstable : (prefixWord ++ tailWord_5350275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350275).length < 2 ^ (prefixWord ++ tailWord_5350275).sum := by decide
  have hdescent : baseEnd_5350275 < baseStart_5350275 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350288 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 5]
def baseStart_5350288 : Nat := 118140960795 + 5350288 * 2 ^ 59
def prefixEnd_5350288 : Nat := 4983230072969 + 3 ^ 40 * 5350288 * 2
def baseEnd_5350288 : Nat := 2747269383982668207294479

theorem tailTrace_5350288 : CollatzResearch.WordTrace tailWord_5350288 prefixEnd_5350288 2747269383982668207294479 := by
  unfold tailWord_5350288
  simp only [CollatzResearch.WordTrace]
  refine ⟨97570517420413903643821759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130094023227218538191762345 97570517420413903643821759)
  ·
    refine ⟨146355776130620855465732639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 97570517420413903643821759 146355776130620855465732639)
    ·
      refine ⟨219533664195931283198598959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146355776130620855465732639 219533664195931283198598959)
      ·
        refine ⟨329300496293896924797898439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 219533664195931283198598959 329300496293896924797898439)
        ·
          refine ⟨493950744440845387196847659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329300496293896924797898439 493950744440845387196847659)
          ·
            refine ⟨740926116661268080795271489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 493950744440845387196847659 740926116661268080795271489)
            ·
              refine ⟨555694587495951060596453617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740926116661268080795271489 555694587495951060596453617)
              ·
                refine ⟨416770940621963295447340213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555694587495951060596453617 416770940621963295447340213)
                ·
                  refine ⟨39072275683309058948188145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 416770940621963295447340213 39072275683309058948188145)
                  ·
                    refine ⟨29304206762481794211141109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39072275683309058948188145 29304206762481794211141109)
                    ·
                      refine ⟨2747269383982668207294479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29304206762481794211141109 2747269383982668207294479)
                      ·
                        rfl

theorem cell23_5350288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_5350288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350288 prefixEnd_5350288 := by exact prefixLift 5350288
  have htrace : WordTrace (prefixWord ++ tailWord_5350288) baseStart_5350288 baseEnd_5350288 := by
    simpa [prefixWord, tailWord_5350288, baseEnd_5350288] using wordTrace_append hprefix tailTrace_5350288
  have hstable : (prefixWord ++ tailWord_5350288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350288).length < 2 ^ (prefixWord ++ tailWord_5350288).sum := by decide
  have hdescent : baseEnd_5350288 < baseStart_5350288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350292 : List Nat := [2, 4, 2, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_5350292 : Nat := 118140960795 + 5350292 * 2 ^ 59
def prefixEnd_5350292 : Nat := 4983230072969 + 3 ^ 40 * 5350292 * 2
def baseEnd_5350292 : Nat := 2747271437905286191644461

theorem tailTrace_5350292 : CollatzResearch.WordTrace tailWord_5350292 prefixEnd_5350292 2747271437905286191644461 := by
  unfold tailWord_5350292
  simp only [CollatzResearch.WordTrace]
  refine ⟨97570590366406657985394565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130094120488542210647192753 97570590366406657985394565)
  ·
    refine ⟨18294485693701248372261481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 97570590366406657985394565 18294485693701248372261481)
    ·
      refine ⟨13720864270275936279196111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18294485693701248372261481 13720864270275936279196111)
      ·
        refine ⟨20581296405413904418794167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13720864270275936279196111 20581296405413904418794167)
        ·
          refine ⟨30871944608120856628191251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20581296405413904418794167 30871944608120856628191251)
          ·
            refine ⟨46307916912181284942286877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30871944608120856628191251 46307916912181284942286877)
            ·
              refine ⟨17365468842067981853357579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46307916912181284942286877 17365468842067981853357579)
              ·
                refine ⟨26048203263101972780036369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17365468842067981853357579 26048203263101972780036369)
                ·
                  refine ⟨19536152447326479585027277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26048203263101972780036369 19536152447326479585027277)
                  ·
                    refine ⟨7326057167747429844385229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19536152447326479585027277 7326057167747429844385229)
                    ·
                      refine ⟨2747271437905286191644461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7326057167747429844385229 2747271437905286191644461)
                      ·
                        rfl

theorem cell23_5350292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_5350292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350292 prefixEnd_5350292 := by exact prefixLift 5350292
  have htrace : WordTrace (prefixWord ++ tailWord_5350292) baseStart_5350292 baseEnd_5350292 := by
    simpa [prefixWord, tailWord_5350292, baseEnd_5350292] using wordTrace_append hprefix tailTrace_5350292
  have hstable : (prefixWord ++ tailWord_5350292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350292).length < 2 ^ (prefixWord ++ tailWord_5350292).sum := by decide
  have hdescent : baseEnd_5350292 < baseStart_5350292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350386 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 2, 2, 3]
def baseStart_5350386 : Nat := 118140960795 + 5350386 * 2 ^ 59
def prefixEnd_5350386 : Nat := 4983230072969 + 3 ^ 40 * 5350386 * 2
def baseEnd_5350386 : Nat := 2747319705086808823869029

theorem tailTrace_5350386 : CollatzResearch.WordTrace tailWord_5350386 prefixEnd_5350386 2747319705086808823869029 := by
  unfold tailWord_5350386
  simp only [CollatzResearch.WordTrace]
  refine ⟨48786152298618192506177753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130096406129648513349807341 48786152298618192506177753)
  ·
    refine ⟨36589614223963644379633315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48786152298618192506177753 36589614223963644379633315)
    ·
      refine ⟨54884421335945466569449973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36589614223963644379633315 54884421335945466569449973)
      ·
        refine ⟨5145414500244887490885935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54884421335945466569449973 5145414500244887490885935)
        ·
          refine ⟨7718121750367331236328903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5145414500244887490885935 7718121750367331236328903)
          ·
            refine ⟨11577182625550996854493355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7718121750367331236328903 11577182625550996854493355)
            ·
              refine ⟨17365773938326495281740033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11577182625550996854493355 17365773938326495281740033)
              ·
                refine ⟨13024330453744871461305025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17365773938326495281740033 13024330453744871461305025)
                ·
                  refine ⟨9768247840308653595978769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13024330453744871461305025 9768247840308653595978769)
                  ·
                    refine ⟨7326185880231490196984077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9768247840308653595978769 7326185880231490196984077)
                    ·
                      refine ⟨2747319705086808823869029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7326185880231490196984077 2747319705086808823869029)
                      ·
                        rfl

theorem cell23_5350386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_5350386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350386 prefixEnd_5350386 := by exact prefixLift 5350386
  have htrace : WordTrace (prefixWord ++ tailWord_5350386) baseStart_5350386 baseEnd_5350386 := by
    simpa [prefixWord, tailWord_5350386, baseEnd_5350386] using wordTrace_append hprefix tailTrace_5350386
  have hstable : (prefixWord ++ tailWord_5350386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350386).length < 2 ^ (prefixWord ++ tailWord_5350386).sum := by decide
  have hdescent : baseEnd_5350386 < baseStart_5350386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350425 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 3, 1, 5]
def baseStart_5350425 : Nat := 118140960795 + 5350425 * 2 ^ 59
def prefixEnd_5350425 : Nat := 4983230072969 + 3 ^ 40 * 5350425 * 2
def baseEnd_5350425 : Nat := 2747339730832334171281349

theorem tailTrace_5350425 : CollatzResearch.WordTrace tailWord_5350425 prefixEnd_5350425 2747339730832334171281349 := by
  unfold tailWord_5350425
  simp only [CollatzResearch.WordTrace]
  refine ⟨195146031641331479685380729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130097354427554319790253819 195146031641331479685380729)
  ·
    refine ⟨146359523730998609764035547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195146031641331479685380729 146359523730998609764035547)
    ·
      refine ⟨219539285596497914646053321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 146359523730998609764035547 219539285596497914646053321)
      ·
        refine ⟨164654464197373435984539991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 219539285596497914646053321 164654464197373435984539991)
        ·
          refine ⟨246981696296060153976809987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 164654464197373435984539991 246981696296060153976809987)
          ·
            refine ⟨370472544444090230965214981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246981696296060153976809987 370472544444090230965214981)
            ·
              refine ⟨69463602083266918305977809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 370472544444090230965214981 69463602083266918305977809)
              ·
                refine ⟨52097701562450188729483357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 69463602083266918305977809 52097701562450188729483357)
                ·
                  refine ⟨19536638085918820773556259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52097701562450188729483357 19536638085918820773556259)
                  ·
                    refine ⟨29304957128878231160334389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19536638085918820773556259 29304957128878231160334389)
                    ·
                      refine ⟨2747339730832334171281349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29304957128878231160334389 2747339730832334171281349)
                      ·
                        rfl

theorem cell23_5350425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_5350425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350425 prefixEnd_5350425 := by exact prefixLift 5350425
  have htrace : WordTrace (prefixWord ++ tailWord_5350425) baseStart_5350425 baseEnd_5350425 := by
    simpa [prefixWord, tailWord_5350425, baseEnd_5350425] using wordTrace_append hprefix tailTrace_5350425
  have hstable : (prefixWord ++ tailWord_5350425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350425).length < 2 ^ (prefixWord ++ tailWord_5350425).sum := by decide
  have hdescent : baseEnd_5350425 < baseStart_5350425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350436 : List Nat := [2, 3, 1, 4, 1, 2, 3, 1, 1, 5]
def baseStart_5350436 : Nat := 118140960795 + 5350436 * 2 ^ 59
def prefixEnd_5350436 : Nat := 4983230072969 + 3 ^ 40 * 5350436 * 2
def baseEnd_5350436 : Nat := 915781793039844542747933

theorem tailTrace_5350436 : CollatzResearch.WordTrace tailWord_5350436 prefixEnd_5350436 915781793039844542747933 := by
  unfold tailWord_5350436
  simp only [CollatzResearch.WordTrace]
  refine ⟨97573216422145814282015581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130097621896194419042687441 97573216422145814282015581)
  ·
    refine ⟨36589956158304680355755843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 97573216422145814282015581 36589956158304680355755843)
    ·
      refine ⟨54884934237457020533633765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36589956158304680355755843 54884934237457020533633765)
      ·
        refine ⟨10290925169523191350056331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54884934237457020533633765 10290925169523191350056331)
        ·
          refine ⟨15436387754284787025084497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10290925169523191350056331 15436387754284787025084497)
          ·
            refine ⟨11577290815713590268813373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15436387754284787025084497 11577290815713590268813373)
            ·
              refine ⟨4341484055892596350805015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11577290815713590268813373 4341484055892596350805015)
              ·
                refine ⟨6512226083838894526207523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4341484055892596350805015 6512226083838894526207523)
                ·
                  refine ⟨9768339125758341789311285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6512226083838894526207523 9768339125758341789311285)
                  ·
                    refine ⟨915781793039844542747933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9768339125758341789311285 915781793039844542747933)
                    ·
                      rfl

theorem cell23_5350436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_5350436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350436 prefixEnd_5350436 := by exact prefixLift 5350436
  have htrace : WordTrace (prefixWord ++ tailWord_5350436) baseStart_5350436 baseEnd_5350436 := by
    simpa [prefixWord, tailWord_5350436, baseEnd_5350436] using wordTrace_append hprefix tailTrace_5350436
  have hstable : (prefixWord ++ tailWord_5350436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350436).length < 2 ^ (prefixWord ++ tailWord_5350436).sum := by decide
  have hdescent : baseEnd_5350436 < baseStart_5350436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350449 : List Nat := [1, 2, 2, 3, 1, 2, 4, 2, 2, 4]
def baseStart_5350449 : Nat := 118140960795 + 5350449 * 2 ^ 59
def prefixEnd_5350449 : Nat := 4983230072969 + 3 ^ 40 * 5350449 * 2
def baseEnd_5350449 : Nat := 915784018122680692460413

theorem tailTrace_5350449 : CollatzResearch.WordTrace tailWord_5350449 prefixEnd_5350449 915784018122680692460413 := by
  unfold tailWord_5350449
  simp only [CollatzResearch.WordTrace]
  refine ⟨195146906993244531784254401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130097937995496354522836267 195146906993244531784254401)
  ·
    refine ⟨146360180244933398838190801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 195146906993244531784254401 146360180244933398838190801)
    ·
      refine ⟨109770135183700049128643101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 146360180244933398838190801 109770135183700049128643101)
      ·
        refine ⟨41163800693887518423241163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 109770135183700049128643101 41163800693887518423241163)
        ·
          refine ⟨61745701040831277634861745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41163800693887518423241163 61745701040831277634861745)
          ·
            refine ⟨46309275780623458226146309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 61745701040831277634861745 46309275780623458226146309)
            ·
              refine ⟨8682989208866898417402433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46309275780623458226146309 8682989208866898417402433)
              ·
                refine ⟨6512241906650173813051825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8682989208866898417402433 6512241906650173813051825)
                ·
                  refine ⟨4884181429987630359788869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6512241906650173813051825 4884181429987630359788869)
                  ·
                    refine ⟨915784018122680692460413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4884181429987630359788869 915784018122680692460413)
                    ·
                      rfl

theorem cell23_5350449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_5350449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350449 prefixEnd_5350449 := by exact prefixLift 5350449
  have htrace : WordTrace (prefixWord ++ tailWord_5350449) baseStart_5350449 baseEnd_5350449 := by
    simpa [prefixWord, tailWord_5350449, baseEnd_5350449] using wordTrace_append hprefix tailTrace_5350449
  have hstable : (prefixWord ++ tailWord_5350449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350449).length < 2 ^ (prefixWord ++ tailWord_5350449).sum := by decide
  have hdescent : baseEnd_5350449 < baseStart_5350449 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350493 : List Nat := [1, 4, 4, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_5350493 : Nat := 118140960795 + 5350493 * 2 ^ 59
def prefixEnd_5350493 : Nat := 4983230072969 + 3 ^ 40 * 5350493 * 2
def baseEnd_5350493 : Nat := 2747374647516839905231037

theorem tailTrace_5350493 : CollatzResearch.WordTrace tailWord_5350493 prefixEnd_5350493 2747374647516839905231037 := by
  unfold tailWord_5350493
  simp only [CollatzResearch.WordTrace]
  refine ⟨195148511805085127298856133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130099007870056751532570755 195148511805085127298856133)
  ·
    refine ⟨36590345963453461368535525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 195148511805085127298856133 36590345963453461368535525)
    ·
      refine ⟨6860689868147524006600411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36590345963453461368535525 6860689868147524006600411)
      ·
        refine ⟨10291034802221286009900617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6860689868147524006600411 10291034802221286009900617)
        ·
          refine ⟨7718276101665964507425463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10291034802221286009900617 7718276101665964507425463)
          ·
            refine ⟨11577414152498946761138195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7718276101665964507425463 11577414152498946761138195)
            ·
              refine ⟨17366121228748420141707293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11577414152498946761138195 17366121228748420141707293)
              ·
                refine ⟨6512295460780657553140235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17366121228748420141707293 6512295460780657553140235)
                ·
                  refine ⟨9768443191170986329710353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6512295460780657553140235 9768443191170986329710353)
                  ·
                    refine ⟨7326332393378239747282765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9768443191170986329710353 7326332393378239747282765)
                    ·
                      refine ⟨2747374647516839905231037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7326332393378239747282765 2747374647516839905231037)
                      ·
                        rfl

theorem cell23_5350493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_5350493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350493 prefixEnd_5350493 := by exact prefixLift 5350493
  have htrace : WordTrace (prefixWord ++ tailWord_5350493) baseStart_5350493 baseEnd_5350493 := by
    simpa [prefixWord, tailWord_5350493, baseEnd_5350493] using wordTrace_append hprefix tailTrace_5350493
  have hstable : (prefixWord ++ tailWord_5350493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350493).length < 2 ^ (prefixWord ++ tailWord_5350493).sum := by decide
  have hdescent : baseEnd_5350493 < baseStart_5350493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350506 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 4, 1, 3]
def baseStart_5350506 : Nat := 118140960795 + 5350506 * 2 ^ 59
def prefixEnd_5350506 : Nat := 4983230072969 + 3 ^ 40 * 5350506 * 2
def baseEnd_5350506 : Nat := 2747381322765348354368477

theorem tailTrace_5350506 : CollatzResearch.WordTrace tailWord_5350506 prefixEnd_5350506 2747381322765348354368477 := by
  unfold tailWord_5350506
  simp only [CollatzResearch.WordTrace]
  refine ⟨48787246488509507629769843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130099323969358687012719581 48787246488509507629769843)
  ·
    refine ⟨73180869732764261444654765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48787246488509507629769843 73180869732764261444654765)
    ·
      refine ⟨27442826149786598041745537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73180869732764261444654765 27442826149786598041745537)
      ·
        refine ⟨20582119612339948531309153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27442826149786598041745537 20582119612339948531309153)
        ·
          refine ⟨15436589709254961398481865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20582119612339948531309153 15436589709254961398481865)
          ·
            refine ⟨11577442281941221048861399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15436589709254961398481865 11577442281941221048861399)
            ·
              refine ⟨17366163422911831573292099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11577442281941221048861399 17366163422911831573292099)
              ·
                refine ⟨26049245134367747359938149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17366163422911831573292099 26049245134367747359938149)
                ·
                  refine ⟨4884233462693952629988403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26049245134367747359938149 4884233462693952629988403)
                  ·
                    refine ⟨7326350194040928944982605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4884233462693952629988403 7326350194040928944982605)
                    ·
                      refine ⟨2747381322765348354368477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7326350194040928944982605 2747381322765348354368477)
                      ·
                        rfl

theorem cell23_5350506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_5350506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350506 prefixEnd_5350506 := by exact prefixLift 5350506
  have htrace : WordTrace (prefixWord ++ tailWord_5350506) baseStart_5350506 baseEnd_5350506 := by
    simpa [prefixWord, tailWord_5350506, baseEnd_5350506] using wordTrace_append hprefix tailTrace_5350506
  have hstable : (prefixWord ++ tailWord_5350506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350506).length < 2 ^ (prefixWord ++ tailWord_5350506).sum := by decide
  have hdescent : baseEnd_5350506 < baseStart_5350506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350533 : List Nat := [1, 3, 1, 1, 6, 1, 2, 2, 1, 3, 2]
def baseStart_5350533 : Nat := 118140960795 + 5350533 * 2 ^ 59
def prefixEnd_5350533 : Nat := 4983230072969 + 3 ^ 40 * 5350533 * 2
def baseEnd_5350533 : Nat := 2747395186743019748730853

theorem tailTrace_5350533 : CollatzResearch.WordTrace tailWord_5350533 prefixEnd_5350533 2747395186743019748730853 := by
  unfold tailWord_5350533
  simp only [CollatzResearch.WordTrace]
  refine ⟨195149970724940214130312253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 130099980483293476086874835 195149970724940214130312253)
  ·
    refine ⟨73181239021852580298867095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 195149970724940214130312253 73181239021852580298867095)
    ·
      refine ⟨109771858532778870448300643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73181239021852580298867095 109771858532778870448300643)
      ·
        refine ⟨164657787799168305672450965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109771858532778870448300643 164657787799168305672450965)
        ·
          refine ⟨7718333803086014328396139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 164657787799168305672450965 7718333803086014328396139)
          ·
            refine ⟨11577500704629021492594209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7718333803086014328396139 11577500704629021492594209)
            ·
              refine ⟨8683125528471766119445657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11577500704629021492594209 8683125528471766119445657)
              ·
                refine ⟨6512344146353824589584243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8683125528471766119445657 6512344146353824589584243)
                ·
                  refine ⟨9768516219530736884376365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6512344146353824589584243 9768516219530736884376365)
                  ·
                    refine ⟨3663193582324026331641137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9768516219530736884376365 3663193582324026331641137)
                    ·
                      refine ⟨2747395186743019748730853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3663193582324026331641137 2747395186743019748730853)
                      ·
                        rfl

theorem cell23_5350533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 1, 3, 2].length) (baseStart_5350533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350533 prefixEnd_5350533 := by exact prefixLift 5350533
  have htrace : WordTrace (prefixWord ++ tailWord_5350533) baseStart_5350533 baseEnd_5350533 := by
    simpa [prefixWord, tailWord_5350533, baseEnd_5350533] using wordTrace_append hprefix tailTrace_5350533
  have hstable : (prefixWord ++ tailWord_5350533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350533).length < 2 ^ (prefixWord ++ tailWord_5350533).sum := by decide
  have hdescent : baseEnd_5350533 < baseStart_5350533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350636 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 2, 4, 2]
def baseStart_5350636 : Nat := 118140960795 + 5350636 * 2 ^ 59
def prefixEnd_5350636 : Nat := 4983230072969 + 3 ^ 40 * 5350636 * 2
def baseEnd_5350636 : Nat := 2747448075250432845742879

theorem tailTrace_5350636 : CollatzResearch.WordTrace tailWord_5350636 prefixEnd_5350636 2747448075250432845742879 := by
  unfold tailWord_5350636
  simp only [CollatzResearch.WordTrace]
  refine ⟨97576863721783531360655881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 130102484962378041814207841 97576863721783531360655881)
  ·
    refine ⟨73182647791337648520491911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 97576863721783531360655881 73182647791337648520491911)
    ·
      refine ⟨109773971687006472780737867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73182647791337648520491911 109773971687006472780737867)
      ·
        refine ⟨164660957530509709171106801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 109773971687006472780737867 164660957530509709171106801)
        ·
          refine ⟨123495718147882281878330101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 164660957530509709171106801 123495718147882281878330101)
          ·
            refine ⟨11577723576363963926093447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 123495718147882281878330101 11577723576363963926093447)
            ·
              refine ⟨17366585364545945889140171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11577723576363963926093447 17366585364545945889140171)
              ·
                refine ⟨26049878046818918833710257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17366585364545945889140171 26049878046818918833710257)
                ·
                  refine ⟨19537408535114189125282693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26049878046818918833710257 19537408535114189125282693)
                  ·
                    refine ⟨3663264100333910460990505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19537408535114189125282693 3663264100333910460990505)
                    ·
                      refine ⟨2747448075250432845742879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3663264100333910460990505 2747448075250432845742879)
                      ·
                        rfl

theorem cell23_5350636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 4, 2].length) (baseStart_5350636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350636 prefixEnd_5350636 := by exact prefixLift 5350636
  have htrace : WordTrace (prefixWord ++ tailWord_5350636) baseStart_5350636 baseEnd_5350636 := by
    simpa [prefixWord, tailWord_5350636, baseEnd_5350636] using wordTrace_append hprefix tailTrace_5350636
  have hstable : (prefixWord ++ tailWord_5350636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350636).length < 2 ^ (prefixWord ++ tailWord_5350636).sum := by decide
  have hdescent : baseEnd_5350636 < baseStart_5350636 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5350706 : List Nat := [3, 2, 1, 1, 4, 1, 1, 4, 1, 5]
def baseStart_5350706 : Nat := 118140960795 + 5350706 * 2 ^ 59
def prefixEnd_5350706 : Nat := 4983230072969 + 3 ^ 40 * 5350706 * 2
def baseEnd_5350706 : Nat := 915828006298749190622519

theorem tailTrace_5350706 : CollatzResearch.WordTrace tailWord_5350706 prefixEnd_5350706 915828006298749190622519 := by
  unfold tailWord_5350706
  simp only [CollatzResearch.WordTrace]
  refine ⟨48789070138328366169089993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 130104187035542309784239981 48789070138328366169089993)
  ·
    refine ⟨36591802603746274626817495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48789070138328366169089993 36591802603746274626817495)
    ·
      refine ⟨54887703905619411940226243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36591802603746274626817495 54887703905619411940226243)
      ·
        refine ⟨82331555858429117910339365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54887703905619411940226243 82331555858429117910339365)
        ·
          refine ⟨15437166723455459608188631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 82331555858429117910339365 15437166723455459608188631)
          ·
            refine ⟨23155750085183189412282947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15437166723455459608188631 23155750085183189412282947)
            ·
              refine ⟨34733625127774784118424421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23155750085183189412282947 34733625127774784118424421)
              ·
                refine ⟨6512554711457772022204579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34733625127774784118424421 6512554711457772022204579)
                ·
                  refine ⟨9768832067186658033306869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6512554711457772022204579 9768832067186658033306869)
                  ·
                    refine ⟨915828006298749190622519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9768832067186658033306869 915828006298749190622519)
                    ·
                      rfl

theorem cell23_5350706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_5350706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5350706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5350706 prefixEnd_5350706 := by exact prefixLift 5350706
  have htrace : WordTrace (prefixWord ++ tailWord_5350706) baseStart_5350706 baseEnd_5350706 := by
    simpa [prefixWord, tailWord_5350706, baseEnd_5350706] using wordTrace_append hprefix tailTrace_5350706
  have hstable : (prefixWord ++ tailWord_5350706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5350706).length < 2 ^ (prefixWord ++ tailWord_5350706).sum := by decide
  have hdescent : baseEnd_5350706 < baseStart_5350706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5350706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
