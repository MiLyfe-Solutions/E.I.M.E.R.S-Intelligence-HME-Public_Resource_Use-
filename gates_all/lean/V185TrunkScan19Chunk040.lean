import V185TrunkScan19Chunk039

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_401863 : List Nat := [1, 1, 4, 1, 1, 4, 4, 3]
def baseStart_401863 : Nat := 118140960795 + 401863 * 2 ^ 59
def prefixEnd_401863 : Nat := 4983230072969 + 3 ^ 40 * 401863 * 2
def baseEnd_401863 : Nat := 122280815560217151327035

theorem tailTrace_401863 : CollatzResearch.WordTrace tailWord_401863 prefixEnd_401863 122280815560217151327035 := by
  unfold tailWord_401863
  simp only [CollatzResearch.WordTrace]
  refine ⟨14657147743126458581378243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9771431828750972387585495 14657147743126458581378243)
  ·
    refine ⟨21985721614689687872067365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14657147743126458581378243 21985721614689687872067365)
    ·
      refine ⟨4122322802754316476012631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21985721614689687872067365 4122322802754316476012631)
      ·
        refine ⟨6183484204131474714018947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4122322802754316476012631 6183484204131474714018947)
        ·
          refine ⟨9275226306197212071028421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6183484204131474714018947 9275226306197212071028421)
          ·
            refine ⟨1739104932411977263317829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9275226306197212071028421 1739104932411977263317829)
            ·
              refine ⟨326082174827245736872093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1739104932411977263317829 326082174827245736872093)
              ·
                refine ⟨122280815560217151327035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326082174827245736872093 122280815560217151327035)
                ·
                  rfl

theorem cell19_401863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 4, 3].length) (baseStart_401863 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401863 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401863 prefixEnd_401863 := by exact prefixLift 401863
  have htrace : WordTrace (prefixWord ++ tailWord_401863) baseStart_401863 baseEnd_401863 := by
    simpa [prefixWord, tailWord_401863, baseEnd_401863] using wordTrace_append hprefix tailTrace_401863
  have hstable : (prefixWord ++ tailWord_401863).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401863).length < 2 ^ (prefixWord ++ tailWord_401863).sum := by decide
  have hdescent : baseEnd_401863 < baseStart_401863 := by decide
  rcases family_descends (prefixWord ++ tailWord_401863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401901 : List Nat := [1, 5, 1, 3, 1, 1, 1, 6]
def baseStart_401901 : Nat := 118140960795 + 401901 * 2 ^ 59
def prefixEnd_401901 : Nat := 4983230072969 + 3 ^ 40 * 401901 * 2
def baseEnd_401901 : Nat := 122292378383844322482487

theorem tailTrace_401901 : CollatzResearch.WordTrace tailWord_401901 prefixEnd_401901 122292378383844322482487 := by
  unfold tailWord_401901
  simp only [CollatzResearch.WordTrace]
  refine ⟨14658533716988791071261557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9772355811325860714174371 14658533716988791071261557)
  ·
    refine ⟨1374237535967699162930771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14658533716988791071261557 1374237535967699162930771)
    ·
      refine ⟨2061356303951548744396157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1374237535967699162930771 2061356303951548744396157)
      ·
        refine ⟨773008613981830779148559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2061356303951548744396157 773008613981830779148559)
        ·
          refine ⟨1159512920972746168722839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 773008613981830779148559 1159512920972746168722839)
          ·
            refine ⟨1739269381459119253084259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1159512920972746168722839 1739269381459119253084259)
            ·
              refine ⟨2608904072188678879626389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1739269381459119253084259 2608904072188678879626389)
              ·
                refine ⟨122292378383844322482487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2608904072188678879626389 122292378383844322482487)
                ·
                  rfl

theorem cell19_401901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 6].length) (baseStart_401901 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401901 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401901 prefixEnd_401901 := by exact prefixLift 401901
  have htrace : WordTrace (prefixWord ++ tailWord_401901) baseStart_401901 baseEnd_401901 := by
    simpa [prefixWord, tailWord_401901, baseEnd_401901] using wordTrace_append hprefix tailTrace_401901
  have hstable : (prefixWord ++ tailWord_401901).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401901).length < 2 ^ (prefixWord ++ tailWord_401901).sum := by decide
  have hdescent : baseEnd_401901 < baseStart_401901 := by decide
  rcases family_descends (prefixWord ++ tailWord_401901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_401977 : List Nat := [1, 2, 1, 5, 1, 1, 5, 3]
def baseStart_401977 : Nat := 118140960795 + 401977 * 2 ^ 59
def prefixEnd_401977 : Nat := 4983230072969 + 3 ^ 40 * 401977 * 2
def baseEnd_401977 : Nat := 122315504031098664793391

theorem tailTrace_401977 : CollatzResearch.WordTrace tailWord_401977 prefixEnd_401977 122315504031098664793391 := by
  unfold tailWord_401977
  simp only [CollatzResearch.WordTrace]
  refine ⟨14661305664713456051028185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9774203776475637367352123 14661305664713456051028185)
  ·
    refine ⟨10995979248535092038271139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14661305664713456051028185 10995979248535092038271139)
    ·
      refine ⟨16493968872802638057406709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10995979248535092038271139 16493968872802638057406709)
      ·
        refine ⟨1546309581825247317881879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16493968872802638057406709 1546309581825247317881879)
        ·
          refine ⟨2319464372737870976822819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1546309581825247317881879 2319464372737870976822819)
          ·
            refine ⟨3479196559106806465234229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2319464372737870976822819 3479196559106806465234229)
            ·
              refine ⟨326174677416263106115709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3479196559106806465234229 326174677416263106115709)
              ·
                refine ⟨122315504031098664793391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326174677416263106115709 122315504031098664793391)
                ·
                  rfl

theorem cell19_401977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 5, 3].length) (baseStart_401977 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_401977 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_401977 prefixEnd_401977 := by exact prefixLift 401977
  have htrace : WordTrace (prefixWord ++ tailWord_401977) baseStart_401977 baseEnd_401977 := by
    simpa [prefixWord, tailWord_401977, baseEnd_401977] using wordTrace_append hprefix tailTrace_401977
  have hstable : (prefixWord ++ tailWord_401977).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_401977).length < 2 ^ (prefixWord ++ tailWord_401977).sum := by decide
  have hdescent : baseEnd_401977 < baseStart_401977 := by decide
  rcases family_descends (prefixWord ++ tailWord_401977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402032 : List Nat := [2, 1, 1, 1, 7, 2, 2, 3]
def baseStart_402032 : Nat := 118140960795 + 402032 * 2 ^ 59
def prefixEnd_402032 : Nat := 4983230072969 + 3 ^ 40 * 402032 * 2
def baseEnd_402032 : Nat := 122332239696874833571019

theorem tailTrace_402032 : CollatzResearch.WordTrace tailWord_402032 prefixEnd_402032 122332239696874833571019 := by
  unfold tailWord_402032
  simp only [CollatzResearch.WordTrace]
  refine ⟨7331655839757100222140175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9775541119676133629520233 7331655839757100222140175)
  ·
    refine ⟨10997483759635650333210263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7331655839757100222140175 10997483759635650333210263)
    ·
      refine ⟨16496225639453475499815395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10997483759635650333210263 16496225639453475499815395)
      ·
        refine ⟨24744338459180213249723093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16496225639453475499815395 24744338459180213249723093)
        ·
          refine ⟨579945432637036248040385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 24744338459180213249723093 579945432637036248040385)
          ·
            refine ⟨434959074477777186030289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 579945432637036248040385 434959074477777186030289)
            ·
              refine ⟨326219305858332889522717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 434959074477777186030289 326219305858332889522717)
              ·
                refine ⟨122332239696874833571019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326219305858332889522717 122332239696874833571019)
                ·
                  rfl

theorem cell19_402032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_402032 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402032 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402032 prefixEnd_402032 := by exact prefixLift 402032
  have htrace : WordTrace (prefixWord ++ tailWord_402032) baseStart_402032 baseEnd_402032 := by
    simpa [prefixWord, tailWord_402032, baseEnd_402032] using wordTrace_append hprefix tailTrace_402032
  have hstable : (prefixWord ++ tailWord_402032).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402032).length < 2 ^ (prefixWord ++ tailWord_402032).sum := by decide
  have hdescent : baseEnd_402032 < baseStart_402032 := by decide
  rcases family_descends (prefixWord ++ tailWord_402032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402034 : List Nat := [3, 2, 1, 2, 4, 1, 1, 5]
def baseStart_402034 : Nat := 118140960795 + 402034 * 2 ^ 59
def prefixEnd_402034 : Nat := 4983230072969 + 3 ^ 40 * 402034 * 2
def baseEnd_402034 : Nat := 122332848266539421526569

theorem tailTrace_402034 : CollatzResearch.WordTrace tailWord_402034 prefixEnd_402034 122332848266539421526569 := by
  unfold tailWord_402034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3665846156376738696463289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9775589750337969857235437 3665846156376738696463289)
  ·
    refine ⟨2749384617282554022347467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3665846156376738696463289 2749384617282554022347467)
    ·
      refine ⟨4124076925923831033521201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2749384617282554022347467 4124076925923831033521201)
      ·
        refine ⟨3093057694442873275140901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4124076925923831033521201 3093057694442873275140901)
        ·
          refine ⟨579948317708038739088919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3093057694442873275140901 579948317708038739088919)
          ·
            refine ⟨869922476562058108633379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 579948317708038739088919 869922476562058108633379)
            ·
              refine ⟨1304883714843087162950069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 869922476562058108633379 1304883714843087162950069)
              ·
                refine ⟨122332848266539421526569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1304883714843087162950069 122332848266539421526569)
                ·
                  rfl

theorem cell19_402034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_402034 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402034 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402034 prefixEnd_402034 := by exact prefixLift 402034
  have htrace : WordTrace (prefixWord ++ tailWord_402034) baseStart_402034 baseEnd_402034 := by
    simpa [prefixWord, tailWord_402034, baseEnd_402034] using wordTrace_append hprefix tailTrace_402034
  have hstable : (prefixWord ++ tailWord_402034).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402034).length < 2 ^ (prefixWord ++ tailWord_402034).sum := by decide
  have hdescent : baseEnd_402034 < baseStart_402034 := by decide
  rcases family_descends (prefixWord ++ tailWord_402034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402125 : List Nat := [1, 6, 2, 1, 2, 2, 1, 4]
def baseStart_402125 : Nat := 118140960795 + 402125 * 2 ^ 59
def prefixEnd_402125 : Nat := 4983230072969 + 3 ^ 40 * 402125 * 2
def baseEnd_402125 : Nat := 122360538186278173504099

theorem tailTrace_402125 : CollatzResearch.WordTrace tailWord_402125 prefixEnd_402125 122360538186278173504099 := by
  unfold tailWord_402125
  simp only [CollatzResearch.WordTrace]
  refine ⟨14666703668177277327415829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9777802445451518218277219 14666703668177277327415829)
  ·
    refine ⟨687501734445809874722617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14666703668177277327415829 687501734445809874722617)
    ·
      refine ⟨515626300834357406041963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 687501734445809874722617 515626300834357406041963)
      ·
        refine ⟨773439451251536109062945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 515626300834357406041963 773439451251536109062945)
        ·
          refine ⟨580079588438652081797209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 773439451251536109062945 580079588438652081797209)
          ·
            refine ⟨435059691328989061347907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 580079588438652081797209 435059691328989061347907)
            ·
              refine ⟨652589536993483592021861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435059691328989061347907 652589536993483592021861)
              ·
                refine ⟨122360538186278173504099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 652589536993483592021861 122360538186278173504099)
                ·
                  rfl

theorem cell19_402125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_402125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402125 prefixEnd_402125 := by exact prefixLift 402125
  have htrace : WordTrace (prefixWord ++ tailWord_402125) baseStart_402125 baseEnd_402125 := by
    simpa [prefixWord, tailWord_402125, baseEnd_402125] using wordTrace_append hprefix tailTrace_402125
  have hstable : (prefixWord ++ tailWord_402125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402125).length < 2 ^ (prefixWord ++ tailWord_402125).sum := by decide
  have hdescent : baseEnd_402125 < baseStart_402125 := by decide
  rcases family_descends (prefixWord ++ tailWord_402125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402148 : List Nat := [2, 3, 1, 1, 1, 5, 3, 3]
def baseStart_402148 : Nat := 118140960795 + 402148 * 2 ^ 59
def prefixEnd_402148 : Nat := 4983230072969 + 3 ^ 40 * 402148 * 2
def baseEnd_402148 : Nat := 122367536737420934992925

theorem tailTrace_402148 : CollatzResearch.WordTrace tailWord_402148 prefixEnd_402148 122367536737420934992925 := by
  unfold tailWord_402148
  simp only [CollatzResearch.WordTrace]
  refine ⟨7333771273546976127751549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9778361698062634837002065 7333771273546976127751549)
  ·
    refine ⟨2750164227580116047906831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7333771273546976127751549 2750164227580116047906831)
    ·
      refine ⟨4125246341370174071860247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2750164227580116047906831 4125246341370174071860247)
      ·
        refine ⟨6187869512055261107790371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4125246341370174071860247 6187869512055261107790371)
        ·
          refine ⟨9281804268082891661685557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6187869512055261107790371 9281804268082891661685557)
          ·
            refine ⟨870169150132771093283021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9281804268082891661685557 870169150132771093283021)
            ·
              refine ⟨326313431299789159981133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 870169150132771093283021 326313431299789159981133)
              ·
                refine ⟨122367536737420934992925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326313431299789159981133 122367536737420934992925)
                ·
                  rfl

theorem cell19_402148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 3].length) (baseStart_402148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402148 prefixEnd_402148 := by exact prefixLift 402148
  have htrace : WordTrace (prefixWord ++ tailWord_402148) baseStart_402148 baseEnd_402148 := by
    simpa [prefixWord, tailWord_402148, baseEnd_402148] using wordTrace_append hprefix tailTrace_402148
  have hstable : (prefixWord ++ tailWord_402148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402148).length < 2 ^ (prefixWord ++ tailWord_402148).sum := by decide
  have hdescent : baseEnd_402148 < baseStart_402148 := by decide
  rcases family_descends (prefixWord ++ tailWord_402148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402207 : List Nat := [1, 1, 2, 4, 2, 3, 1, 5]
def baseStart_402207 : Nat := 118140960795 + 402207 * 2 ^ 59
def prefixEnd_402207 : Nat := 4983230072969 + 3 ^ 40 * 402207 * 2
def baseEnd_402207 : Nat := 122385489542526279681653

theorem tailTrace_402207 : CollatzResearch.WordTrace tailWord_402207 prefixEnd_402207 122385489542526279681653 := by
  unfold tailWord_402207
  simp only [CollatzResearch.WordTrace]
  refine ⟨14669694453880205331900875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9779796302586803554600583 14669694453880205331900875)
  ·
    refine ⟨22004541680820307997851313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14669694453880205331900875 22004541680820307997851313)
    ·
      refine ⟨16503406260615230998388485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22004541680820307997851313 16503406260615230998388485)
      ·
        refine ⟨3094388673865355812197841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16503406260615230998388485 3094388673865355812197841)
        ·
          refine ⟨2320791505399016859148381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3094388673865355812197841 2320791505399016859148381)
          ·
            refine ⟨870296814524631322180643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2320791505399016859148381 870296814524631322180643)
            ·
              refine ⟨1305445221786946983270965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 870296814524631322180643 1305445221786946983270965)
              ·
                refine ⟨122385489542526279681653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1305445221786946983270965 122385489542526279681653)
                ·
                  rfl

theorem cell19_402207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 5].length) (baseStart_402207 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402207 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402207 prefixEnd_402207 := by exact prefixLift 402207
  have htrace : WordTrace (prefixWord ++ tailWord_402207) baseStart_402207 baseEnd_402207 := by
    simpa [prefixWord, tailWord_402207, baseEnd_402207] using wordTrace_append hprefix tailTrace_402207
  have hstable : (prefixWord ++ tailWord_402207).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402207).length < 2 ^ (prefixWord ++ tailWord_402207).sum := by decide
  have hdescent : baseEnd_402207 < baseStart_402207 := by decide
  rcases family_descends (prefixWord ++ tailWord_402207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402241 : List Nat := [1, 2, 5, 3, 1, 1, 2, 4]
def baseStart_402241 : Nat := 118140960795 + 402241 * 2 ^ 59
def prefixEnd_402241 : Nat := 4983230072969 + 3 ^ 40 * 402241 * 2
def baseEnd_402241 : Nat := 122395835226824274926005

theorem tailTrace_402241 : CollatzResearch.WordTrace tailWord_402241 prefixEnd_402241 122395835226824274926005 := by
  unfold tailWord_402241
  simp only [CollatzResearch.WordTrace]
  refine ⟨14670934535757029138638577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9780623023838019425759051 14670934535757029138638577)
  ·
    refine ⟨11003200901817771853978933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14670934535757029138638577 11003200901817771853978933)
    ·
      refine ⟨1031550084545416111310525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11003200901817771853978933 1031550084545416111310525)
      ·
        refine ⟨386831281704531041741447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1031550084545416111310525 386831281704531041741447)
        ·
          refine ⟨580246922556796562612171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386831281704531041741447 580246922556796562612171)
          ·
            refine ⟨870370383835194843918257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580246922556796562612171 870370383835194843918257)
            ·
              refine ⟨652777787876396132938693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870370383835194843918257 652777787876396132938693)
              ·
                refine ⟨122395835226824274926005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 652777787876396132938693 122395835226824274926005)
                ·
                  rfl

theorem cell19_402241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 4].length) (baseStart_402241 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402241 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402241 prefixEnd_402241 := by exact prefixLift 402241
  have htrace : WordTrace (prefixWord ++ tailWord_402241) baseStart_402241 baseEnd_402241 := by
    simpa [prefixWord, tailWord_402241, baseEnd_402241] using wordTrace_append hprefix tailTrace_402241
  have hstable : (prefixWord ++ tailWord_402241).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402241).length < 2 ^ (prefixWord ++ tailWord_402241).sum := by decide
  have hdescent : baseEnd_402241 < baseStart_402241 := by decide
  rcases family_descends (prefixWord ++ tailWord_402241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402304 : List Nat := [2, 1, 1, 2, 1, 2, 2, 8]
def baseStart_402304 : Nat := 118140960795 + 402304 * 2 ^ 59
def prefixEnd_402304 : Nat := 4983230072969 + 3 ^ 40 * 402304 * 2
def baseEnd_402304 : Nat := 122415005171258795525833

theorem tailTrace_402304 : CollatzResearch.WordTrace tailWord_402304 prefixEnd_402304 122415005171258795525833 := by
  unfold tailWord_402304
  simp only [CollatzResearch.WordTrace]
  refine ⟨7336616167264395449090983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9782154889685860598787977 7336616167264395449090983)
  ·
    refine ⟨11004924250896593173636475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7336616167264395449090983 11004924250896593173636475)
    ·
      refine ⟨16507386376344889760454713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11004924250896593173636475 16507386376344889760454713)
      ·
        refine ⟨12380539782258667320341035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16507386376344889760454713 12380539782258667320341035)
        ·
          refine ⟨18570809673388000980511553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12380539782258667320341035 18570809673388000980511553)
          ·
            refine ⟨13928107255041000735383665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18570809673388000980511553 13928107255041000735383665)
            ·
              refine ⟨10446080441280750551537749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13928107255041000735383665 10446080441280750551537749)
              ·
                refine ⟨122415005171258795525833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10446080441280750551537749 122415005171258795525833)
                ·
                  rfl

theorem cell19_402304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_402304 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402304 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402304 prefixEnd_402304 := by exact prefixLift 402304
  have htrace : WordTrace (prefixWord ++ tailWord_402304) baseStart_402304 baseEnd_402304 := by
    simpa [prefixWord, tailWord_402304, baseEnd_402304] using wordTrace_append hprefix tailTrace_402304
  have hstable : (prefixWord ++ tailWord_402304).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402304).length < 2 ^ (prefixWord ++ tailWord_402304).sum := by decide
  have hdescent : baseEnd_402304 < baseStart_402304 := by decide
  rcases family_descends (prefixWord ++ tailWord_402304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402372 : List Nat := [2, 3, 3, 3, 1, 2, 2, 3]
def baseStart_402372 : Nat := 118140960795 + 402372 * 2 ^ 59
def prefixEnd_402372 : Nat := 4983230072969 + 3 ^ 40 * 402372 * 2
def baseEnd_402372 : Nat := 122435696539854786014537

theorem tailTrace_402372 : CollatzResearch.WordTrace tailWord_402372 prefixEnd_402372 122435696539854786014537 := by
  unfold tailWord_402372
  simp only [CollatzResearch.WordTrace]
  refine ⟨7337856249141219255828685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9783808332188292341104913 7337856249141219255828685)
  ·
    refine ⟨2751696093427957220935757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7337856249141219255828685 2751696093427957220935757)
    ·
      refine ⟨1031886035035483957850909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2751696093427957220935757 1031886035035483957850909)
      ·
        refine ⟨386957263138306484194091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1031886035035483957850909 386957263138306484194091)
        ·
          refine ⟨580435894707459726291137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 386957263138306484194091 580435894707459726291137)
          ·
            refine ⟨435326921030594794718353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 580435894707459726291137 435326921030594794718353)
            ·
              refine ⟨326495190772946096038765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 435326921030594794718353 326495190772946096038765)
              ·
                refine ⟨122435696539854786014537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326495190772946096038765 122435696539854786014537)
                ·
                  rfl

theorem cell19_402372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_402372 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402372 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402372 prefixEnd_402372 := by exact prefixLift 402372
  have htrace : WordTrace (prefixWord ++ tailWord_402372) baseStart_402372 baseEnd_402372 := by
    simpa [prefixWord, tailWord_402372, baseEnd_402372] using wordTrace_append hprefix tailTrace_402372
  have hstable : (prefixWord ++ tailWord_402372).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402372).length < 2 ^ (prefixWord ++ tailWord_402372).sum := by decide
  have hdescent : baseEnd_402372 < baseStart_402372 := by decide
  rcases family_descends (prefixWord ++ tailWord_402372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402397 : List Nat := [1, 4, 3, 1, 2, 1, 7]
def baseStart_402397 : Nat := 118140960795 + 402397 * 2 ^ 59
def prefixEnd_402397 : Nat := 4983230072969 + 3 ^ 40 * 402397 * 2
def baseEnd_402397 : Nat := 40814434553554045152971

theorem tailTrace_402397 : CollatzResearch.WordTrace tailWord_402397 prefixEnd_402397 40814434553554045152971 := by
  unfold tailWord_402397
  simp only [CollatzResearch.WordTrace]
  refine ⟨14676624323191867781317445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9784416215461245187544963 14676624323191867781317445)
  ·
    refine ⟨2751867060598475208997021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14676624323191867781317445 2751867060598475208997021)
    ·
      refine ⟨1031950147724428203373883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2751867060598475208997021 1031950147724428203373883)
      ·
        refine ⟨1547925221586642305060825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1031950147724428203373883 1547925221586642305060825)
        ·
          refine ⟨1160943916189981728795619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1547925221586642305060825 1160943916189981728795619)
          ·
            refine ⟨1741415874284972593193429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1160943916189981728795619 1741415874284972593193429)
            ·
              refine ⟨40814434553554045152971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1741415874284972593193429 40814434553554045152971)
              ·
                rfl

theorem cell19_402397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 7].length) (baseStart_402397 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402397 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402397 prefixEnd_402397 := by exact prefixLift 402397
  have htrace : WordTrace (prefixWord ++ tailWord_402397) baseStart_402397 baseEnd_402397 := by
    simpa [prefixWord, tailWord_402397, baseEnd_402397] using wordTrace_append hprefix tailTrace_402397
  have hstable : (prefixWord ++ tailWord_402397).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402397).length < 2 ^ (prefixWord ++ tailWord_402397).sum := by decide
  have hdescent : baseEnd_402397 < baseStart_402397 := by decide
  rcases family_descends (prefixWord ++ tailWord_402397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402414 : List Nat := [4, 1, 2, 1, 4, 1, 2, 4]
def baseStart_402414 : Nat := 118140960795 + 402414 * 2 ^ 59
def prefixEnd_402414 : Nat := 4983230072969 + 3 ^ 40 * 402414 * 2
def baseEnd_402414 : Nat := 122448476502811133081089

theorem tailTrace_402414 : CollatzResearch.WordTrace tailWord_402414 prefixEnd_402414 122448476502811133081089 := by
  unfold tailWord_402414
  simp only [CollatzResearch.WordTrace]
  refine ⟨1834655545516284960585787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9784829576086853123124197 1834655545516284960585787)
  ·
    refine ⟨2751983318274427440878681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1834655545516284960585787 2751983318274427440878681)
    ·
      refine ⟨2063987488705820580659011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2751983318274427440878681 2063987488705820580659011)
      ·
        refine ⟨3095981233058730870988517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2063987488705820580659011 3095981233058730870988517)
        ·
          refine ⟨580496481198512038310347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3095981233058730870988517 580496481198512038310347)
          ·
            refine ⟨870744721797768057465521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580496481198512038310347 870744721797768057465521)
            ·
              refine ⟨653058541348326043099141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 870744721797768057465521 653058541348326043099141)
              ·
                refine ⟨122448476502811133081089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 653058541348326043099141 122448476502811133081089)
                ·
                  rfl

theorem cell19_402414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_402414 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402414 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402414 prefixEnd_402414 := by exact prefixLift 402414
  have htrace : WordTrace (prefixWord ++ tailWord_402414) baseStart_402414 baseEnd_402414 := by
    simpa [prefixWord, tailWord_402414, baseEnd_402414] using wordTrace_append hprefix tailTrace_402414
  have hstable : (prefixWord ++ tailWord_402414).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402414).length < 2 ^ (prefixWord ++ tailWord_402414).sum := by decide
  have hdescent : baseEnd_402414 < baseStart_402414 := by decide
  rcases family_descends (prefixWord ++ tailWord_402414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402437 : List Nat := [1, 3, 1, 1, 2, 3, 1, 7]
def baseStart_402437 : Nat := 118140960795 + 402437 * 2 ^ 59
def prefixEnd_402437 : Nat := 4983230072969 + 3 ^ 40 * 402437 * 2
def baseEnd_402437 : Nat := 122455475053953894569915

theorem tailTrace_402437 : CollatzResearch.WordTrace tailWord_402437 prefixEnd_402437 122455475053953894569915 := by
  unfold tailWord_402437
  simp only [CollatzResearch.WordTrace]
  refine ⟨14678083243046954612773565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9785388828697969741849043 14678083243046954612773565)
  ·
    refine ⟨5504281216142607979790087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14678083243046954612773565 5504281216142607979790087)
    ·
      refine ⟨8256421824213911969685131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5504281216142607979790087 8256421824213911969685131)
      ·
        refine ⟨12384632736320867954527697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8256421824213911969685131 12384632736320867954527697)
        ·
          refine ⟨9288474552240650965895773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12384632736320867954527697 9288474552240650965895773)
          ·
            refine ⟨3483177957090244112210915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9288474552240650965895773 3483177957090244112210915)
            ·
              refine ⟨5224766935635366168316373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3483177957090244112210915 5224766935635366168316373)
              ·
                refine ⟨122455475053953894569915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5224766935635366168316373 122455475053953894569915)
                ·
                  rfl

theorem cell19_402437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 7].length) (baseStart_402437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402437 prefixEnd_402437 := by exact prefixLift 402437
  have htrace : WordTrace (prefixWord ++ tailWord_402437) baseStart_402437 baseEnd_402437 := by
    simpa [prefixWord, tailWord_402437, baseEnd_402437] using wordTrace_append hprefix tailTrace_402437
  have hstable : (prefixWord ++ tailWord_402437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402437).length < 2 ^ (prefixWord ++ tailWord_402437).sum := by decide
  have hdescent : baseEnd_402437 < baseStart_402437 := by decide
  rcases family_descends (prefixWord ++ tailWord_402437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402450 : List Nat := [3, 2, 5, 1, 1, 7]
def baseStart_402450 : Nat := 118140960795 + 402450 * 2 ^ 59
def prefixEnd_402450 : Nat := 4983230072969 + 3 ^ 40 * 402450 * 2
def baseEnd_402450 : Nat := 13606603417419301808999

theorem tailTrace_402450 : CollatzResearch.WordTrace tailWord_402450 prefixEnd_402450 13606603417419301808999 := by
  unfold tailWord_402450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3669639347999964458249201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9785704927999905221997869 3669639347999964458249201)
  ·
    refine ⟨2752229510999973343686901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3669639347999964458249201 2752229510999973343686901)
    ·
      refine ⟨258021516656247500970647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2752229510999973343686901 258021516656247500970647)
      ·
        refine ⟨387032274984371251455971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258021516656247500970647 387032274984371251455971)
        ·
          refine ⟨580548412476556877183957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387032274984371251455971 580548412476556877183957)
          ·
            refine ⟨13606603417419301808999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 580548412476556877183957 13606603417419301808999)
            ·
              rfl

theorem cell19_402450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 1, 7].length) (baseStart_402450 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402450 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402450 prefixEnd_402450 := by exact prefixLift 402450
  have htrace : WordTrace (prefixWord ++ tailWord_402450) baseStart_402450 baseEnd_402450 := by
    simpa [prefixWord, tailWord_402450, baseEnd_402450] using wordTrace_append hprefix tailTrace_402450
  have hstable : (prefixWord ++ tailWord_402450).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402450).length < 2 ^ (prefixWord ++ tailWord_402450).sum := by decide
  have hdescent : baseEnd_402450 < baseStart_402450 := by decide
  rcases family_descends (prefixWord ++ tailWord_402450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402456 : List Nat := [2, 1, 2, 3, 2, 9]
def baseStart_402456 : Nat := 118140960795 + 402456 * 2 ^ 59
def prefixEnd_402456 : Nat := 4983230072969 + 3 ^ 40 * 402456 * 2
def baseEnd_402456 : Nat := 13606806273974164460849

theorem tailTrace_402456 : CollatzResearch.WordTrace tailWord_402456 prefixEnd_402456 13606806273974164460849 := by
  unfold tailWord_402456
  simp only [CollatzResearch.WordTrace]
  refine ⟨7339388114989060428857611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9785850819985413905143481 7339388114989060428857611)
  ·
    refine ⟨11009082172483590643286417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7339388114989060428857611 11009082172483590643286417)
    ·
      refine ⟨8256811629362692982464813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11009082172483590643286417 8256811629362692982464813)
      ·
        refine ⟨3096304361011009868424305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8256811629362692982464813 3096304361011009868424305)
        ·
          refine ⟨2322228270758257401318229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3096304361011009868424305 2322228270758257401318229)
          ·
            refine ⟨13606806273974164460849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2322228270758257401318229 13606806273974164460849)
            ·
              rfl

theorem cell19_402456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 9].length) (baseStart_402456 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402456 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402456 prefixEnd_402456 := by exact prefixLift 402456
  have htrace : WordTrace (prefixWord ++ tailWord_402456) baseStart_402456 baseEnd_402456 := by
    simpa [prefixWord, tailWord_402456, baseEnd_402456] using wordTrace_append hprefix tailTrace_402456
  have hstable : (prefixWord ++ tailWord_402456).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402456).length < 2 ^ (prefixWord ++ tailWord_402456).sum := by decide
  have hdescent : baseEnd_402456 < baseStart_402456 := by decide
  rcases family_descends (prefixWord ++ tailWord_402456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402471 : List Nat := [1, 1, 7, 1, 1, 1, 3, 4]
def baseStart_402471 : Nat := 118140960795 + 402471 * 2 ^ 59
def prefixEnd_402471 : Nat := 4983230072969 + 3 ^ 40 * 402471 * 2
def baseEnd_402471 : Nat := 122465820738251889814267

theorem tailTrace_402471 : CollatzResearch.WordTrace tailWord_402471 prefixEnd_402471 122465820738251889814267 := by
  unfold tailWord_402471
  simp only [CollatzResearch.WordTrace]
  refine ⟨14679323324923778419511267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9786215549949185613007511 14679323324923778419511267)
  ·
    refine ⟨22018984987385667629266901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14679323324923778419511267 22018984987385667629266901)
    ·
      refine ⟨516069960641851585060943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 22018984987385667629266901 516069960641851585060943)
      ·
        refine ⟨774104940962777377591415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516069960641851585060943 774104940962777377591415)
        ·
          refine ⟨1161157411444166066387123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774104940962777377591415 1161157411444166066387123)
          ·
            refine ⟨1741736117166249099580685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1161157411444166066387123 1741736117166249099580685)
            ·
              refine ⟨653151043937343412342757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1741736117166249099580685 653151043937343412342757)
              ·
                refine ⟨122465820738251889814267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 653151043937343412342757 122465820738251889814267)
                ·
                  rfl

theorem cell19_402471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 3, 4].length) (baseStart_402471 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402471 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402471 prefixEnd_402471 := by exact prefixLift 402471
  have htrace : WordTrace (prefixWord ++ tailWord_402471) baseStart_402471 baseEnd_402471 := by
    simpa [prefixWord, tailWord_402471, baseEnd_402471] using wordTrace_append hprefix tailTrace_402471
  have hstable : (prefixWord ++ tailWord_402471).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402471).length < 2 ^ (prefixWord ++ tailWord_402471).sum := by decide
  have hdescent : baseEnd_402471 < baseStart_402471 := by decide
  rcases family_descends (prefixWord ++ tailWord_402471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402532 : List Nat := [2, 3, 1, 1, 2, 1, 1, 8]
def baseStart_402532 : Nat := 118140960795 + 402532 * 2 ^ 59
def prefixEnd_402532 : Nat := 4983230072969 + 3 ^ 40 * 402532 * 2
def baseEnd_402532 : Nat := 122484382113021822458545

theorem tailTrace_402532 : CollatzResearch.WordTrace tailWord_402532 prefixEnd_402532 122484382113021822458545 := by
  unfold tailWord_402532
  simp only [CollatzResearch.WordTrace]
  refine ⟨7340774088851392918740925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9787698785135190558321233 7340774088851392918740925)
  ·
    refine ⟨2752790283319272344527847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7340774088851392918740925 2752790283319272344527847)
    ·
      refine ⟨4129185424978908516791771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2752790283319272344527847 4129185424978908516791771)
      ·
        refine ⟨6193778137468362775187657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4129185424978908516791771 6193778137468362775187657)
        ·
          refine ⟨4645333603101272081390743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6193778137468362775187657 4645333603101272081390743)
          ·
            refine ⟨6968000404651908122086115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4645333603101272081390743 6968000404651908122086115)
            ·
              refine ⟨10452000606977862183129173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6968000404651908122086115 10452000606977862183129173)
              ·
                refine ⟨122484382113021822458545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10452000606977862183129173 122484382113021822458545)
                ·
                  rfl

theorem cell19_402532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_402532 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402532 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402532 prefixEnd_402532 := by exact prefixLift 402532
  have htrace : WordTrace (prefixWord ++ tailWord_402532) baseStart_402532 baseEnd_402532 := by
    simpa [prefixWord, tailWord_402532, baseEnd_402532] using wordTrace_append hprefix tailTrace_402532
  have hstable : (prefixWord ++ tailWord_402532).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402532).length < 2 ^ (prefixWord ++ tailWord_402532).sum := by decide
  have hdescent : baseEnd_402532 < baseStart_402532 := by decide
  rcases family_descends (prefixWord ++ tailWord_402532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402551 : List Nat := [1, 1, 3, 1, 1, 4, 3, 5]
def baseStart_402551 : Nat := 118140960795 + 402551 * 2 ^ 59
def prefixEnd_402551 : Nat := 4983230072969 + 3 ^ 40 * 402551 * 2
def baseEnd_402551 : Nat := 122490163524835408036271

theorem tailTrace_402551 : CollatzResearch.WordTrace tailWord_402551 prefixEnd_402551 122490163524835408036271 := by
  unfold tailWord_402551
  simp only [CollatzResearch.WordTrace]
  refine ⟨14682241164633952082423507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9788160776422634721615671 14682241164633952082423507)
  ·
    refine ⟨22023361746950928123635261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14682241164633952082423507 22023361746950928123635261)
    ·
      refine ⟨8258760655106598046363223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22023361746950928123635261 8258760655106598046363223)
      ·
        refine ⟨12388140982659897069544835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8258760655106598046363223 12388140982659897069544835)
        ·
          refine ⟨18582211473989845604317253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12388140982659897069544835 18582211473989845604317253)
          ·
            refine ⟨3484164651373096050809485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18582211473989845604317253 3484164651373096050809485)
            ·
              refine ⟨1306561744264911019053557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3484164651373096050809485 1306561744264911019053557)
              ·
                refine ⟨122490163524835408036271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1306561744264911019053557 122490163524835408036271)
                ·
                  rfl

theorem cell19_402551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 5].length) (baseStart_402551 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402551 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402551 prefixEnd_402551 := by exact prefixLift 402551
  have htrace : WordTrace (prefixWord ++ tailWord_402551) baseStart_402551 baseEnd_402551 := by
    simpa [prefixWord, tailWord_402551, baseEnd_402551] using wordTrace_append hprefix tailTrace_402551
  have hstable : (prefixWord ++ tailWord_402551).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402551).length < 2 ^ (prefixWord ++ tailWord_402551).sum := by decide
  have hdescent : baseEnd_402551 < baseStart_402551 := by decide
  rcases family_descends (prefixWord ++ tailWord_402551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402625 : List Nat := [1, 2, 6, 1, 1, 8]
def baseStart_402625 : Nat := 118140960795 + 402625 * 2 ^ 59
def prefixEnd_402625 : Nat := 4983230072969 + 3 ^ 40 * 402625 * 2
def baseEnd_402625 : Nat := 13612520066936129154625

theorem tailTrace_402625 : CollatzResearch.WordTrace tailWord_402625 prefixEnd_402625 13612520066936129154625 := by
  unfold tailWord_402625
  simp only [CollatzResearch.WordTrace]
  refine ⟨14684940166365862720617329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9789960110910575147078219 14684940166365862720617329)
  ·
    refine ⟨11013705124774397040462997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14684940166365862720617329 11013705124774397040462997)
    ·
      refine ⟨516267427723799861271703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11013705124774397040462997 516267427723799861271703)
      ·
        refine ⟨774401141585699791907555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516267427723799861271703 774401141585699791907555)
        ·
          refine ⟨1161601712378549687861333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774401141585699791907555 1161601712378549687861333)
          ·
            refine ⟨13612520066936129154625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1161601712378549687861333 13612520066936129154625)
            ·
              rfl

theorem cell19_402625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 8].length) (baseStart_402625 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402625 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402625 prefixEnd_402625 := by exact prefixLift 402625
  have htrace : WordTrace (prefixWord ++ tailWord_402625) baseStart_402625 baseEnd_402625 := by
    simpa [prefixWord, tailWord_402625, baseEnd_402625] using wordTrace_append hprefix tailTrace_402625
  have hstable : (prefixWord ++ tailWord_402625).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402625).length < 2 ^ (prefixWord ++ tailWord_402625).sum := by decide
  have hdescent : baseEnd_402625 < baseStart_402625 := by decide
  rcases family_descends (prefixWord ++ tailWord_402625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402661 : List Nat := [1, 3, 1, 4, 3, 1, 3, 3]
def baseStart_402661 : Nat := 118140960795 + 402661 * 2 ^ 59
def prefixEnd_402661 : Nat := 4983230072969 + 3 ^ 40 * 402661 * 2
def baseEnd_402661 : Nat := 122523634856387745591527

theorem tailTrace_402661 : CollatzResearch.WordTrace tailWord_402661 prefixEnd_402661 122523634856387745591527 := by
  unfold tailWord_402661
  simp only [CollatzResearch.WordTrace]
  refine ⟨14686253194235440868927837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9790835462823627245951891 14686253194235440868927837)
  ·
    refine ⟨5507344947838290325847939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14686253194235440868927837 5507344947838290325847939)
    ·
      refine ⟨8261017421757435488771909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5507344947838290325847939 8261017421757435488771909)
      ·
        refine ⟨1548940766579519154144733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8261017421757435488771909 1548940766579519154144733)
        ·
          refine ⟨580852787467319682804275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1548940766579519154144733 580852787467319682804275)
          ·
            refine ⟨871279181200979524206413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580852787467319682804275 871279181200979524206413)
            ·
              refine ⟨326729692950367321577405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 871279181200979524206413 326729692950367321577405)
              ·
                refine ⟨122523634856387745591527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 326729692950367321577405 122523634856387745591527)
                ·
                  rfl

theorem cell19_402661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 3, 3].length) (baseStart_402661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402661 prefixEnd_402661 := by exact prefixLift 402661
  have htrace : WordTrace (prefixWord ++ tailWord_402661) baseStart_402661 baseEnd_402661 := by
    simpa [prefixWord, tailWord_402661, baseEnd_402661] using wordTrace_append hprefix tailTrace_402661
  have hstable : (prefixWord ++ tailWord_402661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402661).length < 2 ^ (prefixWord ++ tailWord_402661).sum := by decide
  have hdescent : baseEnd_402661 < baseStart_402661 := by decide
  rcases family_descends (prefixWord ++ tailWord_402661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402720 : List Nat := [2, 1, 1, 5, 3, 1, 1, 5]
def baseStart_402720 : Nat := 118140960795 + 402720 * 2 ^ 59
def prefixEnd_402720 : Nat := 4983230072969 + 3 ^ 40 * 402720 * 2
def baseEnd_402720 : Nat := 122541587661493090280255

theorem tailTrace_402720 : CollatzResearch.WordTrace tailWord_402720 prefixEnd_402720 122541587661493090280255 := by
  unfold tailWord_402720
  simp only [CollatzResearch.WordTrace]
  refine ⟨7344202550510846972662807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9792270067347795963550409 7344202550510846972662807)
  ·
    refine ⟨11016303825766270458994211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7344202550510846972662807 11016303825766270458994211)
    ·
      refine ⟨16524455738649405688491317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11016303825766270458994211 16524455738649405688491317)
      ·
        refine ⟨1549167725498381783296061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16524455738649405688491317 1549167725498381783296061)
        ·
          refine ⟨580937897061893168736023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1549167725498381783296061 580937897061893168736023)
          ·
            refine ⟨871406845592839753104035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 580937897061893168736023 871406845592839753104035)
            ·
              refine ⟨1307110268389259629656053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 871406845592839753104035 1307110268389259629656053)
              ·
                refine ⟨122541587661493090280255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1307110268389259629656053 122541587661493090280255)
                ·
                  rfl

theorem cell19_402720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 5].length) (baseStart_402720 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402720 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402720 prefixEnd_402720 := by exact prefixLift 402720
  have htrace : WordTrace (prefixWord ++ tailWord_402720) baseStart_402720 baseEnd_402720 := by
    simpa [prefixWord, tailWord_402720, baseEnd_402720] using wordTrace_append hprefix tailTrace_402720
  have hstable : (prefixWord ++ tailWord_402720).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402720).length < 2 ^ (prefixWord ++ tailWord_402720).sum := by decide
  have hdescent : baseEnd_402720 < baseStart_402720 := by decide
  rcases family_descends (prefixWord ++ tailWord_402720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402741 : List Nat := [1, 3, 3, 1, 2, 2, 7]
def baseStart_402741 : Nat := 118140960795 + 402741 * 2 ^ 59
def prefixEnd_402741 : Nat := 4983230072969 + 3 ^ 40 * 402741 * 2
def baseEnd_402741 : Nat := 40849325880990421271177

theorem tailTrace_402741 : CollatzResearch.WordTrace tailWord_402741 prefixEnd_402741 40849325880990421271177 := by
  unfold tailWord_402741
  simp only [CollatzResearch.WordTrace]
  refine ⟨14689171033945614531840077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9792780689297076354560051 14689171033945614531840077)
  ·
    refine ⟨5508439137729605449440029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14689171033945614531840077 5508439137729605449440029)
    ·
      refine ⟨2065664676648602043540011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5508439137729605449440029 2065664676648602043540011)
      ·
        refine ⟨3098497014972903065310017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2065664676648602043540011 3098497014972903065310017)
        ·
          refine ⟨2323872761229677298982513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3098497014972903065310017 2323872761229677298982513)
          ·
            refine ⟨1742904570922257974236885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2323872761229677298982513 1742904570922257974236885)
            ·
              refine ⟨40849325880990421271177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1742904570922257974236885 40849325880990421271177)
              ·
                rfl

theorem cell19_402741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 7].length) (baseStart_402741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402741 prefixEnd_402741 := by exact prefixLift 402741
  have htrace : WordTrace (prefixWord ++ tailWord_402741) baseStart_402741 baseEnd_402741 := by
    simpa [prefixWord, tailWord_402741, baseEnd_402741] using wordTrace_append hprefix tailTrace_402741
  have hstable : (prefixWord ++ tailWord_402741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402741).length < 2 ^ (prefixWord ++ tailWord_402741).sum := by decide
  have hdescent : baseEnd_402741 < baseStart_402741 := by decide
  rcases family_descends (prefixWord ++ tailWord_402741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402756 : List Nat := [2, 3, 4, 1, 1, 2, 2, 4]
def baseStart_402756 : Nat := 118140960795 + 402756 * 2 ^ 59
def prefixEnd_402756 : Nat := 4983230072969 + 3 ^ 40 * 402756 * 2
def baseEnd_402756 : Nat := 122552541915455673480157

theorem tailTrace_402756 : CollatzResearch.WordTrace tailWord_402756 prefixEnd_402756 122552541915455673480157 := by
  unfold tailWord_402756
  simp only [CollatzResearch.WordTrace]
  refine ⟨7344859064445636046818061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9793145419260848062424081 7344859064445636046818061)
  ·
    refine ⟨2754322149167113517556773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7344859064445636046818061 2754322149167113517556773)
    ·
      refine ⟨516435402968833784541895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2754322149167113517556773 516435402968833784541895)
      ·
        refine ⟨774653104453250676812843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516435402968833784541895 774653104453250676812843)
        ·
          refine ⟨1161979656679876015219265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 774653104453250676812843 1161979656679876015219265)
          ·
            refine ⟨871484742509907011414449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1161979656679876015219265 871484742509907011414449)
            ·
              refine ⟨653613556882430258560837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 871484742509907011414449 653613556882430258560837)
              ·
                refine ⟨122552541915455673480157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 653613556882430258560837 122552541915455673480157)
                ·
                  rfl

theorem cell19_402756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 4].length) (baseStart_402756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402756 prefixEnd_402756 := by exact prefixLift 402756
  have htrace : WordTrace (prefixWord ++ tailWord_402756) baseStart_402756 baseEnd_402756 := by
    simpa [prefixWord, tailWord_402756, baseEnd_402756] using wordTrace_append hprefix tailTrace_402756
  have hstable : (prefixWord ++ tailWord_402756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402756).length < 2 ^ (prefixWord ++ tailWord_402756).sum := by decide
  have hdescent : baseEnd_402756 < baseStart_402756 := by decide
  rcases family_descends (prefixWord ++ tailWord_402756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402855 : List Nat := [1, 1, 6, 1, 1, 1, 8]
def baseStart_402855 : Nat := 118140960795 + 402855 * 2 ^ 59
def prefixEnd_402855 : Nat := 4983230072969 + 3 ^ 40 * 402855 * 2
def baseEnd_402855 : Nat := 40860888704617592426629

theorem tailTrace_402855 : CollatzResearch.WordTrace tailWord_402855 prefixEnd_402855 40860888704617592426629 := by
  unfold tailWord_402855
  simp only [CollatzResearch.WordTrace]
  refine ⟨14693328955532612001490019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9795552637021741334326679 14693328955532612001490019)
  ·
    refine ⟨22039993433298918002235029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14693328955532612001490019 22039993433298918002235029)
    ·
      refine ⟨1033124692185886781354767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22039993433298918002235029 1033124692185886781354767)
      ·
        refine ⟨1549687038278830172032151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1033124692185886781354767 1549687038278830172032151)
        ·
          refine ⟨2324530557418245258048227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1549687038278830172032151 2324530557418245258048227)
          ·
            refine ⟨3486795836127367887072341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2324530557418245258048227 3486795836127367887072341)
            ·
              refine ⟨40860888704617592426629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3486795836127367887072341 40860888704617592426629)
              ·
                rfl

theorem cell19_402855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 8].length) (baseStart_402855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402855 prefixEnd_402855 := by exact prefixLift 402855
  have htrace : WordTrace (prefixWord ++ tailWord_402855) baseStart_402855 baseEnd_402855 := by
    simpa [prefixWord, tailWord_402855, baseEnd_402855] using wordTrace_append hprefix tailTrace_402855
  have hstable : (prefixWord ++ tailWord_402855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402855).length < 2 ^ (prefixWord ++ tailWord_402855).sum := by decide
  have hdescent : baseEnd_402855 < baseStart_402855 := by decide
  rcases family_descends (prefixWord ++ tailWord_402855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_402984 : List Nat := [2, 1, 5, 2, 2, 2, 1, 4]
def baseStart_402984 : Nat := 118140960795 + 402984 * 2 ^ 59
def prefixEnd_402984 : Nat := 4983230072969 + 3 ^ 40 * 402984 * 2
def baseEnd_402984 : Nat := 122621918857218700412869

theorem tailTrace_402984 : CollatzResearch.WordTrace tailWord_402984 prefixEnd_402984 122621918857218700412869 := by
  unfold tailWord_402984
  simp only [CollatzResearch.WordTrace]
  refine ⟨7349016986032633516468003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9798689314710178021957337 7349016986032633516468003)
  ·
    refine ⟨11023525479048950274702005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7349016986032633516468003 11023525479048950274702005)
    ·
      refine ⟨1033455513660839088253313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11023525479048950274702005 1033455513660839088253313)
      ·
        refine ⟨775091635245629316189985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1033455513660839088253313 775091635245629316189985)
        ·
          refine ⟨581318726434221987142489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775091635245629316189985 581318726434221987142489)
          ·
            refine ⟨435989044825666490356867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581318726434221987142489 435989044825666490356867)
            ·
              refine ⟨653983567238499735535301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 435989044825666490356867 653983567238499735535301)
              ·
                refine ⟨122621918857218700412869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 653983567238499735535301 122621918857218700412869)
                ·
                  rfl

theorem cell19_402984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 4].length) (baseStart_402984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_402984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_402984 prefixEnd_402984 := by exact prefixLift 402984
  have htrace : WordTrace (prefixWord ++ tailWord_402984) baseStart_402984 baseEnd_402984 := by
    simpa [prefixWord, tailWord_402984, baseEnd_402984] using wordTrace_append hprefix tailTrace_402984
  have hstable : (prefixWord ++ tailWord_402984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_402984).length < 2 ^ (prefixWord ++ tailWord_402984).sum := by decide
  have hdescent : baseEnd_402984 < baseStart_402984 := by decide
  rcases family_descends (prefixWord ++ tailWord_402984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403026 : List Nat := [3, 2, 2, 1, 2, 3, 6]
def baseStart_403026 : Nat := 118140960795 + 403026 * 2 ^ 59
def prefixEnd_403026 : Nat := 4983230072969 + 3 ^ 40 * 403026 * 2
def baseEnd_403026 : Nat := 40878232940058349159807

theorem tailTrace_403026 : CollatzResearch.WordTrace tailWord_403026 prefixEnd_403026 40878232940058349159807 := by
  unfold tailWord_403026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3674891459478277051491233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9799710558608738803976621 3674891459478277051491233)
  ·
    refine ⟨2756168594608707788618425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3674891459478277051491233 2756168594608707788618425)
    ·
      refine ⟨2067126445956530841463819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2756168594608707788618425 2067126445956530841463819)
      ·
        refine ⟨3100689668934796262195729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2067126445956530841463819 3100689668934796262195729)
        ·
          refine ⟨2325517251701097196646797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3100689668934796262195729 2325517251701097196646797)
          ·
            refine ⟨872068969387911448742549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2325517251701097196646797 872068969387911448742549)
            ·
              refine ⟨40878232940058349159807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 872068969387911448742549 40878232940058349159807)
              ·
                rfl

theorem cell19_403026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 6].length) (baseStart_403026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403026 prefixEnd_403026 := by exact prefixLift 403026
  have htrace : WordTrace (prefixWord ++ tailWord_403026) baseStart_403026 baseEnd_403026 := by
    simpa [prefixWord, tailWord_403026, baseEnd_403026] using wordTrace_append hprefix tailTrace_403026
  have hstable : (prefixWord ++ tailWord_403026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403026).length < 2 ^ (prefixWord ++ tailWord_403026).sum := by decide
  have hdescent : baseEnd_403026 < baseStart_403026 := by decide
  rcases family_descends (prefixWord ++ tailWord_403026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403062 : List Nat := [5, 1, 1, 2, 2, 2, 1, 5]
def baseStart_403062 : Nat := 118140960795 + 403062 * 2 ^ 59
def prefixEnd_403062 : Nat := 4983230072969 + 3 ^ 40 * 403062 * 2
def baseEnd_403062 : Nat := 122645653074137630679323

theorem tailTrace_403062 : CollatzResearch.WordTrace tailWord_403062 prefixEnd_403062 122645653074137630679323 := by
  unfold tailWord_403062
  simp only [CollatzResearch.WordTrace]
  refine ⟨918804929111417897142215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9800585910521790902850293 918804929111417897142215)
  ·
    refine ⟨1378207393667126845713323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 918804929111417897142215 1378207393667126845713323)
    ·
      refine ⟨2067311090500690268569985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1378207393667126845713323 2067311090500690268569985)
      ·
        refine ⟨1550483317875517701427489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2067311090500690268569985 1550483317875517701427489)
        ·
          refine ⟨1162862488406638276070617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1550483317875517701427489 1162862488406638276070617)
          ·
            refine ⟨872146866304978707052963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1162862488406638276070617 872146866304978707052963)
            ·
              refine ⟨1308220299457468060579445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 872146866304978707052963 1308220299457468060579445)
              ·
                refine ⟨122645653074137630679323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1308220299457468060579445 122645653074137630679323)
                ·
                  rfl

theorem cell19_403062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_403062 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403062 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403062 prefixEnd_403062 := by exact prefixLift 403062
  have htrace : WordTrace (prefixWord ++ tailWord_403062) baseStart_403062 baseEnd_403062 := by
    simpa [prefixWord, tailWord_403062, baseEnd_403062] using wordTrace_append hprefix tailTrace_403062
  have hstable : (prefixWord ++ tailWord_403062).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403062).length < 2 ^ (prefixWord ++ tailWord_403062).sum := by decide
  have hdescent : baseEnd_403062 < baseStart_403062 := by decide
  rcases family_descends (prefixWord ++ tailWord_403062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403100 : List Nat := [2, 2, 3, 2, 3, 1, 2, 4]
def baseStart_403100 : Nat := 118140960795 + 403100 * 2 ^ 59
def prefixEnd_403100 : Nat := 4983230072969 + 3 ^ 40 * 403100 * 2
def baseEnd_403100 : Nat := 122657215897764801834775

theorem tailTrace_403100 : CollatzResearch.WordTrace tailWord_403100 prefixEnd_403100 122657215897764801834775 := by
  unfold tailWord_403100
  simp only [CollatzResearch.WordTrace]
  refine ⟨7351132419822509422079377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9801509893096679229439169 7351132419822509422079377)
  ·
    refine ⟨5513349314866882066559533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7351132419822509422079377 5513349314866882066559533)
    ·
      refine ⟨2067505993075080774959825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5513349314866882066559533 2067505993075080774959825)
      ·
        refine ⟨1550629494806310581219869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2067505993075080774959825 1550629494806310581219869)
        ·
          refine ⟨581486060552366467957451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1550629494806310581219869 581486060552366467957451)
          ·
            refine ⟨872229090828549701936177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581486060552366467957451 872229090828549701936177)
            ·
              refine ⟨654171818121412276452133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 872229090828549701936177 654171818121412276452133)
              ·
                refine ⟨122657215897764801834775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 654171818121412276452133 122657215897764801834775)
                ·
                  rfl

theorem cell19_403100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 2, 4].length) (baseStart_403100 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403100 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403100 prefixEnd_403100 := by exact prefixLift 403100
  have htrace : WordTrace (prefixWord ++ tailWord_403100) baseStart_403100 baseEnd_403100 := by
    simpa [prefixWord, tailWord_403100, baseEnd_403100] using wordTrace_append hprefix tailTrace_403100
  have hstable : (prefixWord ++ tailWord_403100).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403100).length < 2 ^ (prefixWord ++ tailWord_403100).sum := by decide
  have hdescent : baseEnd_403100 < baseStart_403100 := by decide
  rcases family_descends (prefixWord ++ tailWord_403100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403123 : List Nat := [1, 1, 1, 2, 3, 3, 1, 7]
def baseStart_403123 : Nat := 118140960795 + 403123 * 2 ^ 59
def prefixEnd_403123 : Nat := 4983230072969 + 3 ^ 40 * 403123 * 2
def baseEnd_403123 : Nat := 122664214448907563323601

theorem tailTrace_403123 : CollatzResearch.WordTrace tailWord_403123 prefixEnd_403123 122664214448907563323601 := by
  unfold tailWord_403123
  simp only [CollatzResearch.WordTrace]
  refine ⟨14703103718561693772246023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9802069145707795848164015 14703103718561693772246023)
  ·
    refine ⟨22054655577842540658369035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14703103718561693772246023 22054655577842540658369035)
    ·
      refine ⟨33081983366763810987553553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22054655577842540658369035 33081983366763810987553553)
      ·
        refine ⟨24811487525072858240665165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33081983366763810987553553 24811487525072858240665165)
        ·
          refine ⟨9304307821902321840249437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24811487525072858240665165 9304307821902321840249437)
          ·
            refine ⟨3489115433213370690093539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9304307821902321840249437 3489115433213370690093539)
            ·
              refine ⟨5233673149820056035140309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3489115433213370690093539 5233673149820056035140309)
              ·
                refine ⟨122664214448907563323601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5233673149820056035140309 122664214448907563323601)
                ·
                  rfl

theorem cell19_403123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_403123 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403123 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403123 prefixEnd_403123 := by exact prefixLift 403123
  have htrace : WordTrace (prefixWord ++ tailWord_403123) baseStart_403123 baseEnd_403123 := by
    simpa [prefixWord, tailWord_403123, baseEnd_403123] using wordTrace_append hprefix tailTrace_403123
  have hstable : (prefixWord ++ tailWord_403123).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403123).length < 2 ^ (prefixWord ++ tailWord_403123).sum := by decide
  have hdescent : baseEnd_403123 < baseStart_403123 := by decide
  rcases family_descends (prefixWord ++ tailWord_403123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403176 : List Nat := [2, 1, 4, 1, 3, 2, 3, 3]
def baseStart_403176 : Nat := 118140960795 + 403176 * 2 ^ 59
def prefixEnd_403176 : Nat := 4983230072969 + 3 ^ 40 * 403176 * 2
def baseEnd_403176 : Nat := 122680341545019144145679

theorem tailTrace_403176 : CollatzResearch.WordTrace tailWord_403176 prefixEnd_403176 122680341545019144145679 := by
  unfold tailWord_403176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7352518393684841911962691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9803357858246455882616921 7352518393684841911962691)
  ·
    refine ⟨11028777590527262867944037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7352518393684841911962691 11028777590527262867944037)
    ·
      refine ⟨2067895798223861787739507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11028777590527262867944037 2067895798223861787739507)
      ·
        refine ⟨3101843697335792681609261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2067895798223861787739507 3101843697335792681609261)
        ·
          refine ⟨1163191386500922255603473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3101843697335792681609261 1163191386500922255603473)
          ·
            refine ⟨872393539875691691702605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1163191386500922255603473 872393539875691691702605)
            ·
              refine ⟨327147577453384384388477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 872393539875691691702605 327147577453384384388477)
              ·
                refine ⟨122680341545019144145679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327147577453384384388477 122680341545019144145679)
                ·
                  rfl

theorem cell19_403176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_403176 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403176 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403176 prefixEnd_403176 := by exact prefixLift 403176
  have htrace : WordTrace (prefixWord ++ tailWord_403176) baseStart_403176 baseEnd_403176 := by
    simpa [prefixWord, tailWord_403176, baseEnd_403176] using wordTrace_append hprefix tailTrace_403176
  have hstable : (prefixWord ++ tailWord_403176).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403176).length < 2 ^ (prefixWord ++ tailWord_403176).sum := by decide
  have hdescent : baseEnd_403176 < baseStart_403176 := by decide
  rcases family_descends (prefixWord ++ tailWord_403176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403180 : List Nat := [2, 2, 1, 1, 2, 2, 2, 7]
def baseStart_403180 : Nat := 118140960795 + 403180 * 2 ^ 59
def prefixEnd_403180 : Nat := 4983230072969 + 3 ^ 40 * 403180 * 2
def baseEnd_403180 : Nat := 122681558684348320056779

theorem tailTrace_403180 : CollatzResearch.WordTrace tailWord_403180 prefixEnd_403180 122681558684348320056779 := by
  unfold tailWord_403180
  simp only [CollatzResearch.WordTrace]
  refine ⟨7352591339677596253535497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9803455119570128338047329 7352591339677596253535497)
  ·
    refine ⟨5514443504758197190151623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7352591339677596253535497 5514443504758197190151623)
    ·
      refine ⟨8271665257137295785227435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5514443504758197190151623 8271665257137295785227435)
      ·
        refine ⟨12407497885705943677841153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8271665257137295785227435 12407497885705943677841153)
        ·
          refine ⟨9305623414279457758380865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12407497885705943677841153 9305623414279457758380865)
          ·
            refine ⟨6979217560709593318785649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9305623414279457758380865 6979217560709593318785649)
            ·
              refine ⟨5234413170532194989089237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6979217560709593318785649 5234413170532194989089237)
              ·
                refine ⟨122681558684348320056779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5234413170532194989089237 122681558684348320056779)
                ·
                  rfl

theorem cell19_403180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_403180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403180 prefixEnd_403180 := by exact prefixLift 403180
  have htrace : WordTrace (prefixWord ++ tailWord_403180) baseStart_403180 baseEnd_403180 := by
    simpa [prefixWord, tailWord_403180, baseEnd_403180] using wordTrace_append hprefix tailTrace_403180
  have hstable : (prefixWord ++ tailWord_403180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403180).length < 2 ^ (prefixWord ++ tailWord_403180).sum := by decide
  have hdescent : baseEnd_403180 < baseStart_403180 := by decide
  rcases family_descends (prefixWord ++ tailWord_403180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403233 : List Nat := [1, 2, 3, 2, 1, 5, 2, 3]
def baseStart_403233 : Nat := 118140960795 + 403233 * 2 ^ 59
def prefixEnd_403233 : Nat := 4983230072969 + 3 ^ 40 * 403233 * 2
def baseEnd_403233 : Nat := 122697685780459900878857

theorem tailTrace_403233 : CollatzResearch.WordTrace tailWord_403233 prefixEnd_403233 122697685780459900878857 := by
  unfold tailWord_403233
  simp only [CollatzResearch.WordTrace]
  refine ⟨14707115748163182558750353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9804743832108788372500235 14707115748163182558750353)
  ·
    refine ⟨11030336811122386919062765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14707115748163182558750353 11030336811122386919062765)
    ·
      refine ⟨4136376304170895094648537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11030336811122386919062765 4136376304170895094648537)
      ·
        refine ⟨3102282228128171320986403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4136376304170895094648537 3102282228128171320986403)
        ·
          refine ⟨4653423342192256981479605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3102282228128171320986403 4653423342192256981479605)
          ·
            refine ⟨436258438330524092013713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4653423342192256981479605 436258438330524092013713)
            ·
              refine ⟨327193828747893069010285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436258438330524092013713 327193828747893069010285)
              ·
                refine ⟨122697685780459900878857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327193828747893069010285 122697685780459900878857)
                ·
                  rfl

theorem cell19_403233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 3].length) (baseStart_403233 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403233 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403233 prefixEnd_403233 := by exact prefixLift 403233
  have htrace : WordTrace (prefixWord ++ tailWord_403233) baseStart_403233 baseEnd_403233 := by
    simpa [prefixWord, tailWord_403233, baseEnd_403233] using wordTrace_append hprefix tailTrace_403233
  have hstable : (prefixWord ++ tailWord_403233).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403233).length < 2 ^ (prefixWord ++ tailWord_403233).sum := by decide
  have hdescent : baseEnd_403233 < baseStart_403233 := by decide
  rcases family_descends (prefixWord ++ tailWord_403233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403235 : List Nat := [1, 1, 1, 4, 2, 1, 6, 3]
def baseStart_403235 : Nat := 118140960795 + 403235 * 2 ^ 59
def prefixEnd_403235 : Nat := 4983230072969 + 3 ^ 40 * 403235 * 2
def baseEnd_403235 : Nat := 122698294350124488834407

theorem tailTrace_403235 : CollatzResearch.WordTrace tailWord_403235 prefixEnd_403235 122698294350124488834407 := by
  unfold tailWord_403235
  simp only [CollatzResearch.WordTrace]
  refine ⟨14707188694155936900323159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9804792462770624600215439 14707188694155936900323159)
  ·
    refine ⟨22060783041233905350484739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14707188694155936900323159 22060783041233905350484739)
    ·
      refine ⟨33091174561850858025727109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22060783041233905350484739 33091174561850858025727109)
      ·
        refine ⟨6204595230347035879823833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33091174561850858025727109 6204595230347035879823833)
        ·
          refine ⟨4653446422760276909867875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6204595230347035879823833 4653446422760276909867875)
          ·
            refine ⟨6980169634140415364801813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4653446422760276909867875 6980169634140415364801813)
            ·
              refine ⟨327195451600331970225085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6980169634140415364801813 327195451600331970225085)
              ·
                refine ⟨122698294350124488834407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327195451600331970225085 122698294350124488834407)
                ·
                  rfl

theorem cell19_403235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 6, 3].length) (baseStart_403235 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403235 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403235 prefixEnd_403235 := by exact prefixLift 403235
  have htrace : WordTrace (prefixWord ++ tailWord_403235) baseStart_403235 baseEnd_403235 := by
    simpa [prefixWord, tailWord_403235, baseEnd_403235] using wordTrace_append hprefix tailTrace_403235
  have hstable : (prefixWord ++ tailWord_403235).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403235).length < 2 ^ (prefixWord ++ tailWord_403235).sum := by decide
  have hdescent : baseEnd_403235 < baseStart_403235 := by decide
  rcases family_descends (prefixWord ++ tailWord_403235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403252 : List Nat := [2, 5, 1, 1, 2, 3, 5]
def baseStart_403252 : Nat := 118140960795 + 403252 * 2 ^ 59
def prefixEnd_403252 : Nat := 4983230072969 + 3 ^ 40 * 403252 * 2
def baseEnd_403252 : Nat := 40901155730757828818861

theorem tailTrace_403252 : CollatzResearch.WordTrace tailWord_403252 prefixEnd_403252 40901155730757828818861 := by
  unfold tailWord_403252
  simp only [CollatzResearch.WordTrace]
  refine ⟨7353904367547174401846005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9805205823396232535794673 7353904367547174401846005)
  ·
    refine ⟨689428534457547600173063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7353904367547174401846005 689428534457547600173063)
    ·
      refine ⟨1034142801686321400259595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 689428534457547600173063 1034142801686321400259595)
      ·
        refine ⟨1551214202529482100389393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1034142801686321400259595 1551214202529482100389393)
        ·
          refine ⟨1163410651897111575292045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1551214202529482100389393 1163410651897111575292045)
          ·
            refine ⟨436278994461416840734517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1163410651897111575292045 436278994461416840734517)
            ·
              refine ⟨40901155730757828818861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 436278994461416840734517 40901155730757828818861)
              ·
                rfl

theorem cell19_403252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 5].length) (baseStart_403252 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403252 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403252 prefixEnd_403252 := by exact prefixLift 403252
  have htrace : WordTrace (prefixWord ++ tailWord_403252) baseStart_403252 baseEnd_403252 := by
    simpa [prefixWord, tailWord_403252, baseEnd_403252] using wordTrace_append hprefix tailTrace_403252
  have hstable : (prefixWord ++ tailWord_403252).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403252).length < 2 ^ (prefixWord ++ tailWord_403252).sum := by decide
  have hdescent : baseEnd_403252 < baseStart_403252 := by decide
  rcases family_descends (prefixWord ++ tailWord_403252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403256 : List Nat := [2, 1, 2, 1, 3, 3, 7]
def baseStart_403256 : Nat := 118140960795 + 403256 * 2 ^ 59
def prefixEnd_403256 : Nat := 4983230072969 + 3 ^ 40 * 403256 * 2
def baseEnd_403256 : Nat := 40901561443867554122561

theorem tailTrace_403256 : CollatzResearch.WordTrace tailWord_403256 prefixEnd_403256 40901561443867554122561 := by
  unfold tailWord_403256
  simp only [CollatzResearch.WordTrace]
  refine ⟨7353977313539928743418811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9805303084719904991225081 7353977313539928743418811)
  ·
    refine ⟨11030965970309893115128217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7353977313539928743418811 11030965970309893115128217)
    ·
      refine ⟨8273224477732419836346163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11030965970309893115128217 8273224477732419836346163)
      ·
        refine ⟨12409836716598629754519245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8273224477732419836346163 12409836716598629754519245)
        ·
          refine ⟨4653688768724486157944717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12409836716598629754519245 4653688768724486157944717)
          ·
            refine ⟨1745133288271682309229269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4653688768724486157944717 1745133288271682309229269)
            ·
              refine ⟨40901561443867554122561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1745133288271682309229269 40901561443867554122561)
              ·
                rfl

theorem cell19_403256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 7].length) (baseStart_403256 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403256 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403256 prefixEnd_403256 := by exact prefixLift 403256
  have htrace : WordTrace (prefixWord ++ tailWord_403256) baseStart_403256 baseEnd_403256 := by
    simpa [prefixWord, tailWord_403256, baseEnd_403256] using wordTrace_append hprefix tailTrace_403256
  have hstable : (prefixWord ++ tailWord_403256).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403256).length < 2 ^ (prefixWord ++ tailWord_403256).sum := by decide
  have hdescent : baseEnd_403256 < baseStart_403256 := by decide
  rcases family_descends (prefixWord ++ tailWord_403256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403326 : List Nat := [4, 2, 3, 1, 1, 3, 1, 4]
def baseStart_403326 : Nat := 118140960795 + 403326 * 2 ^ 59
def prefixEnd_403326 : Nat := 4983230072969 + 3 ^ 40 * 403326 * 2
def baseEnd_403326 : Nat := 122725984269863240811937

theorem tailTrace_403326 : CollatzResearch.WordTrace tailWord_403326 prefixEnd_403326 122725984269863240811937 := by
  unfold tailWord_403326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1838813467103282430235729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9807005157884172961257221 1838813467103282430235729)
  ·
    refine ⟨1379110100327461822676797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1838813467103282430235729 1379110100327461822676797)
    ·
      refine ⟨517166287622798183503799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1379110100327461822676797 517166287622798183503799)
      ·
        refine ⟨775749431434197275255699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517166287622798183503799 775749431434197275255699)
        ·
          refine ⟨1163624147151295912883549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775749431434197275255699 1163624147151295912883549)
          ·
            refine ⟨436359055181735967331331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1163624147151295912883549 436359055181735967331331)
            ·
              refine ⟨654538582772603950996997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436359055181735967331331 654538582772603950996997)
              ·
                refine ⟨122725984269863240811937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 654538582772603950996997 122725984269863240811937)
                ·
                  rfl

theorem cell19_403326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_403326 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403326 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403326 prefixEnd_403326 := by exact prefixLift 403326
  have htrace : WordTrace (prefixWord ++ tailWord_403326) baseStart_403326 baseEnd_403326 := by
    simpa [prefixWord, tailWord_403326, baseEnd_403326] using wordTrace_append hprefix tailTrace_403326
  have hstable : (prefixWord ++ tailWord_403326).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403326).length < 2 ^ (prefixWord ++ tailWord_403326).sum := by decide
  have hdescent : baseEnd_403326 < baseStart_403326 := by decide
  rcases family_descends (prefixWord ++ tailWord_403326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403349 : List Nat := [1, 3, 2, 1, 1, 3, 5, 3]
def baseStart_403349 : Nat := 118140960795 + 403349 * 2 ^ 59
def prefixEnd_403349 : Nat := 4983230072969 + 3 ^ 40 * 403349 * 2
def baseEnd_403349 : Nat := 122732982821006002300763

theorem tailTrace_403349 : CollatzResearch.WordTrace tailWord_403349 prefixEnd_403349 122732982821006002300763 := by
  unfold tailWord_403349
  simp only [CollatzResearch.WordTrace]
  refine ⟨14711346615742934369973101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9807564410495289579982067 14711346615742934369973101)
  ·
    refine ⟨5516754980903600388739913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14711346615742934369973101 5516754980903600388739913)
    ·
      refine ⟨4137566235677700291554935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5516754980903600388739913 4137566235677700291554935)
      ·
        refine ⟨6206349353516550437332403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4137566235677700291554935 6206349353516550437332403)
        ·
          refine ⟨9309524030274825655998605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6206349353516550437332403 9309524030274825655998605)
          ·
            refine ⟨3491071511353059620999477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9309524030274825655998605 3491071511353059620999477)
            ·
              refine ⟨327287954189349339468701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3491071511353059620999477 327287954189349339468701)
              ·
                refine ⟨122732982821006002300763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327287954189349339468701 122732982821006002300763)
                ·
                  rfl

theorem cell19_403349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5, 3].length) (baseStart_403349 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403349 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403349 prefixEnd_403349 := by exact prefixLift 403349
  have htrace : WordTrace (prefixWord ++ tailWord_403349) baseStart_403349 baseEnd_403349 := by
    simpa [prefixWord, tailWord_403349, baseEnd_403349] using wordTrace_append hprefix tailTrace_403349
  have hstable : (prefixWord ++ tailWord_403349).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403349).length < 2 ^ (prefixWord ++ tailWord_403349).sum := by decide
  have hdescent : baseEnd_403349 < baseStart_403349 := by decide
  rcases family_descends (prefixWord ++ tailWord_403349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403404 : List Nat := [2, 2, 1, 4, 1, 4, 2, 3]
def baseStart_403404 : Nat := 118140960795 + 403404 * 2 ^ 59
def prefixEnd_403404 : Nat := 4983230072969 + 3 ^ 40 * 403404 * 2
def baseEnd_403404 : Nat := 122749718486782171078391

theorem tailTrace_403404 : CollatzResearch.WordTrace tailWord_403404 prefixEnd_403404 122749718486782171078391 := by
  unfold tailWord_403404
  simp only [CollatzResearch.WordTrace]
  refine ⟨7356676315271839381612633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9808901753695785842150177 7356676315271839381612633)
  ·
    refine ⟨5517507236453879536209475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7356676315271839381612633 5517507236453879536209475)
    ·
      refine ⟨8276260854680819304314213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5517507236453879536209475 8276260854680819304314213)
      ·
        refine ⟨1551798910252653619558915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8276260854680819304314213 1551798910252653619558915)
        ·
          refine ⟨2327698365378980429338373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1551798910252653619558915 2327698365378980429338373)
          ·
            refine ⟨436443443508558830500945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2327698365378980429338373 436443443508558830500945)
            ·
              refine ⟨327332582631419122875709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436443443508558830500945 327332582631419122875709)
              ·
                refine ⟨122749718486782171078391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327332582631419122875709 122749718486782171078391)
                ·
                  rfl

theorem cell19_403404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 2, 3].length) (baseStart_403404 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403404 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403404 prefixEnd_403404 := by exact prefixLift 403404
  have htrace : WordTrace (prefixWord ++ tailWord_403404) baseStart_403404 baseEnd_403404 := by
    simpa [prefixWord, tailWord_403404, baseEnd_403404] using wordTrace_append hprefix tailTrace_403404
  have hstable : (prefixWord ++ tailWord_403404).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403404).length < 2 ^ (prefixWord ++ tailWord_403404).sum := by decide
  have hdescent : baseEnd_403404 < baseStart_403404 := by decide
  rcases family_descends (prefixWord ++ tailWord_403404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403427 : List Nat := [1, 1, 1, 6, 1, 2, 7]
def baseStart_403427 : Nat := 118140960795 + 403427 * 2 ^ 59
def prefixEnd_403427 : Nat := 4983230072969 + 3 ^ 40 * 403427 * 2
def baseEnd_403427 : Nat := 40918905679308310855739

theorem tailTrace_403427 : CollatzResearch.WordTrace tailWord_403427 prefixEnd_403427 40918905679308310855739 := by
  unfold tailWord_403427
  simp only [CollatzResearch.WordTrace]
  refine ⟨14714191509460353691312535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9809461006306902460875023 14714191509460353691312535)
  ·
    refine ⟨22071287264190530536968803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14714191509460353691312535 22071287264190530536968803)
    ·
      refine ⟨33106930896285795805453205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22071287264190530536968803 33106930896285795805453205)
      ·
        refine ⟨1551887385763396678380619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33106930896285795805453205 1551887385763396678380619)
        ·
          refine ⟨2327831078645095017570929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1551887385763396678380619 2327831078645095017570929)
          ·
            refine ⟨1745873308983821263178197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2327831078645095017570929 1745873308983821263178197)
            ·
              refine ⟨40918905679308310855739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1745873308983821263178197 40918905679308310855739)
              ·
                rfl

theorem cell19_403427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 7].length) (baseStart_403427 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403427 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403427 prefixEnd_403427 := by exact prefixLift 403427
  have htrace : WordTrace (prefixWord ++ tailWord_403427) baseStart_403427 baseEnd_403427 := by
    simpa [prefixWord, tailWord_403427, baseEnd_403427] using wordTrace_append hprefix tailTrace_403427
  have hstable : (prefixWord ++ tailWord_403427).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403427).length < 2 ^ (prefixWord ++ tailWord_403427).sum := by decide
  have hdescent : baseEnd_403427 < baseStart_403427 := by decide
  rcases family_descends (prefixWord ++ tailWord_403427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403484 : List Nat := [2, 2, 3, 1, 3, 8]
def baseStart_403484 : Nat := 118140960795 + 403484 * 2 ^ 59
def prefixEnd_403484 : Nat := 4983230072969 + 3 ^ 40 * 403484 * 2
def baseEnd_403484 : Nat := 13641562363707298811155

theorem tailTrace_403484 : CollatzResearch.WordTrace tailWord_403484 prefixEnd_403484 13641562363707298811155 := by
  unfold tailWord_403484
  simp only [CollatzResearch.WordTrace]
  refine ⟨7358135235126926213068753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9810846980169234950758337 7358135235126926213068753)
  ·
    refine ⟨5518601426345194659801565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7358135235126926213068753 5518601426345194659801565)
    ·
      refine ⟨2069475534879447997425587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5518601426345194659801565 2069475534879447997425587)
      ·
        refine ⟨3104213302319171996138381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2069475534879447997425587 3104213302319171996138381)
        ·
          refine ⟨1164079988369689498551893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3104213302319171996138381 1164079988369689498551893)
          ·
            refine ⟨13641562363707298811155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1164079988369689498551893 13641562363707298811155)
            ·
              rfl

theorem cell19_403484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 8].length) (baseStart_403484 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403484 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403484 prefixEnd_403484 := by exact prefixLift 403484
  have htrace : WordTrace (prefixWord ++ tailWord_403484) baseStart_403484 baseEnd_403484 := by
    simpa [prefixWord, tailWord_403484, baseEnd_403484] using wordTrace_append hprefix tailTrace_403484
  have hstable : (prefixWord ++ tailWord_403484).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403484).length < 2 ^ (prefixWord ++ tailWord_403484).sum := by decide
  have hdescent : baseEnd_403484 < baseStart_403484 := by decide
  rcases family_descends (prefixWord ++ tailWord_403484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403520 : List Nat := [2, 1, 1, 2, 2, 5, 3, 3]
def baseStart_403520 : Nat := 118140960795 + 403520 * 2 ^ 59
def prefixEnd_403520 : Nat := 4983230072969 + 3 ^ 40 * 403520 * 2
def baseEnd_403520 : Nat := 122785015527328272500297

theorem tailTrace_403520 : CollatzResearch.WordTrace tailWord_403520 prefixEnd_403520 122785015527328272500297 := by
  unfold tailWord_403520
  simp only [CollatzResearch.WordTrace]
  refine ⟨7358791749061715287224007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9811722332082287049632009 7358791749061715287224007)
  ·
    refine ⟨11038187623592572930836011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7358791749061715287224007 11038187623592572930836011)
    ·
      refine ⟨16557281435388859396254017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11038187623592572930836011 16557281435388859396254017)
      ·
        refine ⟨12417961076541644547190513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16557281435388859396254017 12417961076541644547190513)
        ·
          refine ⟨9313470807406233410392885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12417961076541644547190513 9313470807406233410392885)
          ·
            refine ⟨873137888194334382224333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9313470807406233410392885 873137888194334382224333)
            ·
              refine ⟨327426708072875393334125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 873137888194334382224333 327426708072875393334125)
              ·
                refine ⟨122785015527328272500297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327426708072875393334125 122785015527328272500297)
                ·
                  rfl

theorem cell19_403520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 3].length) (baseStart_403520 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403520 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403520 prefixEnd_403520 := by exact prefixLift 403520
  have htrace : WordTrace (prefixWord ++ tailWord_403520) baseStart_403520 baseEnd_403520 := by
    simpa [prefixWord, tailWord_403520, baseEnd_403520] using wordTrace_append hprefix tailTrace_403520
  have hstable : (prefixWord ++ tailWord_403520).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403520).length < 2 ^ (prefixWord ++ tailWord_403520).sum := by decide
  have hdescent : baseEnd_403520 < baseStart_403520 := by decide
  rcases family_descends (prefixWord ++ tailWord_403520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403541 : List Nat := [1, 3, 2, 2, 1, 4, 6]
def baseStart_403541 : Nat := 118140960795 + 403541 * 2 ^ 59
def prefixEnd_403541 : Nat := 4983230072969 + 3 ^ 40 * 403541 * 2
def baseEnd_403541 : Nat := 40930468502935482011191

theorem tailTrace_403541 : CollatzResearch.WordTrace tailWord_403541 prefixEnd_403541 40930468502935482011191 := by
  unfold tailWord_403541
  simp only [CollatzResearch.WordTrace]
  refine ⟨14718349431047351160962477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9812232954031567440641651 14718349431047351160962477)
  ·
    refine ⟨5519381036642756685360929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14718349431047351160962477 5519381036642756685360929)
    ·
      refine ⟨4139535777482067514020697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5519381036642756685360929 4139535777482067514020697)
      ·
        refine ⟨3104651833111550635515523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4139535777482067514020697 3104651833111550635515523)
        ·
          refine ⟨4656977749667325953273285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3104651833111550635515523 4656977749667325953273285)
          ·
            refine ⟨873183328062623616238741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4656977749667325953273285 873183328062623616238741)
            ·
              refine ⟨40930468502935482011191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 873183328062623616238741 40930468502935482011191)
              ·
                rfl

theorem cell19_403541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 6].length) (baseStart_403541 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403541 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403541 prefixEnd_403541 := by exact prefixLift 403541
  have htrace : WordTrace (prefixWord ++ tailWord_403541) baseStart_403541 baseEnd_403541 := by
    simpa [prefixWord, tailWord_403541, baseEnd_403541] using wordTrace_append hprefix tailTrace_403541
  have hstable : (prefixWord ++ tailWord_403541).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403541).length < 2 ^ (prefixWord ++ tailWord_403541).sum := by decide
  have hdescent : baseEnd_403541 < baseStart_403541 := by decide
  rcases family_descends (prefixWord ++ tailWord_403541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403577 : List Nat := [1, 2, 1, 3, 4, 1, 4, 3]
def baseStart_403577 : Nat := 118140960795 + 403577 * 2 ^ 59
def prefixEnd_403577 : Nat := 4983230072969 + 3 ^ 40 * 403577 * 2
def baseEnd_403577 : Nat := 122802359762769029233475

theorem tailTrace_403577 : CollatzResearch.WordTrace tailWord_403577 prefixEnd_403577 122802359762769029233475 := by
  unfold tailWord_403577
  simp only [CollatzResearch.WordTrace]
  refine ⟨14719662458916929309272985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9813108305944619539515323 14719662458916929309272985)
  ·
    refine ⟨11039746844187696981954739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14719662458916929309272985 11039746844187696981954739)
    ·
      refine ⟨16559620266281545472932109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11039746844187696981954739 16559620266281545472932109)
      ·
        refine ⟨6209857599855579552349541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16559620266281545472932109 6209857599855579552349541)
        ·
          refine ⟨1164348299972921166065539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6209857599855579552349541 1164348299972921166065539)
          ·
            refine ⟨1746522449959381749098309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164348299972921166065539 1746522449959381749098309)
            ·
              refine ⟨327472959367384077955933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1746522449959381749098309 327472959367384077955933)
              ·
                refine ⟨122802359762769029233475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327472959367384077955933 122802359762769029233475)
                ·
                  rfl

theorem cell19_403577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 3].length) (baseStart_403577 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403577 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403577 prefixEnd_403577 := by exact prefixLift 403577
  have htrace : WordTrace (prefixWord ++ tailWord_403577) baseStart_403577 baseEnd_403577 := by
    simpa [prefixWord, tailWord_403577, baseEnd_403577] using wordTrace_append hprefix tailTrace_403577
  have hstable : (prefixWord ++ tailWord_403577).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403577).length < 2 ^ (prefixWord ++ tailWord_403577).sum := by decide
  have hdescent : baseEnd_403577 < baseStart_403577 := by decide
  rcases family_descends (prefixWord ++ tailWord_403577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403615 : List Nat := [1, 1, 2, 6, 1, 2, 2, 4]
def baseStart_403615 : Nat := 118140960795 + 403615 * 2 ^ 59
def prefixEnd_403615 : Nat := 4983230072969 + 3 ^ 40 * 403615 * 2
def baseEnd_403615 : Nat := 122813922586396200388927

theorem tailTrace_403615 : CollatzResearch.WordTrace tailWord_403615 prefixEnd_403615 122813922586396200388927 := by
  unfold tailWord_403615
  simp only [CollatzResearch.WordTrace]
  refine ⟨14721048432779261799156299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9814032288519507866104199 14721048432779261799156299)
  ·
    refine ⟨22081572649168892698734449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14721048432779261799156299 22081572649168892698734449)
    ·
      refine ⟨16561179486876669524050837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22081572649168892698734449 16561179486876669524050837)
      ·
        refine ⟨776305288447343883939883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16561179486876669524050837 776305288447343883939883)
        ·
          refine ⟨1164457932671015825909825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776305288447343883939883 1164457932671015825909825)
          ·
            refine ⟨873343449503261869432369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1164457932671015825909825 873343449503261869432369)
            ·
              refine ⟨655007587127446402074277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 873343449503261869432369 655007587127446402074277)
              ·
                refine ⟨122813922586396200388927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 655007587127446402074277 122813922586396200388927)
                ·
                  rfl

theorem cell19_403615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 4].length) (baseStart_403615 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403615 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403615 prefixEnd_403615 := by exact prefixLift 403615
  have htrace : WordTrace (prefixWord ++ tailWord_403615) baseStart_403615 baseEnd_403615 := by
    simpa [prefixWord, tailWord_403615, baseEnd_403615] using wordTrace_append hprefix tailTrace_403615
  have hstable : (prefixWord ++ tailWord_403615).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403615).length < 2 ^ (prefixWord ++ tailWord_403615).sum := by decide
  have hdescent : baseEnd_403615 < baseStart_403615 := by decide
  rcases family_descends (prefixWord ++ tailWord_403615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403617 : List Nat := [1, 2, 3, 3, 1, 2, 1, 6]
def baseStart_403617 : Nat := 118140960795 + 403617 * 2 ^ 59
def prefixEnd_403617 : Nat := 4983230072969 + 3 ^ 40 * 403617 * 2
def baseEnd_403617 : Nat := 122814531156060788344477

theorem tailTrace_403617 : CollatzResearch.WordTrace tailWord_403617 prefixEnd_403617 122814531156060788344477 := by
  unfold tailWord_403617
  simp only [CollatzResearch.WordTrace]
  refine ⟨14721121378772016140729105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9814080919181344093819403 14721121378772016140729105)
  ·
    refine ⟨11040841034079012105546829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14721121378772016140729105 11040841034079012105546829)
    ·
      refine ⟨4140315387779629539580061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11040841034079012105546829 4140315387779629539580061)
      ·
        refine ⟨1552618270417361077342523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4140315387779629539580061 1552618270417361077342523)
        ·
          refine ⟨2328927405626041616013785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1552618270417361077342523 2328927405626041616013785)
          ·
            refine ⟨1746695554219531212010339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2328927405626041616013785 1746695554219531212010339)
            ·
              refine ⟨2620043331329296818015509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1746695554219531212010339 2620043331329296818015509)
              ·
                refine ⟨122814531156060788344477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2620043331329296818015509 122814531156060788344477)
                ·
                  rfl

theorem cell19_403617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 6].length) (baseStart_403617 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403617 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403617 prefixEnd_403617 := by exact prefixLift 403617
  have htrace : WordTrace (prefixWord ++ tailWord_403617) baseStart_403617 baseEnd_403617 := by
    simpa [prefixWord, tailWord_403617, baseEnd_403617] using wordTrace_append hprefix tailTrace_403617
  have hstable : (prefixWord ++ tailWord_403617).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403617).length < 2 ^ (prefixWord ++ tailWord_403617).sum := by decide
  have hdescent : baseEnd_403617 < baseStart_403617 := by decide
  rcases family_descends (prefixWord ++ tailWord_403617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403670 : List Nat := [5, 2, 1, 2, 1, 1, 3, 4]
def baseStart_403670 : Nat := 118140960795 + 403670 * 2 ^ 59
def prefixEnd_403670 : Nat := 4983230072969 + 3 ^ 40 * 403670 * 2
def baseEnd_403670 : Nat := 122830658252172369166555

theorem tailTrace_403670 : CollatzResearch.WordTrace tailWord_403670 prefixEnd_403670 122830658252172369166555 := by
  unfold tailWord_403670
  simp only [CollatzResearch.WordTrace]
  refine ⟨920190902973750387025529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9815369631720004128272309 920190902973750387025529)
  ·
    refine ⟨690143177230312790269147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 920190902973750387025529 690143177230312790269147)
    ·
      refine ⟨1035214765845469185403721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 690143177230312790269147 1035214765845469185403721)
      ·
        refine ⟨776411074384101889052791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1035214765845469185403721 776411074384101889052791)
        ·
          refine ⟨1164616611576152833579187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776411074384101889052791 1164616611576152833579187)
          ·
            refine ⟨1746924917364229250368781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164616611576152833579187 1746924917364229250368781)
            ·
              refine ⟨655096844011585968888293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1746924917364229250368781 655096844011585968888293)
              ·
                refine ⟨122830658252172369166555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 655096844011585968888293 122830658252172369166555)
                ·
                  rfl

theorem cell19_403670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_403670 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403670 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403670 prefixEnd_403670 := by exact prefixLift 403670
  have htrace : WordTrace (prefixWord ++ tailWord_403670) baseStart_403670 baseEnd_403670 := by
    simpa [prefixWord, tailWord_403670, baseEnd_403670] using wordTrace_append hprefix tailTrace_403670
  have hstable : (prefixWord ++ tailWord_403670).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403670).length < 2 ^ (prefixWord ++ tailWord_403670).sum := by decide
  have hdescent : baseEnd_403670 < baseStart_403670 := by decide
  rcases family_descends (prefixWord ++ tailWord_403670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403672 : List Nat := [2, 1, 2, 2, 4, 3, 1, 4]
def baseStart_403672 : Nat := 118140960795 + 403672 * 2 ^ 59
def prefixEnd_403672 : Nat := 4983230072969 + 3 ^ 40 * 403672 * 2
def baseEnd_403672 : Nat := 122831266821836957122105

theorem tailTrace_403672 : CollatzResearch.WordTrace tailWord_403672 prefixEnd_403672 122831266821836957122105 := by
  unfold tailWord_403672
  simp only [CollatzResearch.WordTrace]
  refine ⟨7361563696786380266990635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9815418262381840355987513 7361563696786380266990635)
  ·
    refine ⟨11042345545179570400485953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7361563696786380266990635 11042345545179570400485953)
    ·
      refine ⟨8281759158884677800364465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11042345545179570400485953 8281759158884677800364465)
      ·
        refine ⟨6211319369163508350273349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8281759158884677800364465 6211319369163508350273349)
        ·
          refine ⟨1164622381718157815676253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6211319369163508350273349 1164622381718157815676253)
          ·
            refine ⟨436733393144309180878595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1164622381718157815676253 436733393144309180878595)
            ·
              refine ⟨655100089716463771317893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436733393144309180878595 655100089716463771317893)
              ·
                refine ⟨122831266821836957122105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 655100089716463771317893 122831266821836957122105)
                ·
                  rfl

theorem cell19_403672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_403672 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403672 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403672 prefixEnd_403672 := by exact prefixLift 403672
  have htrace : WordTrace (prefixWord ++ tailWord_403672) baseStart_403672 baseEnd_403672 := by
    simpa [prefixWord, tailWord_403672, baseEnd_403672] using wordTrace_append hprefix tailTrace_403672
  have hstable : (prefixWord ++ tailWord_403672).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403672).length < 2 ^ (prefixWord ++ tailWord_403672).sum := by decide
  have hdescent : baseEnd_403672 < baseStart_403672 := by decide
  rcases family_descends (prefixWord ++ tailWord_403672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403674 : List Nat := [3, 1, 1, 2, 2, 1, 5, 4]
def baseStart_403674 : Nat := 118140960795 + 403674 * 2 ^ 59
def prefixEnd_403674 : Nat := 4983230072969 + 3 ^ 40 * 403674 * 2
def baseEnd_403674 : Nat := 122831875391501545077655

theorem tailTrace_403674 : CollatzResearch.WordTrace tailWord_403674 prefixEnd_403674 122831875391501545077655 := by
  unfold tailWord_403674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3680800084891378718888519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9815466893043676583702717 3680800084891378718888519)
  ·
    refine ⟨5521200127337068078332779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3680800084891378718888519 5521200127337068078332779)
    ·
      refine ⟨8281800191005602117499169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5521200127337068078332779 8281800191005602117499169)
      ·
        refine ⟨6211350143254201588124377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8281800191005602117499169 6211350143254201588124377)
        ·
          refine ⟨4658512607440651191093283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6211350143254201588124377 4658512607440651191093283)
          ·
            refine ⟨6987768911160976786639925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4658512607440651191093283 6987768911160976786639925)
            ·
              refine ⟨655103335421341573747493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6987768911160976786639925 655103335421341573747493)
              ·
                refine ⟨122831875391501545077655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 655103335421341573747493 122831875391501545077655)
                ·
                  rfl

theorem cell19_403674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_403674 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403674 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403674 prefixEnd_403674 := by exact prefixLift 403674
  have htrace : WordTrace (prefixWord ++ tailWord_403674) baseStart_403674 baseEnd_403674 := by
    simpa [prefixWord, tailWord_403674, baseEnd_403674] using wordTrace_append hprefix tailTrace_403674
  have hstable : (prefixWord ++ tailWord_403674).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403674).length < 2 ^ (prefixWord ++ tailWord_403674).sum := by decide
  have hdescent : baseEnd_403674 < baseStart_403674 := by decide
  rcases family_descends (prefixWord ++ tailWord_403674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403746 : List Nat := [3, 3, 1, 1, 3, 3, 2, 3]
def baseStart_403746 : Nat := 118140960795 + 403746 * 2 ^ 59
def prefixEnd_403746 : Nat := 4983230072969 + 3 ^ 40 * 403746 * 2
def baseEnd_403746 : Nat := 122853783899426711477459

theorem tailTrace_403746 : CollatzResearch.WordTrace tailWord_403746 prefixEnd_403746 122853783899426711477459 := by
  unfold tailWord_403746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3681456598826167793043773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9817217596869780781450061 3681456598826167793043773)
  ·
    refine ⟨1380546224559812922391415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3681456598826167793043773 1380546224559812922391415)
    ·
      refine ⟨2070819336839719383587123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1380546224559812922391415 2070819336839719383587123)
      ·
        refine ⟨3106229005259579075380685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2070819336839719383587123 3106229005259579075380685)
        ·
          refine ⟨1164835876972342153267757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3106229005259579075380685 1164835876972342153267757)
          ·
            refine ⟨436813453864628307475409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1164835876972342153267757 436813453864628307475409)
            ·
              refine ⟨327610090398471230606557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436813453864628307475409 327610090398471230606557)
              ·
                refine ⟨122853783899426711477459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327610090398471230606557 122853783899426711477459)
                ·
                  rfl

theorem cell19_403746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 3].length) (baseStart_403746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403746 prefixEnd_403746 := by exact prefixLift 403746
  have htrace : WordTrace (prefixWord ++ tailWord_403746) baseStart_403746 baseEnd_403746 := by
    simpa [prefixWord, tailWord_403746, baseEnd_403746] using wordTrace_append hprefix tailTrace_403746
  have hstable : (prefixWord ++ tailWord_403746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403746).length < 2 ^ (prefixWord ++ tailWord_403746).sum := by decide
  have hdescent : baseEnd_403746 < baseStart_403746 := by decide
  rcases family_descends (prefixWord ++ tailWord_403746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403748 : List Nat := [2, 3, 1, 3, 1, 2, 4, 3]
def baseStart_403748 : Nat := 118140960795 + 403748 * 2 ^ 59
def prefixEnd_403748 : Nat := 4983230072969 + 3 ^ 40 * 403748 * 2
def baseEnd_403748 : Nat := 122854392469091299433009

theorem tailTrace_403748 : CollatzResearch.WordTrace tailWord_403748 prefixEnd_403748 122854392469091299433009 := by
  unfold tailWord_403748
  simp only [CollatzResearch.WordTrace]
  refine ⟨7362949670648712756873949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9817266227531617009165265 7362949670648712756873949)
  ·
    refine ⟨2761106126493267283827731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7362949670648712756873949 2761106126493267283827731)
    ·
      refine ⟨4141659189739900925741597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2761106126493267283827731 4141659189739900925741597)
      ·
        refine ⟨1553122196152462847153099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4141659189739900925741597 1553122196152462847153099)
        ·
          refine ⟨2329683294228694270729649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1553122196152462847153099 2329683294228694270729649)
          ·
            refine ⟨1747262470671520703047237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2329683294228694270729649 1747262470671520703047237)
            ·
              refine ⟨327611713250910131821357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1747262470671520703047237 327611713250910131821357)
              ·
                refine ⟨122854392469091299433009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327611713250910131821357 122854392469091299433009)
                ·
                  rfl

theorem cell19_403748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 3].length) (baseStart_403748 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403748 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403748 prefixEnd_403748 := by exact prefixLift 403748
  have htrace : WordTrace (prefixWord ++ tailWord_403748) baseStart_403748 baseEnd_403748 := by
    simpa [prefixWord, tailWord_403748, baseEnd_403748] using wordTrace_append hprefix tailTrace_403748
  have hstable : (prefixWord ++ tailWord_403748).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403748).length < 2 ^ (prefixWord ++ tailWord_403748).sum := by decide
  have hdescent : baseEnd_403748 < baseStart_403748 := by decide
  rcases family_descends (prefixWord ++ tailWord_403748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403769 : List Nat := [1, 2, 1, 6, 1, 1, 7]
def baseStart_403769 : Nat := 118140960795 + 403769 * 2 ^ 59
def prefixEnd_403769 : Nat := 4983230072969 + 3 ^ 40 * 403769 * 2
def baseEnd_403769 : Nat := 40953594150189824322095

theorem tailTrace_403769 : CollatzResearch.WordTrace tailWord_403769 prefixEnd_403769 40953594150189824322095 := by
  unfold tailWord_403769
  simp only [CollatzResearch.WordTrace]
  refine ⟨14726665274221346100262361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9817776849480897400174907 14726665274221346100262361)
  ·
    refine ⟨11044998955666009575196771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14726665274221346100262361 11044998955666009575196771)
    ·
      refine ⟨16567498433499014362795157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11044998955666009575196771 16567498433499014362795157)
      ·
        refine ⟨776601489070266298256023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16567498433499014362795157 776601489070266298256023)
        ·
          refine ⟨1164902233605399447384035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776601489070266298256023 1164902233605399447384035)
          ·
            refine ⟨1747353350408099171076053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1164902233605399447384035 1747353350408099171076053)
            ·
              refine ⟨40953594150189824322095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1747353350408099171076053 40953594150189824322095)
              ·
                rfl

theorem cell19_403769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 7].length) (baseStart_403769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403769 prefixEnd_403769 := by exact prefixLift 403769
  have htrace : WordTrace (prefixWord ++ tailWord_403769) baseStart_403769 baseEnd_403769 := by
    simpa [prefixWord, tailWord_403769, baseEnd_403769] using wordTrace_append hprefix tailTrace_403769
  have hstable : (prefixWord ++ tailWord_403769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403769).length < 2 ^ (prefixWord ++ tailWord_403769).sum := by decide
  have hdescent : baseEnd_403769 < baseStart_403769 := by decide
  rcases family_descends (prefixWord ++ tailWord_403769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403788 : List Nat := [2, 2, 1, 3, 2, 1, 4, 4]
def baseStart_403788 : Nat := 118140960795 + 403788 * 2 ^ 59
def prefixEnd_403788 : Nat := 4983230072969 + 3 ^ 40 * 403788 * 2
def baseEnd_403788 : Nat := 122866563862383058544011

theorem tailTrace_403788 : CollatzResearch.WordTrace tailWord_403788 prefixEnd_403788 122866563862383058544011 := by
  unfold tailWord_403788
  simp only [CollatzResearch.WordTrace]
  refine ⟨7363679130576256172602009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9818238840768341563469345 7363679130576256172602009)
  ·
    refine ⟨5522759347932192129451507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7363679130576256172602009 5522759347932192129451507)
    ·
      refine ⟨8284139021898288194177261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5522759347932192129451507 8284139021898288194177261)
      ·
        refine ⟨3106552133211858072816473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8284139021898288194177261 3106552133211858072816473)
        ·
          refine ⟨2329914099908893554612355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3106552133211858072816473 2329914099908893554612355)
          ·
            refine ⟨3494871149863340331918533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2329914099908893554612355 3494871149863340331918533)
            ·
              refine ⟨655288340599376312234725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3494871149863340331918533 655288340599376312234725)
              ·
                refine ⟨122866563862383058544011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 655288340599376312234725 122866563862383058544011)
                ·
                  rfl

theorem cell19_403788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_403788 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403788 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403788 prefixEnd_403788 := by exact prefixLift 403788
  have htrace : WordTrace (prefixWord ++ tailWord_403788) baseStart_403788 baseEnd_403788 := by
    simpa [prefixWord, tailWord_403788, baseEnd_403788] using wordTrace_append hprefix tailTrace_403788
  have hstable : (prefixWord ++ tailWord_403788).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403788).length < 2 ^ (prefixWord ++ tailWord_403788).sum := by decide
  have hdescent : baseEnd_403788 < baseStart_403788 := by decide
  rcases family_descends (prefixWord ++ tailWord_403788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403843 : List Nat := [1, 1, 1, 3, 6, 2, 1, 4]
def baseStart_403843 : Nat := 118140960795 + 403843 * 2 ^ 59
def prefixEnd_403843 : Nat := 4983230072969 + 3 ^ 40 * 403843 * 2
def baseEnd_403843 : Nat := 122883299528159227321639

theorem tailTrace_403843 : CollatzResearch.WordTrace tailWord_403843 prefixEnd_403843 122883299528159227321639 := by
  unfold tailWord_403843
  simp only [CollatzResearch.WordTrace]
  refine ⟨14729364275953256738456183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9819576183968837825637455 14729364275953256738456183)
  ·
    refine ⟨22094046413929885107684275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14729364275953256738456183 22094046413929885107684275)
    ·
      refine ⟨33141069620894827661526413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22094046413929885107684275 33141069620894827661526413)
      ·
        refine ⟨12427901107835560373072405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33141069620894827661526413 12427901107835560373072405)
        ·
          refine ⟨582557864429791892487769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12427901107835560373072405 582557864429791892487769)
          ·
            refine ⟨436918398322343919365827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 582557864429791892487769 436918398322343919365827)
            ·
              refine ⟨655377597483515879048741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436918398322343919365827 655377597483515879048741)
              ·
                refine ⟨122883299528159227321639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 655377597483515879048741 122883299528159227321639)
                ·
                  rfl

theorem cell19_403843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 1, 4].length) (baseStart_403843 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403843 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403843 prefixEnd_403843 := by exact prefixLift 403843
  have htrace : WordTrace (prefixWord ++ tailWord_403843) baseStart_403843 baseEnd_403843 := by
    simpa [prefixWord, tailWord_403843, baseEnd_403843] using wordTrace_append hprefix tailTrace_403843
  have hstable : (prefixWord ++ tailWord_403843).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403843).length < 2 ^ (prefixWord ++ tailWord_403843).sum := by decide
  have hdescent : baseEnd_403843 < baseStart_403843 := by decide
  rcases family_descends (prefixWord ++ tailWord_403843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403860 : List Nat := [2, 4, 2, 1, 3, 1, 3, 3]
def baseStart_403860 : Nat := 118140960795 + 403860 * 2 ^ 59
def prefixEnd_403860 : Nat := 4983230072969 + 3 ^ 40 * 403860 * 2
def baseEnd_403860 : Nat := 122888472370308224943815

theorem tailTrace_403860 : CollatzResearch.WordTrace tailWord_403860 prefixEnd_403860 122888472370308224943815 := by
  unfold tailWord_403860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7364992158445834320912517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9819989544594445761216689 7364992158445834320912517)
  ·
    refine ⟨1380936029708593935171097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7364992158445834320912517 1380936029708593935171097)
    ·
      refine ⟨1035702022281445451378323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1380936029708593935171097 1035702022281445451378323)
      ·
        refine ⟨1553553033422168177067485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1035702022281445451378323 1553553033422168177067485)
        ·
          refine ⟨582582387533313066400307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1553553033422168177067485 582582387533313066400307)
          ·
            refine ⟨873873581299969599600461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582582387533313066400307 873873581299969599600461)
            ·
              refine ⟨327702592987488599850173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 873873581299969599600461 327702592987488599850173)
              ·
                refine ⟨122888472370308224943815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327702592987488599850173 122888472370308224943815)
                ·
                  rfl

theorem cell19_403860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 3, 3].length) (baseStart_403860 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403860 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403860 prefixEnd_403860 := by exact prefixLift 403860
  have htrace : WordTrace (prefixWord ++ tailWord_403860) baseStart_403860 baseEnd_403860 := by
    simpa [prefixWord, tailWord_403860, baseEnd_403860] using wordTrace_append hprefix tailTrace_403860
  have hstable : (prefixWord ++ tailWord_403860).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403860).length < 2 ^ (prefixWord ++ tailWord_403860).sum := by decide
  have hdescent : baseEnd_403860 < baseStart_403860 := by decide
  rcases family_descends (prefixWord ++ tailWord_403860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403904 : List Nat := [2, 1, 1, 2, 3, 1, 1, 8]
def baseStart_403904 : Nat := 118140960795 + 403904 * 2 ^ 59
def prefixEnd_403904 : Nat := 4983230072969 + 3 ^ 40 * 403904 * 2
def baseEnd_403904 : Nat := 122901860902929159965917

theorem tailTrace_403904 : CollatzResearch.WordTrace tailWord_403904 prefixEnd_403904 122901860902929159965917 := by
  unfold tailWord_403904
  simp only [CollatzResearch.WordTrace]
  refine ⟨7365794564366132078213383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9821059419154842770951177 7365794564366132078213383)
  ·
    refine ⟨11048691846549198117320075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7365794564366132078213383 11048691846549198117320075)
    ·
      refine ⟨16573037769823797175980113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11048691846549198117320075 16573037769823797175980113)
      ·
        refine ⟨12429778327367847881985085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16573037769823797175980113 12429778327367847881985085)
        ·
          refine ⟨4661166872762942955744407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12429778327367847881985085 4661166872762942955744407)
          ·
            refine ⟨6991750309144414433616611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4661166872762942955744407 6991750309144414433616611)
            ·
              refine ⟨10487625463716621650424917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6991750309144414433616611 10487625463716621650424917)
              ·
                refine ⟨122901860902929159965917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10487625463716621650424917 122901860902929159965917)
                ·
                  rfl

theorem cell19_403904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_403904 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403904 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403904 prefixEnd_403904 := by exact prefixLift 403904
  have htrace : WordTrace (prefixWord ++ tailWord_403904) baseStart_403904 baseEnd_403904 := by
    simpa [prefixWord, tailWord_403904, baseEnd_403904] using wordTrace_append hprefix tailTrace_403904
  have hstable : (prefixWord ++ tailWord_403904).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403904).length < 2 ^ (prefixWord ++ tailWord_403904).sum := by decide
  have hdescent : baseEnd_403904 < baseStart_403904 := by decide
  rcases family_descends (prefixWord ++ tailWord_403904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_403961 : List Nat := [1, 2, 1, 3, 1, 2, 3, 6]
def baseStart_403961 : Nat := 118140960795 + 403961 * 2 ^ 59
def prefixEnd_403961 : Nat := 4983230072969 + 3 ^ 40 * 403961 * 2
def baseEnd_403961 : Nat := 122919205138369916699095

theorem tailTrace_403961 : CollatzResearch.WordTrace tailWord_403961 prefixEnd_403961 122919205138369916699095 := by
  unfold tailWord_403961
  simp only [CollatzResearch.WordTrace]
  refine ⟨14733668089525762891251737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9822445393017175260834491 14733668089525762891251737)
  ·
    refine ⟨11050251067144322168438803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14733668089525762891251737 11050251067144322168438803)
    ·
      refine ⟨16575376600716483252658205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11050251067144322168438803 16575376600716483252658205)
      ·
        refine ⟨6215766225268681219746827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16575376600716483252658205 6215766225268681219746827)
        ·
          refine ⟨9323649337903021829620241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6215766225268681219746827 9323649337903021829620241)
          ·
            refine ⟨6992737003427266372215181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9323649337903021829620241 6992737003427266372215181)
            ·
              refine ⟨2622276376285224889580693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6992737003427266372215181 2622276376285224889580693)
              ·
                refine ⟨122919205138369916699095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2622276376285224889580693 122919205138369916699095)
                ·
                  rfl

theorem cell19_403961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_403961 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_403961 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_403961 prefixEnd_403961 := by exact prefixLift 403961
  have htrace : WordTrace (prefixWord ++ tailWord_403961) baseStart_403961 baseEnd_403961 := by
    simpa [prefixWord, tailWord_403961, baseEnd_403961] using wordTrace_append hprefix tailTrace_403961
  have hstable : (prefixWord ++ tailWord_403961).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_403961).length < 2 ^ (prefixWord ++ tailWord_403961).sum := by decide
  have hdescent : baseEnd_403961 < baseStart_403961 := by decide
  rcases family_descends (prefixWord ++ tailWord_403961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404033 : List Nat := [1, 2, 5, 1, 1, 3, 3, 3]
def baseStart_404033 : Nat := 118140960795 + 404033 * 2 ^ 59
def prefixEnd_404033 : Nat := 4983230072969 + 3 ^ 40 * 404033 * 2
def baseEnd_404033 : Nat := 122941113646295083098899

theorem tailTrace_404033 : CollatzResearch.WordTrace tailWord_404033 prefixEnd_404033 122941113646295083098899 := by
  unfold tailWord_404033
  simp only [CollatzResearch.WordTrace]
  refine ⟨14736294145264919187872753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9824196096843279458581835 14736294145264919187872753)
  ·
    refine ⟨11052220608948689390904565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14736294145264919187872753 11052220608948689390904565)
    ·
      refine ⟨1036145682088939630397303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11052220608948689390904565 1036145682088939630397303)
      ·
        refine ⟨1554218523133409445595955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036145682088939630397303 1554218523133409445595955)
        ·
          refine ⟨2331327784700114168393933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1554218523133409445595955 2331327784700114168393933)
          ·
            refine ⟨874247919262542813147725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2331327784700114168393933 874247919262542813147725)
            ·
              refine ⟨327842969723453554930397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 874247919262542813147725 327842969723453554930397)
              ·
                refine ⟨122941113646295083098899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327842969723453554930397 122941113646295083098899)
                ·
                  rfl

theorem cell19_404033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 3].length) (baseStart_404033 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404033 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404033 prefixEnd_404033 := by exact prefixLift 404033
  have htrace : WordTrace (prefixWord ++ tailWord_404033) baseStart_404033 baseEnd_404033 := by
    simpa [prefixWord, tailWord_404033, baseEnd_404033] using wordTrace_append hprefix tailTrace_404033
  have hstable : (prefixWord ++ tailWord_404033).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404033).length < 2 ^ (prefixWord ++ tailWord_404033).sum := by decide
  have hdescent : baseEnd_404033 < baseStart_404033 := by decide
  rcases family_descends (prefixWord ++ tailWord_404033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404086 : List Nat := [5, 1, 1, 2, 4, 1, 2, 3]
def baseStart_404086 : Nat := 118140960795 + 404086 * 2 ^ 59
def prefixEnd_404086 : Nat := 4983230072969 + 3 ^ 40 * 404086 * 2
def baseEnd_404086 : Nat := 122957240742406663920977

theorem tailTrace_404086 : CollatzResearch.WordTrace tailWord_404086 prefixEnd_404086 122957240742406663920977 := by
  unfold tailWord_404086
  simp only [CollatzResearch.WordTrace]
  refine ⟨921139200879556827472007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9825484809381939493034741 921139200879556827472007)
  ·
    refine ⟨1381708801319335241208011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 921139200879556827472007 1381708801319335241208011)
    ·
      refine ⟨2072563201979002861812017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1381708801319335241208011 2072563201979002861812017)
      ·
        refine ⟨1554422401484252146359013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2072563201979002861812017 1554422401484252146359013)
        ·
          refine ⟨291454200278297277442315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1554422401484252146359013 291454200278297277442315)
          ·
            refine ⟨437181300417445916163473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291454200278297277442315 437181300417445916163473)
            ·
              refine ⟨327885975313084437122605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 437181300417445916163473 327885975313084437122605)
              ·
                refine ⟨122957240742406663920977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327885975313084437122605 122957240742406663920977)
                ·
                  rfl

theorem cell19_404086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_404086 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404086 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404086 prefixEnd_404086 := by exact prefixLift 404086
  have htrace : WordTrace (prefixWord ++ tailWord_404086) baseStart_404086 baseEnd_404086 := by
    simpa [prefixWord, tailWord_404086, baseEnd_404086] using wordTrace_append hprefix tailTrace_404086
  have hstable : (prefixWord ++ tailWord_404086).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404086).length < 2 ^ (prefixWord ++ tailWord_404086).sum := by decide
  have hdescent : baseEnd_404086 < baseStart_404086 := by decide
  rcases family_descends (prefixWord ++ tailWord_404086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404092 : List Nat := [2, 2, 2, 1, 1, 2, 6, 3]
def baseStart_404092 : Nat := 118140960795 + 404092 * 2 ^ 59
def prefixEnd_404092 : Nat := 4983230072969 + 3 ^ 40 * 404092 * 2
def baseEnd_404092 : Nat := 122959066451400427787627

theorem tailTrace_404092 : CollatzResearch.WordTrace tailWord_404092 prefixEnd_404092 122959066451400427787627 := by
  unfold tailWord_404092
  simp only [CollatzResearch.WordTrace]
  refine ⟨7369223026025586132135265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9825630701367448176180353 7369223026025586132135265)
  ·
    refine ⟨5526917269519189599101449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7369223026025586132135265 5526917269519189599101449)
    ·
      refine ⟨4145187952139392199326087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5526917269519189599101449 4145187952139392199326087)
      ·
        refine ⟨6217781928209088298989131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4145187952139392199326087 6217781928209088298989131)
        ·
          refine ⟨9326672892313632448483697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6217781928209088298989131 9326672892313632448483697)
          ·
            refine ⟨6995004669235224336362773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9326672892313632448483697 6995004669235224336362773)
            ·
              refine ⟨327890843870401140767005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6995004669235224336362773 327890843870401140767005)
              ·
                refine ⟨122959066451400427787627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327890843870401140767005 122959066451400427787627)
                ·
                  rfl

theorem cell19_404092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 3].length) (baseStart_404092 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404092 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404092 prefixEnd_404092 := by exact prefixLift 404092
  have htrace : WordTrace (prefixWord ++ tailWord_404092) baseStart_404092 baseEnd_404092 := by
    simpa [prefixWord, tailWord_404092, baseEnd_404092] using wordTrace_append hprefix tailTrace_404092
  have hstable : (prefixWord ++ tailWord_404092).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404092).length < 2 ^ (prefixWord ++ tailWord_404092).sum := by decide
  have hdescent : baseEnd_404092 < baseStart_404092 := by decide
  rcases family_descends (prefixWord ++ tailWord_404092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404149 : List Nat := [1, 3, 3, 3, 1, 1, 2, 5]
def baseStart_404149 : Nat := 118140960795 + 404149 * 2 ^ 59
def prefixEnd_404149 : Nat := 4983230072969 + 3 ^ 40 * 404149 * 2
def baseEnd_404149 : Nat := 122976410686841184520805

theorem tailTrace_404149 : CollatzResearch.WordTrace tailWord_404149 prefixEnd_404149 122976410686841184520805 := by
  unfold tailWord_404149
  simp only [CollatzResearch.WordTrace]
  refine ⟨14740525012844670999095501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9827016675229780666063667 14740525012844670999095501)
  ·
    refine ⟨5527696879816751624660813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14740525012844670999095501 5527696879816751624660813)
    ·
      refine ⟨2072886329931281859247805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5527696879816751624660813 2072886329931281859247805)
      ·
        refine ⟨777332373724230697217927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2072886329931281859247805 777332373724230697217927)
        ·
          refine ⟨1165998560586346045826891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777332373724230697217927 1165998560586346045826891)
          ·
            refine ⟨1748997840879519068740337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1165998560586346045826891 1748997840879519068740337)
            ·
              refine ⟨1311748380659639301555253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1748997840879519068740337 1311748380659639301555253)
              ·
                refine ⟨122976410686841184520805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1311748380659639301555253 122976410686841184520805)
                ·
                  rfl

theorem cell19_404149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 5].length) (baseStart_404149 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404149 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404149 prefixEnd_404149 := by exact prefixLift 404149
  have htrace : WordTrace (prefixWord ++ tailWord_404149) baseStart_404149 baseEnd_404149 := by
    simpa [prefixWord, tailWord_404149, baseEnd_404149] using wordTrace_append hprefix tailTrace_404149
  have hstable : (prefixWord ++ tailWord_404149).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404149).length < 2 ^ (prefixWord ++ tailWord_404149).sum := by decide
  have hdescent : baseEnd_404149 < baseStart_404149 := by decide
  rcases family_descends (prefixWord ++ tailWord_404149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404166 : List Nat := [6, 1, 2, 1, 9]
def baseStart_404166 : Nat := 118140960795 + 404166 * 2 ^ 59
def prefixEnd_404166 : Nat := 4983230072969 + 3 ^ 40 * 404166 * 2
def baseEnd_404166 : Nat := 4554873464036673412703

theorem tailTrace_404166 : CollatzResearch.WordTrace tailWord_404166 prefixEnd_404166 4554873464036673412703 := by
  unfold tailWord_404166
  simp only [CollatzResearch.WordTrace]
  refine ⟨460660782930721340702011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9827430035855388601642901 460660782930721340702011)
  ·
    refine ⟨690991174396082011053017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 460660782930721340702011 690991174396082011053017)
    ·
      refine ⟨518243380797061508289763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 690991174396082011053017 518243380797061508289763)
      ·
        refine ⟨777365071195592262434645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 518243380797061508289763 777365071195592262434645)
        ·
          refine ⟨4554873464036673412703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 777365071195592262434645 4554873464036673412703)
          ·
            rfl

theorem cell19_404166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 9].length) (baseStart_404166 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404166 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404166 prefixEnd_404166 := by exact prefixLift 404166
  have htrace : WordTrace (prefixWord ++ tailWord_404166) baseStart_404166 baseEnd_404166 := by
    simpa [prefixWord, tailWord_404166, baseEnd_404166] using wordTrace_append hprefix tailTrace_404166
  have hstable : (prefixWord ++ tailWord_404166).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404166).length < 2 ^ (prefixWord ++ tailWord_404166).sum := by decide
  have hdescent : baseEnd_404166 < baseStart_404166 := by decide
  rcases family_descends (prefixWord ++ tailWord_404166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404170 : List Nat := [3, 1, 2, 1, 4, 8]
def baseStart_404170 : Nat := 118140960795 + 404170 * 2 ^ 59
def prefixEnd_404170 : Nat := 4983230072969 + 3 ^ 40 * 404170 * 2
def baseEnd_404170 : Nat := 13664755629813262006009

theorem tailTrace_404170 : CollatzResearch.WordTrace tailWord_404170 prefixEnd_404170 13664755629813262006009 := by
  unfold tailWord_404170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3685322736442147896402491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9827527297179061057073309 3685322736442147896402491)
  ·
    refine ⟨5527984104663221844603737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3685322736442147896402491 5527984104663221844603737)
    ·
      refine ⟨4145988078497416383452803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5527984104663221844603737 4145988078497416383452803)
      ·
        refine ⟨6218982117746124575179205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4145988078497416383452803 6218982117746124575179205)
        ·
          refine ⟨1166059147077398357846101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6218982117746124575179205 1166059147077398357846101)
          ·
            refine ⟨13664755629813262006009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1166059147077398357846101 13664755629813262006009)
            ·
              rfl

theorem cell19_404170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 8].length) (baseStart_404170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404170 prefixEnd_404170 := by exact prefixLift 404170
  have htrace : WordTrace (prefixWord ++ tailWord_404170) baseStart_404170 baseEnd_404170 := by
    simpa [prefixWord, tailWord_404170, baseEnd_404170] using wordTrace_append hprefix tailTrace_404170
  have hstable : (prefixWord ++ tailWord_404170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404170).length < 2 ^ (prefixWord ++ tailWord_404170).sum := by decide
  have hdescent : baseEnd_404170 < baseStart_404170 := by decide
  rcases family_descends (prefixWord ++ tailWord_404170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404278 : List Nat := [5, 1, 2, 2, 3, 1, 5]
def baseStart_404278 : Nat := 118140960795 + 404278 * 2 ^ 59
def prefixEnd_404278 : Nat := 4983230072969 + 3 ^ 40 * 404278 * 2
def baseEnd_404278 : Nat := 41005221143402369217929

theorem tailTrace_404278 : CollatzResearch.WordTrace tailWord_404278 prefixEnd_404278 41005221143402369217929 := by
  unfold tailWord_404278
  simp only [CollatzResearch.WordTrace]
  refine ⟨921576876836082876908843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9830153352918217353694325 921576876836082876908843)
  ·
    refine ⟨1382365315254124315363265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 921576876836082876908843 1382365315254124315363265)
    ·
      refine ⟨1036773986440593236522449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1382365315254124315363265 1036773986440593236522449)
      ·
        refine ⟨777580489830444927391837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1036773986440593236522449 777580489830444927391837)
        ·
          refine ⟨291592683686416847771939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 777580489830444927391837 291592683686416847771939)
          ·
            refine ⟨437389025529625271657909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291592683686416847771939 437389025529625271657909)
            ·
              refine ⟨41005221143402369217929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 437389025529625271657909 41005221143402369217929)
              ·
                rfl

theorem cell19_404278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 5].length) (baseStart_404278 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404278 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404278 prefixEnd_404278 := by exact prefixLift 404278
  have htrace : WordTrace (prefixWord ++ tailWord_404278) baseStart_404278 baseEnd_404278 := by
    simpa [prefixWord, tailWord_404278, baseEnd_404278] using wordTrace_append hprefix tailTrace_404278
  have hstable : (prefixWord ++ tailWord_404278).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404278).length < 2 ^ (prefixWord ++ tailWord_404278).sum := by decide
  have hdescent : baseEnd_404278 < baseStart_404278 := by decide
  rcases family_descends (prefixWord ++ tailWord_404278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404282 : List Nat := [3, 1, 1, 1, 6, 2, 5]
def baseStart_404282 : Nat := 118140960795 + 404282 * 2 ^ 59
def prefixEnd_404282 : Nat := 4983230072969 + 3 ^ 40 * 404282 * 2
def baseEnd_404282 : Nat := 41005626856512094521629

theorem tailTrace_404282 : CollatzResearch.WordTrace tailWord_404282 prefixEnd_404282 41005626856512094521629 := by
  unfold tailWord_404282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3686343980340708678421775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9830250614241889809124733 3686343980340708678421775)
  ·
    refine ⟨5529515970511063017632663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3686343980340708678421775 5529515970511063017632663)
    ·
      refine ⟨8294273955766594526448995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5529515970511063017632663 8294273955766594526448995)
      ·
        refine ⟨12441410933649891789673493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8294273955766594526448995 12441410933649891789673493)
        ·
          refine ⟨583191137514838677640945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12441410933649891789673493 583191137514838677640945)
          ·
            refine ⟨437393353136129008230709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 583191137514838677640945 437393353136129008230709)
            ·
              refine ⟨41005626856512094521629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 437393353136129008230709 41005626856512094521629)
              ·
                rfl

theorem cell19_404282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 5].length) (baseStart_404282 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404282 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404282 prefixEnd_404282 := by exact prefixLift 404282
  have htrace : WordTrace (prefixWord ++ tailWord_404282) baseStart_404282 baseEnd_404282 := by
    simpa [prefixWord, tailWord_404282, baseEnd_404282] using wordTrace_append hprefix tailTrace_404282
  have hstable : (prefixWord ++ tailWord_404282).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404282).length < 2 ^ (prefixWord ++ tailWord_404282).sum := by decide
  have hdescent : baseEnd_404282 < baseStart_404282 := by decide
  rcases family_descends (prefixWord ++ tailWord_404282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404341 : List Nat := [1, 3, 4, 1, 1, 9]
def baseStart_404341 : Nat := 118140960795 + 404341 * 2 ^ 59
def prefixEnd_404341 : Nat := 4983230072969 + 3 ^ 40 * 404341 * 2
def baseEnd_404341 : Nat := 13670537041626847583735

theorem tailTrace_404341 : CollatzResearch.WordTrace tailWord_404341 prefixEnd_404341 13670537041626847583735 := by
  unfold tailWord_404341
  simp only [CollatzResearch.WordTrace]
  refine ⟨14747527828149087790084877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9831685218766058526723251 14747527828149087790084877)
  ·
    refine ⟨5530322935555907921281829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14747527828149087790084877 5530322935555907921281829)
    ·
      refine ⟨1036935550416732735240343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5530322935555907921281829 1036935550416732735240343)
      ·
        refine ⟨1555403325625099102860515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1036935550416732735240343 1555403325625099102860515)
        ·
          refine ⟨2333104988437648654290773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1555403325625099102860515 2333104988437648654290773)
          ·
            refine ⟨13670537041626847583735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2333104988437648654290773 13670537041626847583735)
            ·
              rfl

theorem cell19_404341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 9].length) (baseStart_404341 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404341 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404341 prefixEnd_404341 := by exact prefixLift 404341
  have htrace : WordTrace (prefixWord ++ tailWord_404341) baseStart_404341 baseEnd_404341 := by
    simpa [prefixWord, tailWord_404341, baseEnd_404341] using wordTrace_append hprefix tailTrace_404341
  have hstable : (prefixWord ++ tailWord_404341).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404341).length < 2 ^ (prefixWord ++ tailWord_404341).sum := by decide
  have hdescent : baseEnd_404341 < baseStart_404341 := by decide
  rcases family_descends (prefixWord ++ tailWord_404341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404434 : List Nat := [3, 2, 2, 3, 1, 2, 1, 5]
def baseStart_404434 : Nat := 118140960795 + 404434 * 2 ^ 59
def prefixEnd_404434 : Nat := 4983230072969 + 3 ^ 40 * 404434 * 2
def baseEnd_404434 : Nat := 123063131864044968186695

theorem tailTrace_404434 : CollatzResearch.WordTrace tailWord_404434 prefixEnd_404434 123063131864044968186695 := by
  unfold tailWord_404434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3687729954203041168305089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9833946544541443115480237 3687729954203041168305089)
  ·
    refine ⟨2765797465652280876228817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3687729954203041168305089 2765797465652280876228817)
    ·
      refine ⟨2074348099239210657171613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2765797465652280876228817 2074348099239210657171613)
      ·
        refine ⟨777880537214703996439355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2074348099239210657171613 777880537214703996439355)
        ·
          refine ⟨1166820805822055994659033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 777880537214703996439355 1166820805822055994659033)
          ·
            refine ⟨875115604366541995994275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1166820805822055994659033 875115604366541995994275)
            ·
              refine ⟨1312673406549812993991413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 875115604366541995994275 1312673406549812993991413)
              ·
                refine ⟨123063131864044968186695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1312673406549812993991413 123063131864044968186695)
                ·
                  rfl

theorem cell19_404434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 1, 5].length) (baseStart_404434 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404434 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404434 prefixEnd_404434 := by exact prefixLift 404434
  have htrace : WordTrace (prefixWord ++ tailWord_404434) baseStart_404434 baseEnd_404434 := by
    simpa [prefixWord, tailWord_404434, baseEnd_404434] using wordTrace_append hprefix tailTrace_404434
  have hstable : (prefixWord ++ tailWord_404434).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404434).length < 2 ^ (prefixWord ++ tailWord_404434).sum := by decide
  have hdescent : baseEnd_404434 < baseStart_404434 := by decide
  rcases family_descends (prefixWord ++ tailWord_404434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404455 : List Nat := [1, 1, 5, 2, 2, 1, 7]
def baseStart_404455 : Nat := 118140960795 + 404455 * 2 ^ 59
def prefixEnd_404455 : Nat := 4983230072969 + 3 ^ 40 * 404455 * 2
def baseEnd_404455 : Nat := 41023173948507713906657

theorem tailTrace_404455 : CollatzResearch.WordTrace tailWord_404455 prefixEnd_404455 41023173948507713906657 := by
  unfold tailWord_404455
  simp only [CollatzResearch.WordTrace]
  refine ⟨14751685749736085259734819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9834457166490723506489879 14751685749736085259734819)
  ·
    refine ⟨22127528624604127889602229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14751685749736085259734819 22127528624604127889602229)
    ·
      refine ⟨2074455808556636989650209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22127528624604127889602229 2074455808556636989650209)
      ·
        refine ⟨1555841856417477742237657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2074455808556636989650209 1555841856417477742237657)
        ·
          refine ⟨1166881392313108306678243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1555841856417477742237657 1166881392313108306678243)
          ·
            refine ⟨1750322088469662460017365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1166881392313108306678243 1750322088469662460017365)
            ·
              refine ⟨41023173948507713906657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1750322088469662460017365 41023173948507713906657)
              ·
                rfl

theorem cell19_404455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 7].length) (baseStart_404455 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404455 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404455 prefixEnd_404455 := by exact prefixLift 404455
  have htrace : WordTrace (prefixWord ++ tailWord_404455) baseStart_404455 baseEnd_404455 := by
    simpa [prefixWord, tailWord_404455, baseEnd_404455] using wordTrace_append hprefix tailTrace_404455
  have hstable : (prefixWord ++ tailWord_404455).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404455).length < 2 ^ (prefixWord ++ tailWord_404455).sum := by decide
  have hdescent : baseEnd_404455 < baseStart_404455 := by decide
  rcases family_descends (prefixWord ++ tailWord_404455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404512 : List Nat := [2, 1, 1, 7, 8]
def baseStart_404512 : Nat := 118140960795 + 404512 * 2 ^ 59
def prefixEnd_404512 : Nat := 4983230072969 + 3 ^ 40 * 404512 * 2
def baseEnd_404512 : Nat := 4558772817813477720487

theorem tailTrace_404512 : CollatzResearch.WordTrace tailWord_404512 prefixEnd_404512 4558772817813477720487 := by
  unfold tailWord_404512
  simp only [CollatzResearch.WordTrace]
  refine ⟨7376882355264791997279895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9835843140353055996373193 7376882355264791997279895)
  ·
    refine ⟨11065323532897187995919843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7376882355264791997279895 11065323532897187995919843)
    ·
      refine ⟨16597985299345781993879765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11065323532897187995919843 16597985299345781993879765)
      ·
        refine ⟨389015280453416765481557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 16597985299345781993879765 389015280453416765481557)
        ·
          refine ⟨4558772817813477720487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 389015280453416765481557 4558772817813477720487)
          ·
            rfl

theorem cell19_404512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 8].length) (baseStart_404512 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404512 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404512 prefixEnd_404512 := by exact prefixLift 404512
  have htrace : WordTrace (prefixWord ++ tailWord_404512) baseStart_404512 baseEnd_404512 := by
    simpa [prefixWord, tailWord_404512, baseEnd_404512] using wordTrace_append hprefix tailTrace_404512
  have hstable : (prefixWord ++ tailWord_404512).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404512).length < 2 ^ (prefixWord ++ tailWord_404512).sum := by decide
  have hdescent : baseEnd_404512 < baseStart_404512 := by decide
  rcases family_descends (prefixWord ++ tailWord_404512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404626 : List Nat := [3, 2, 3, 1, 1, 2, 7]
def baseStart_404626 : Nat := 118140960795 + 404626 * 2 ^ 59
def prefixEnd_404626 : Nat := 4983230072969 + 3 ^ 40 * 404626 * 2
def baseEnd_404626 : Nat := 41040518183948470639835

theorem tailTrace_404626 : CollatzResearch.WordTrace tailWord_404626 prefixEnd_404626 41040518183948470639835 := by
  unfold tailWord_404626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3689480658029145366052433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9838615088077720976139821 3689480658029145366052433)
  ·
    refine ⟨2767110493521859024539325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3689480658029145366052433 2767110493521859024539325)
    ·
      refine ⟨1037666435070697134202247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2767110493521859024539325 1037666435070697134202247)
      ·
        refine ⟨1556499652606045701303371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1037666435070697134202247 1556499652606045701303371)
        ·
          refine ⟨2334749478909068551955057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1556499652606045701303371 2334749478909068551955057)
          ·
            refine ⟨1751062109181801413966293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2334749478909068551955057 1751062109181801413966293)
            ·
              refine ⟨41040518183948470639835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1751062109181801413966293 41040518183948470639835)
              ·
                rfl

theorem cell19_404626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 7].length) (baseStart_404626 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404626 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404626 prefixEnd_404626 := by exact prefixLift 404626
  have htrace : WordTrace (prefixWord ++ tailWord_404626) baseStart_404626 baseEnd_404626 := by
    simpa [prefixWord, tailWord_404626, baseEnd_404626] using wordTrace_append hprefix tailTrace_404626
  have hstable : (prefixWord ++ tailWord_404626).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404626).length < 2 ^ (prefixWord ++ tailWord_404626).sum := by decide
  have hdescent : baseEnd_404626 < baseStart_404626 := by decide
  rcases family_descends (prefixWord ++ tailWord_404626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404645 : List Nat := [1, 3, 1, 2, 1, 5, 2, 4]
def baseStart_404645 : Nat := 118140960795 + 404645 * 2 ^ 59
def prefixEnd_404645 : Nat := 4983230072969 + 3 ^ 40 * 404645 * 2
def baseEnd_404645 : Nat := 123127335963658997497231

theorem tailTrace_404645 : CollatzResearch.WordTrace tailWord_404645 prefixEnd_404645 123127335963658997497231 := by
  unfold tailWord_404645
  simp only [CollatzResearch.WordTrace]
  refine ⟨14758615619047747709151389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9839077079365165139434259 14758615619047747709151389)
  ·
    refine ⟨5534480857142905390931771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14758615619047747709151389 5534480857142905390931771)
    ·
      refine ⟨8301721285714358086397657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5534480857142905390931771 8301721285714358086397657)
      ·
        refine ⟨6226290964285768564798243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8301721285714358086397657 6226290964285768564798243)
        ·
          refine ⟨9339436446428652847197365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6226290964285768564798243 9339436446428652847197365)
          ·
            refine ⟨875572166852686204424753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9339436446428652847197365 875572166852686204424753)
            ·
              refine ⟨656679125139514653318565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 875572166852686204424753 656679125139514653318565)
              ·
                refine ⟨123127335963658997497231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 656679125139514653318565 123127335963658997497231)
                ·
                  rfl

theorem cell19_404645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 2, 4].length) (baseStart_404645 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404645 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404645 prefixEnd_404645 := by exact prefixLift 404645
  have htrace : WordTrace (prefixWord ++ tailWord_404645) baseStart_404645 baseEnd_404645 := by
    simpa [prefixWord, tailWord_404645, baseEnd_404645] using wordTrace_append hprefix tailTrace_404645
  have hstable : (prefixWord ++ tailWord_404645).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404645).length < 2 ^ (prefixWord ++ tailWord_404645).sum := by decide
  have hdescent : baseEnd_404645 < baseStart_404645 := by decide
  rcases family_descends (prefixWord ++ tailWord_404645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404719 : List Nat := [1, 1, 2, 1, 7, 1, 3, 3]
def baseStart_404719 : Nat := 118140960795 + 404719 * 2 ^ 59
def prefixEnd_404719 : Nat := 4983230072969 + 3 ^ 40 * 404719 * 2
def baseEnd_404719 : Nat := 123149853041248751852585

theorem tailTrace_404719 : CollatzResearch.WordTrace tailWord_404719 prefixEnd_404719 123149853041248751852585 := by
  unfold tailWord_404719
  simp only [CollatzResearch.WordTrace]
  refine ⟨14761314620779658347345211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9840876413853105564896807 14761314620779658347345211)
  ·
    refine ⟨22141971931169487521017817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14761314620779658347345211 22141971931169487521017817)
    ·
      refine ⟨16606478948377115640763363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22141971931169487521017817 16606478948377115640763363)
      ·
        refine ⟨24909718422565673461145045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16606478948377115640763363 24909718422565673461145045)
        ·
          refine ⟨583821525528882971745587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 24909718422565673461145045 583821525528882971745587)
          ·
            refine ⟨875732288293324457618381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583821525528882971745587 875732288293324457618381)
            ·
              refine ⟨328399608109996671606893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 875732288293324457618381 328399608109996671606893)
              ·
                refine ⟨123149853041248751852585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328399608109996671606893 123149853041248751852585)
                ·
                  rfl

theorem cell19_404719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 3].length) (baseStart_404719 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404719 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404719 prefixEnd_404719 := by exact prefixLift 404719
  have htrace : WordTrace (prefixWord ++ tailWord_404719) baseStart_404719 baseEnd_404719 := by
    simpa [prefixWord, tailWord_404719, baseEnd_404719] using wordTrace_append hprefix tailTrace_404719
  have hstable : (prefixWord ++ tailWord_404719).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404719).length < 2 ^ (prefixWord ++ tailWord_404719).sum := by decide
  have hdescent : baseEnd_404719 < baseStart_404719 := by decide
  rcases family_descends (prefixWord ++ tailWord_404719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404738 : List Nat := [3, 4, 1, 1, 3, 1, 6]
def baseStart_404738 : Nat := 118140960795 + 404738 * 2 ^ 59
def prefixEnd_404738 : Nat := 4983230072969 + 3 ^ 40 * 404738 * 2
def baseEnd_404738 : Nat := 41051878151020779143437

theorem tailTrace_404738 : CollatzResearch.WordTrace tailWord_404738 prefixEnd_404738 41051878151020779143437 := by
  unfold tailWord_404738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3690501901927706148071717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9841338405140549728191245 3690501901927706148071717)
  ·
    refine ⟨691969106611444902763447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3690501901927706148071717 691969106611444902763447)
    ·
      refine ⟨1037953659917167354145171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 691969106611444902763447 1037953659917167354145171)
      ·
        refine ⟨1556930489875751031217757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1037953659917167354145171 1556930489875751031217757)
        ·
          refine ⟨583848933703406636706659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1556930489875751031217757 583848933703406636706659)
          ·
            refine ⟨875773400555109955059989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 583848933703406636706659 875773400555109955059989)
            ·
              refine ⟨41051878151020779143437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 875773400555109955059989 41051878151020779143437)
              ·
                rfl

theorem cell19_404738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 6].length) (baseStart_404738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404738 prefixEnd_404738 := by exact prefixLift 404738
  have htrace : WordTrace (prefixWord ++ tailWord_404738) baseStart_404738 baseEnd_404738 := by
    simpa [prefixWord, tailWord_404738, baseEnd_404738] using wordTrace_append hprefix tailTrace_404738
  have hstable : (prefixWord ++ tailWord_404738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404738).length < 2 ^ (prefixWord ++ tailWord_404738).sum := by decide
  have hdescent : baseEnd_404738 < baseStart_404738 := by decide
  rcases family_descends (prefixWord ++ tailWord_404738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404740 : List Nat := [2, 3, 2, 2, 2, 2, 6]
def baseStart_404740 : Nat := 118140960795 + 404740 * 2 ^ 59
def prefixEnd_404740 : Nat := 4983230072969 + 3 ^ 40 * 404740 * 2
def baseEnd_404740 : Nat := 41052081007575641795287

theorem tailTrace_404740 : CollatzResearch.WordTrace tailWord_404740 prefixEnd_404740 41052081007575641795287 := by
  unfold tailWord_404740
  simp only [CollatzResearch.WordTrace]
  refine ⟨7381040276851789466929837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9841387035802385955906449 7381040276851789466929837)
  ·
    refine ⟨2767890103819421050098689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7381040276851789466929837 2767890103819421050098689)
    ·
      refine ⟨2075917577864565787574017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2767890103819421050098689 2075917577864565787574017)
      ·
        refine ⟨1556938183398424340680513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2075917577864565787574017 1556938183398424340680513)
        ·
          refine ⟨1167703637548818255510385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1556938183398424340680513 1167703637548818255510385)
          ·
            refine ⟨875777728161613691632789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1167703637548818255510385 875777728161613691632789)
            ·
              refine ⟨41052081007575641795287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 875777728161613691632789 41052081007575641795287)
              ·
                rfl

theorem cell19_404740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 6].length) (baseStart_404740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404740 prefixEnd_404740 := by exact prefixLift 404740
  have htrace : WordTrace (prefixWord ++ tailWord_404740) baseStart_404740 baseEnd_404740 := by
    simpa [prefixWord, tailWord_404740, baseEnd_404740] using wordTrace_append hprefix tailTrace_404740
  have hstable : (prefixWord ++ tailWord_404740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404740).length < 2 ^ (prefixWord ++ tailWord_404740).sum := by decide
  have hdescent : baseEnd_404740 < baseStart_404740 := by decide
  rcases family_descends (prefixWord ++ tailWord_404740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404776 : List Nat := [2, 1, 5, 1, 2, 1, 4, 3]
def baseStart_404776 : Nat := 118140960795 + 404776 * 2 ^ 59
def prefixEnd_404776 : Nat := 4983230072969 + 3 ^ 40 * 404776 * 2
def baseEnd_404776 : Nat := 123167197276689508585763

theorem tailTrace_404776 : CollatzResearch.WordTrace tailWord_404776 prefixEnd_404776 123167197276689508585763 := by
  unfold tailWord_404776
  simp only [CollatzResearch.WordTrace]
  refine ⟨7381696790786578541085091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9842262387715438054780121 7381696790786578541085091)
  ·
    refine ⟨11072545186179867811627637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7381696790786578541085091 11072545186179867811627637)
    ·
      refine ⟨1038051111204362607340091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11072545186179867811627637 1038051111204362607340091)
      ·
        refine ⟨1557076666806543911010137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1038051111204362607340091 1557076666806543911010137)
        ·
          refine ⟨1167807500104907933257603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1557076666806543911010137 1167807500104907933257603)
          ·
            refine ⟨1751711250157361899886405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1167807500104907933257603 1751711250157361899886405)
            ·
              refine ⟨328445859404505356228701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1751711250157361899886405 328445859404505356228701)
              ·
                refine ⟨123167197276689508585763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328445859404505356228701 123167197276689508585763)
                ·
                  rfl

theorem cell19_404776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 3].length) (baseStart_404776 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404776 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404776 prefixEnd_404776 := by exact prefixLift 404776
  have htrace : WordTrace (prefixWord ++ tailWord_404776) baseStart_404776 baseEnd_404776 := by
    simpa [prefixWord, tailWord_404776, baseEnd_404776] using wordTrace_append hprefix tailTrace_404776
  have hstable : (prefixWord ++ tailWord_404776).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404776).length < 2 ^ (prefixWord ++ tailWord_404776).sum := by decide
  have hdescent : baseEnd_404776 < baseStart_404776 := by decide
  rcases family_descends (prefixWord ++ tailWord_404776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404799 : List Nat := [1, 1, 2, 2, 4, 2, 7]
def baseStart_404799 : Nat := 118140960795 + 404799 * 2 ^ 59
def prefixEnd_404799 : Nat := 4983230072969 + 3 ^ 40 * 404799 * 2
def baseEnd_404799 : Nat := 41058065275944090024863

theorem tailTrace_404799 : CollatzResearch.WordTrace tailWord_404799 prefixEnd_404799 41058065275944090024863 := by
  unfold tailWord_404799
  simp only [CollatzResearch.WordTrace]
  refine ⟨14764232460489832010257451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9842821640326554673504967 14764232460489832010257451)
  ·
    refine ⟨22146348690734748015386177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14764232460489832010257451 22146348690734748015386177)
    ·
      refine ⟨16609761518051061011539633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22146348690734748015386177 16609761518051061011539633)
      ·
        refine ⟨12457321138538295758654725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16609761518051061011539633 12457321138538295758654725)
        ·
          refine ⟨2335747713475930454747761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12457321138538295758654725 2335747713475930454747761)
          ·
            refine ⟨1751810785106947841060821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2335747713475930454747761 1751810785106947841060821)
            ·
              refine ⟨41058065275944090024863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1751810785106947841060821 41058065275944090024863)
              ·
                rfl

theorem cell19_404799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 7].length) (baseStart_404799 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404799 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404799 prefixEnd_404799 := by exact prefixLift 404799
  have htrace : WordTrace (prefixWord ++ tailWord_404799) baseStart_404799 baseEnd_404799 := by
    simpa [prefixWord, tailWord_404799, baseEnd_404799] using wordTrace_append hprefix tailTrace_404799
  have hstable : (prefixWord ++ tailWord_404799).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404799).length < 2 ^ (prefixWord ++ tailWord_404799).sum := by decide
  have hdescent : baseEnd_404799 < baseStart_404799 := by decide
  rcases family_descends (prefixWord ++ tailWord_404799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404837 : List Nat := [1, 3, 1, 3, 1, 2, 1, 7]
def baseStart_404837 : Nat := 118140960795 + 404837 * 2 ^ 59
def prefixEnd_404837 : Nat := 4983230072969 + 3 ^ 40 * 404837 * 2
def baseEnd_404837 : Nat := 123185758651459441230041

theorem tailTrace_404837 : CollatzResearch.WordTrace tailWord_404837 prefixEnd_404837 123185758651459441230041 := by
  unfold tailWord_404837
  simp only [CollatzResearch.WordTrace]
  refine ⟨14765618434352164500140765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9843745622901443000093843 14765618434352164500140765)
  ·
    refine ⟨5537106912882061687552787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14765618434352164500140765 5537106912882061687552787)
    ·
      refine ⟨8305660369323092531329181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5537106912882061687552787 8305660369323092531329181)
      ·
        refine ⟨3114622638496159699248443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8305660369323092531329181 3114622638496159699248443)
        ·
          refine ⟨4671933957744239548872665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3114622638496159699248443 4671933957744239548872665)
          ·
            refine ⟨3503950468308179661654499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4671933957744239548872665 3503950468308179661654499)
            ·
              refine ⟨5255925702462269492481749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3503950468308179661654499 5255925702462269492481749)
              ·
                refine ⟨123185758651459441230041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5255925702462269492481749 123185758651459441230041)
                ·
                  rfl

theorem cell19_404837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_404837 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404837 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404837 prefixEnd_404837 := by exact prefixLift 404837
  have htrace : WordTrace (prefixWord ++ tailWord_404837) baseStart_404837 baseEnd_404837 := by
    simpa [prefixWord, tailWord_404837, baseEnd_404837] using wordTrace_append hprefix tailTrace_404837
  have hstable : (prefixWord ++ tailWord_404837).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404837).length < 2 ^ (prefixWord ++ tailWord_404837).sum := by decide
  have hdescent : baseEnd_404837 < baseStart_404837 := by decide
  rcases family_descends (prefixWord ++ tailWord_404837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404913 : List Nat := [1, 2, 2, 4, 1, 1, 8]
def baseStart_404913 : Nat := 118140960795 + 404913 * 2 ^ 59
def prefixEnd_404913 : Nat := 4983230072969 + 3 ^ 40 * 404913 * 2
def baseEnd_404913 : Nat := 41069628099571261180315

theorem tailTrace_404913 : CollatzResearch.WordTrace tailWord_404913 prefixEnd_404913 41069628099571261180315 := by
  unfold tailWord_404913
  simp only [CollatzResearch.WordTrace]
  refine ⟨14768390382076829479907393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9845593588051219653271595 14768390382076829479907393)
  ·
    refine ⟨11076292786557622109930545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14768390382076829479907393 11076292786557622109930545)
    ·
      refine ⟨8307219589918216582447909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11076292786557622109930545 8307219589918216582447909)
      ·
        refine ⟨1557603673109665609208983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8307219589918216582447909 1557603673109665609208983)
        ·
          refine ⟨2336405509664498413813475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1557603673109665609208983 2336405509664498413813475)
          ·
            refine ⟨3504608264496747620720213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2336405509664498413813475 3504608264496747620720213)
            ·
              refine ⟨41069628099571261180315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3504608264496747620720213 41069628099571261180315)
              ·
                rfl

theorem cell19_404913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_404913 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404913 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404913 prefixEnd_404913 := by exact prefixLift 404913
  have htrace : WordTrace (prefixWord ++ tailWord_404913) baseStart_404913 baseEnd_404913 := by
    simpa [prefixWord, tailWord_404913, baseEnd_404913] using wordTrace_append hprefix tailTrace_404913
  have hstable : (prefixWord ++ tailWord_404913).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404913).length < 2 ^ (prefixWord ++ tailWord_404913).sum := by decide
  have hdescent : baseEnd_404913 < baseStart_404913 := by decide
  rcases family_descends (prefixWord ++ tailWord_404913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_404989 : List Nat := [1, 4, 1, 1, 1, 4, 1, 6]
def baseStart_404989 : Nat := 118140960795 + 404989 * 2 ^ 59
def prefixEnd_404989 : Nat := 4983230072969 + 3 ^ 40 * 404989 * 2
def baseEnd_404989 : Nat := 123232009945968125851849

theorem tailTrace_404989 : CollatzResearch.WordTrace tailWord_404989 prefixEnd_404989 123232009945968125851849 := by
  unfold tailWord_404989
  simp only [CollatzResearch.WordTrace]
  refine ⟨14771162329801494459674021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9847441553200996306449347 14771162329801494459674021)
  ·
    refine ⟨2769592936837780211188879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14771162329801494459674021 2769592936837780211188879)
    ·
      refine ⟨4154389405256670316783319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2769592936837780211188879 4154389405256670316783319)
      ·
        refine ⟨6231584107885005475174979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4154389405256670316783319 6231584107885005475174979)
        ·
          refine ⟨9347376161827508212762469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6231584107885005475174979 9347376161827508212762469)
          ·
            refine ⟨1752633030342657789892963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9347376161827508212762469 1752633030342657789892963)
            ·
              refine ⟨2628949545513986684839445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1752633030342657789892963 2628949545513986684839445)
              ·
                refine ⟨123232009945968125851849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2628949545513986684839445 123232009945968125851849)
                ·
                  rfl

theorem cell19_404989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_404989 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_404989 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_404989 prefixEnd_404989 := by exact prefixLift 404989
  have htrace : WordTrace (prefixWord ++ tailWord_404989) baseStart_404989 baseEnd_404989 := by
    simpa [prefixWord, tailWord_404989, baseEnd_404989] using wordTrace_append hprefix tailTrace_404989
  have hstable : (prefixWord ++ tailWord_404989).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_404989).length < 2 ^ (prefixWord ++ tailWord_404989).sum := by decide
  have hdescent : baseEnd_404989 < baseStart_404989 := by decide
  rcases family_descends (prefixWord ++ tailWord_404989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405027 : List Nat := [1, 1, 1, 4, 5, 7]
def baseStart_405027 : Nat := 118140960795 + 405027 * 2 ^ 59
def prefixEnd_405027 : Nat := 4983230072969 + 3 ^ 40 * 405027 * 2
def baseEnd_405027 : Nat := 13693730307732810778589

theorem tailTrace_405027 : CollatzResearch.WordTrace tailWord_405027 prefixEnd_405027 13693730307732810778589 := by
  unfold tailWord_405027
  simp only [CollatzResearch.WordTrace]
  refine ⟨14772548303663826949557335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9848365535775884633038223 14772548303663826949557335)
  ·
    refine ⟨22158822455495740424336003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14772548303663826949557335 22158822455495740424336003)
    ·
      refine ⟨33238233683243610636504005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22158822455495740424336003 33238233683243610636504005)
      ·
        refine ⟨6232168815608176994344501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33238233683243610636504005 6232168815608176994344501)
        ·
          refine ⟨584265826463266593219797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6232168815608176994344501 584265826463266593219797)
          ·
            refine ⟨13693730307732810778589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 584265826463266593219797 13693730307732810778589)
            ·
              rfl

theorem cell19_405027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 7].length) (baseStart_405027 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405027 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405027 prefixEnd_405027 := by exact prefixLift 405027
  have htrace : WordTrace (prefixWord ++ tailWord_405027) baseStart_405027 baseEnd_405027 := by
    simpa [prefixWord, tailWord_405027, baseEnd_405027] using wordTrace_append hprefix tailTrace_405027
  have hstable : (prefixWord ++ tailWord_405027).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405027).length < 2 ^ (prefixWord ++ tailWord_405027).sum := by decide
  have hdescent : baseEnd_405027 < baseStart_405027 := by decide
  rcases family_descends (prefixWord ++ tailWord_405027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405078 : List Nat := [5, 2, 2, 2, 1, 1, 6]
def baseStart_405078 : Nat := 118140960795 + 405078 * 2 ^ 59
def prefixEnd_405078 : Nat := 4983230072969 + 3 ^ 40 * 405078 * 2
def baseEnd_405078 : Nat := 41086363765347429957943

theorem tailTrace_405078 : CollatzResearch.WordTrace tailWord_405078 prefixEnd_405078 41086363765347429957943 := by
  unfold tailWord_405078
  simp only [CollatzResearch.WordTrace]
  refine ⟨923400526654941416228993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9849605617652708439775925 923400526654941416228993)
  ·
    refine ⟨692550394991206062171745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 923400526654941416228993 692550394991206062171745)
    ·
      refine ⟨519412796243404546628809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 692550394991206062171745 519412796243404546628809)
      ·
        refine ⟨389559597182553409971607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 519412796243404546628809 389559597182553409971607)
        ·
          refine ⟨584339395773830114957411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 389559597182553409971607 584339395773830114957411)
          ·
            refine ⟨876509093660745172436117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 584339395773830114957411 876509093660745172436117)
            ·
              refine ⟨41086363765347429957943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 876509093660745172436117 41086363765347429957943)
              ·
                rfl

theorem cell19_405078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 6].length) (baseStart_405078 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405078 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405078 prefixEnd_405078 := by exact prefixLift 405078
  have htrace : WordTrace (prefixWord ++ tailWord_405078) baseStart_405078 baseEnd_405078 := by
    simpa [prefixWord, tailWord_405078, baseEnd_405078] using wordTrace_append hprefix tailTrace_405078
  have hstable : (prefixWord ++ tailWord_405078).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405078).length < 2 ^ (prefixWord ++ tailWord_405078).sum := by decide
  have hdescent : baseEnd_405078 < baseStart_405078 := by decide
  rcases family_descends (prefixWord ++ tailWord_405078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405196 : List Nat := [2, 2, 1, 5, 3, 6]
def baseStart_405196 : Nat := 118140960795 + 405196 * 2 ^ 59
def prefixEnd_405196 : Nat := 4983230072969 + 3 ^ 40 * 405196 * 2
def baseEnd_405196 : Nat := 13699444100694775472365

theorem tailTrace_405196 : CollatzResearch.WordTrace tailWord_405196 prefixEnd_405196 13699444100694775472365 := by
  unfold tailWord_405196
  simp only [CollatzResearch.WordTrace]
  refine ⟨7389356120025784406229721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9852474826701045874972961 7389356120025784406229721)
  ·
    refine ⟨5542017090019338304672291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7389356120025784406229721 5542017090019338304672291)
    ·
      refine ⟨8313025635029007457008437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5542017090019338304672291 8313025635029007457008437)
      ·
        refine ⟨779346153283969449094541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8313025635029007457008437 779346153283969449094541)
        ·
          refine ⟨292254807481488543410453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 779346153283969449094541 292254807481488543410453)
          ·
            refine ⟨13699444100694775472365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 292254807481488543410453 13699444100694775472365)
            ·
              rfl

theorem cell19_405196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 6].length) (baseStart_405196 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405196 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405196 prefixEnd_405196 := by exact prefixLift 405196
  have htrace : WordTrace (prefixWord ++ tailWord_405196) baseStart_405196 baseEnd_405196 := by
    simpa [prefixWord, tailWord_405196, baseEnd_405196] using wordTrace_append hprefix tailTrace_405196
  have hstable : (prefixWord ++ tailWord_405196).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405196).length < 2 ^ (prefixWord ++ tailWord_405196).sum := by decide
  have hdescent : baseEnd_405196 < baseStart_405196 := by decide
  rcases family_descends (prefixWord ++ tailWord_405196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405234 : List Nat := [3, 2, 1, 3, 1, 1, 5, 3]
def baseStart_405234 : Nat := 118140960795 + 405234 * 2 ^ 59
def prefixEnd_405234 : Nat := 4983230072969 + 3 ^ 40 * 405234 * 2
def baseEnd_405234 : Nat := 123306559729880150406737

theorem tailTrace_405234 : CollatzResearch.WordTrace tailWord_405234 prefixEnd_405234 123306559729880150406737 := by
  unfold tailWord_405234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3695024553478475325585689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9853398809275934201561837 3695024553478475325585689)
  ·
    refine ⟨2771268415108856494189267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3695024553478475325585689 2771268415108856494189267)
    ·
      refine ⟨4156902622663284741283901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2771268415108856494189267 4156902622663284741283901)
      ·
        refine ⟨1558838483498731777981463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4156902622663284741283901 1558838483498731777981463)
        ·
          refine ⟨2338257725248097666972195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1558838483498731777981463 2338257725248097666972195)
          ·
            refine ⟨3507386587872146500458293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2338257725248097666972195 3507386587872146500458293)
            ·
              refine ⟨328817492613013734417965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3507386587872146500458293 328817492613013734417965)
              ·
                refine ⟨123306559729880150406737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328817492613013734417965 123306559729880150406737)
                ·
                  rfl

theorem cell19_405234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 5, 3].length) (baseStart_405234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405234 prefixEnd_405234 := by exact prefixLift 405234
  have htrace : WordTrace (prefixWord ++ tailWord_405234) baseStart_405234 baseEnd_405234 := by
    simpa [prefixWord, tailWord_405234, baseEnd_405234] using wordTrace_append hprefix tailTrace_405234
  have hstable : (prefixWord ++ tailWord_405234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405234).length < 2 ^ (prefixWord ++ tailWord_405234).sum := by decide
  have hdescent : baseEnd_405234 < baseStart_405234 := by decide
  rcases family_descends (prefixWord ++ tailWord_405234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405295 : List Nat := [1, 1, 2, 1, 2, 1, 2, 9]
def baseStart_405295 : Nat := 118140960795 + 405295 * 2 ^ 59
def prefixEnd_405295 : Nat := 4983230072969 + 3 ^ 40 * 405295 * 2
def baseEnd_405295 : Nat := 123325121104650083051015

theorem tailTrace_405295 : CollatzResearch.WordTrace tailWord_405295 prefixEnd_405295 123325121104650083051015 := by
  unfold tailWord_405295
  simp only [CollatzResearch.WordTrace]
  refine ⟨14782323066692908720313339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9854882044461939146875559 14782323066692908720313339)
  ·
    refine ⟨22173484600039363080470009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14782323066692908720313339 22173484600039363080470009)
    ·
      refine ⟨16630113450029522310352507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22173484600039363080470009 16630113450029522310352507)
      ·
        refine ⟨24945170175044283465528761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16630113450029522310352507 24945170175044283465528761)
        ·
          refine ⟨18708877631283212599146571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24945170175044283465528761 18708877631283212599146571)
          ·
            refine ⟨28063316446924818898719857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18708877631283212599146571 28063316446924818898719857)
            ·
              refine ⟨21047487335193614174039893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28063316446924818898719857 21047487335193614174039893)
              ·
                refine ⟨123325121104650083051015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21047487335193614174039893 123325121104650083051015)
                ·
                  rfl

theorem cell19_405295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_405295 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405295 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405295 prefixEnd_405295 := by exact prefixLift 405295
  have htrace : WordTrace (prefixWord ++ tailWord_405295) baseStart_405295 baseEnd_405295 := by
    simpa [prefixWord, tailWord_405295, baseEnd_405295] using wordTrace_append hprefix tailTrace_405295
  have hstable : (prefixWord ++ tailWord_405295).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405295).length < 2 ^ (prefixWord ++ tailWord_405295).sum := by decide
  have hdescent : baseEnd_405295 < baseStart_405295 := by decide
  rcases family_descends (prefixWord ++ tailWord_405295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405310 : List Nat := [4, 2, 1, 2, 2, 3, 5]
def baseStart_405310 : Nat := 118140960795 + 405310 * 2 ^ 59
def prefixEnd_405310 : Nat := 4983230072969 + 3 ^ 40 * 405310 * 2
def baseEnd_405310 : Nat := 41109895125711497572547

theorem tailTrace_405310 : CollatzResearch.WordTrace tailWord_405310 prefixEnd_405310 41109895125711497572547 := by
  unfold tailWord_405310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1847858770204820785263673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9855246774425710854739589 1847858770204820785263673)
  ·
    refine ⟨1385894077653615588947755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1847858770204820785263673 1385894077653615588947755)
    ·
      refine ⟨2078841116480423383421633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1385894077653615588947755 2078841116480423383421633)
      ·
        refine ⟨1559130837360317537566225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2078841116480423383421633 1559130837360317537566225)
        ·
          refine ⟨1169348128020238153174669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1559130837360317537566225 1169348128020238153174669)
          ·
            refine ⟨438505548007589307440501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1169348128020238153174669 438505548007589307440501)
            ·
              refine ⟨41109895125711497572547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 438505548007589307440501 41109895125711497572547)
              ·
                rfl

theorem cell19_405310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 5].length) (baseStart_405310 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405310 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405310 prefixEnd_405310 := by exact prefixLift 405310
  have htrace : WordTrace (prefixWord ++ tailWord_405310) baseStart_405310 baseEnd_405310 := by
    simpa [prefixWord, tailWord_405310, baseEnd_405310] using wordTrace_append hprefix tailTrace_405310
  have hstable : (prefixWord ++ tailWord_405310).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405310).length < 2 ^ (prefixWord ++ tailWord_405310).sum := by decide
  have hdescent : baseEnd_405310 < baseStart_405310 := by decide
  rcases family_descends (prefixWord ++ tailWord_405310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405384 : List Nat := [2, 1, 3, 3, 4, 1, 1, 4]
def baseStart_405384 : Nat := 118140960795 + 405384 * 2 ^ 59
def prefixEnd_405384 : Nat := 4983230072969 + 3 ^ 40 * 405384 * 2
def baseEnd_405384 : Nat := 123352202454724247072995

theorem tailTrace_405384 : CollatzResearch.WordTrace tailWord_405384 prefixEnd_405384 123352202454724247072995 := by
  unfold tailWord_405384
  simp only [CollatzResearch.WordTrace]
  refine ⟨7392784581685238460151603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9857046108913651280202137 7392784581685238460151603)
  ·
    refine ⟨11089176872527857690227405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7392784581685238460151603 11089176872527857690227405)
    ·
      refine ⟨4158441327197946633835277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11089176872527857690227405 4158441327197946633835277)
      ·
        refine ⟨1559415497699229987688229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4158441327197946633835277 1559415497699229987688229)
        ·
          refine ⟨292390405818605622691543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1559415497699229987688229 292390405818605622691543)
          ·
            refine ⟨438585608727908434037315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292390405818605622691543 438585608727908434037315)
            ·
              refine ⟨657878413091862651055973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438585608727908434037315 657878413091862651055973)
              ·
                refine ⟨123352202454724247072995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 657878413091862651055973 123352202454724247072995)
                ·
                  rfl

theorem cell19_405384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 4].length) (baseStart_405384 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405384 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405384 prefixEnd_405384 := by exact prefixLift 405384
  have htrace : WordTrace (prefixWord ++ tailWord_405384) baseStart_405384 baseEnd_405384 := by
    simpa [prefixWord, tailWord_405384, baseEnd_405384] using wordTrace_append hprefix tailTrace_405384
  have hstable : (prefixWord ++ tailWord_405384).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405384).length < 2 ^ (prefixWord ++ tailWord_405384).sum := by decide
  have hdescent : baseEnd_405384 < baseStart_405384 := by decide
  rcases family_descends (prefixWord ++ tailWord_405384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405405 : List Nat := [1, 4, 2, 1, 2, 3, 3, 3]
def baseStart_405405 : Nat := 118140960795 + 405405 * 2 ^ 59
def prefixEnd_405405 : Nat := 4983230072969 + 3 ^ 40 * 405405 * 2
def baseEnd_405405 : Nat := 123358592436202420606271

theorem tailTrace_405405 : CollatzResearch.WordTrace tailWord_405405 prefixEnd_405405 123358592436202420606271 := by
  unfold tailWord_405405
  simp only [CollatzResearch.WordTrace]
  refine ⟨14786335096294397506817669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9857556730862931671211779 14786335096294397506817669)
  ·
    refine ⟨2772437830555199532528313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14786335096294397506817669 2772437830555199532528313)
    ·
      refine ⟨2079328372916399649396235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2772437830555199532528313 2079328372916399649396235)
      ·
        refine ⟨3118992559374599474094353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2079328372916399649396235 3118992559374599474094353)
        ·
          refine ⟨2339244419530949605570765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3118992559374599474094353 2339244419530949605570765)
          ·
            refine ⟨877216657324106102089037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2339244419530949605570765 877216657324106102089037)
            ·
              refine ⟨328956246496539788283389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 877216657324106102089037 328956246496539788283389)
              ·
                refine ⟨123358592436202420606271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328956246496539788283389 123358592436202420606271)
                ·
                  rfl

theorem cell19_405405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 3].length) (baseStart_405405 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405405 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405405 prefixEnd_405405 := by exact prefixLift 405405
  have htrace : WordTrace (prefixWord ++ tailWord_405405) baseStart_405405 baseEnd_405405 := by
    simpa [prefixWord, tailWord_405405, baseEnd_405405] using wordTrace_append hprefix tailTrace_405405
  have hstable : (prefixWord ++ tailWord_405405).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405405).length < 2 ^ (prefixWord ++ tailWord_405405).sum := by decide
  have hdescent : baseEnd_405405 < baseStart_405405 := by decide
  rcases family_descends (prefixWord ++ tailWord_405405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405447 : List Nat := [1, 1, 4, 1, 1, 2, 1, 8]
def baseStart_405447 : Nat := 118140960795 + 405447 * 2 ^ 59
def prefixEnd_405447 : Nat := 4983230072969 + 3 ^ 40 * 405447 * 2
def baseEnd_405447 : Nat := 123371372399158767672823

theorem tailTrace_405447 : CollatzResearch.WordTrace tailWord_405447 prefixEnd_405447 123371372399158767672823 := by
  unfold tailWord_405447
  simp only [CollatzResearch.WordTrace]
  refine ⟨14787866962142238679846595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9858577974761492453231063 14787866962142238679846595)
  ·
    refine ⟨22181800443213358019769893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14787866962142238679846595 22181800443213358019769893)
    ·
      refine ⟨4159087583102504628706855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22181800443213358019769893 4159087583102504628706855)
      ·
        refine ⟨6238631374653756943060283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4159087583102504628706855 6238631374653756943060283)
        ·
          refine ⟨9357947061980635414590425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6238631374653756943060283 9357947061980635414590425)
          ·
            refine ⟨7018460296485476560942819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9357947061980635414590425 7018460296485476560942819)
            ·
              refine ⟨10527690444728214841414229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7018460296485476560942819 10527690444728214841414229)
              ·
                refine ⟨123371372399158767672823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10527690444728214841414229 123371372399158767672823)
                ·
                  rfl

theorem cell19_405447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 8].length) (baseStart_405447 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405447 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405447 prefixEnd_405447 := by exact prefixLift 405447
  have htrace : WordTrace (prefixWord ++ tailWord_405447) baseStart_405447 baseEnd_405447 := by
    simpa [prefixWord, tailWord_405447, baseEnd_405447] using wordTrace_append hprefix tailTrace_405447
  have hstable : (prefixWord ++ tailWord_405447).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405447).length < 2 ^ (prefixWord ++ tailWord_405447).sum := by decide
  have hdescent : baseEnd_405447 < baseStart_405447 := by decide
  rcases family_descends (prefixWord ++ tailWord_405447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405458 : List Nat := [3, 2, 2, 3, 3, 1, 2, 3]
def baseStart_405458 : Nat := 118140960795 + 405458 * 2 ^ 59
def prefixEnd_405458 : Nat := 4983230072969 + 3 ^ 40 * 405458 * 2
def baseEnd_405458 : Nat := 123374719532314001428349

theorem tailTrace_405458 : CollatzResearch.WordTrace tailWord_405458 prefixEnd_405458 123374719532314001428349 := by
  unfold tailWord_405458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3697067041275596889624257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9858845443401591705664685 3697067041275596889624257)
  ·
    refine ⟨2772800280956697667218193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3697067041275596889624257 2772800280956697667218193)
    ·
      refine ⟨2079600210717523250413645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2772800280956697667218193 2079600210717523250413645)
      ·
        refine ⟨779850079019071218905117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2079600210717523250413645 779850079019071218905117)
        ·
          refine ⟨292443779632151707089419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 779850079019071218905117 292443779632151707089419)
          ·
            refine ⟨438665669448227560634129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292443779632151707089419 438665669448227560634129)
            ·
              refine ⟨328999252086170670475597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 438665669448227560634129 328999252086170670475597)
              ·
                refine ⟨123374719532314001428349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 328999252086170670475597 123374719532314001428349)
                ·
                  rfl

theorem cell19_405458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 3].length) (baseStart_405458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405458 prefixEnd_405458 := by exact prefixLift 405458
  have htrace : WordTrace (prefixWord ++ tailWord_405458) baseStart_405458 baseEnd_405458 := by
    simpa [prefixWord, tailWord_405458, baseEnd_405458] using wordTrace_append hprefix tailTrace_405458
  have hstable : (prefixWord ++ tailWord_405458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405458).length < 2 ^ (prefixWord ++ tailWord_405458).sum := by decide
  have hdescent : baseEnd_405458 < baseStart_405458 := by decide
  rcases family_descends (prefixWord ++ tailWord_405458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405523 : List Nat := [1, 1, 1, 2, 1, 4, 4, 5]
def baseStart_405523 : Nat := 118140960795 + 405523 * 2 ^ 59
def prefixEnd_405523 : Nat := 4983230072969 + 3 ^ 40 * 405523 * 2
def baseEnd_405523 : Nat := 123394498046413109983727

theorem tailTrace_405523 : CollatzResearch.WordTrace tailWord_405523 prefixEnd_405523 123394498046413109983727 := by
  unfold tailWord_405523
  simp only [CollatzResearch.WordTrace]
  refine ⟨14790638909866903659613223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9860425939911269106408815 14790638909866903659613223)
  ·
    refine ⟨22185958364800355489419835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14790638909866903659613223 22185958364800355489419835)
    ·
      refine ⟨33278937547200533234129753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22185958364800355489419835 33278937547200533234129753)
      ·
        refine ⟨24959203160400399925597315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33278937547200533234129753 24959203160400399925597315)
        ·
          refine ⟨37438804740600599888395973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24959203160400399925597315 37438804740600599888395973)
          ·
            refine ⟨7019775888862612479074245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37438804740600599888395973 7019775888862612479074245)
            ·
              refine ⟨1316207979161739839826421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7019775888862612479074245 1316207979161739839826421)
              ·
                refine ⟨123394498046413109983727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1316207979161739839826421 123394498046413109983727)
                ·
                  rfl

theorem cell19_405523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 5].length) (baseStart_405523 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405523 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405523 prefixEnd_405523 := by exact prefixLift 405523
  have htrace : WordTrace (prefixWord ++ tailWord_405523) baseStart_405523 baseEnd_405523 := by
    simpa [prefixWord, tailWord_405523, baseEnd_405523] using wordTrace_append hprefix tailTrace_405523
  have hstable : (prefixWord ++ tailWord_405523).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405523).length < 2 ^ (prefixWord ++ tailWord_405523).sum := by decide
  have hdescent : baseEnd_405523 < baseStart_405523 := by decide
  rcases family_descends (prefixWord ++ tailWord_405523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405540 : List Nat := [2, 3, 1, 4, 2, 7]
def baseStart_405540 : Nat := 118140960795 + 405540 * 2 ^ 59
def prefixEnd_405540 : Nat := 4983230072969 + 3 ^ 40 * 405540 * 2
def baseEnd_405540 : Nat := 13711074543173567511767

theorem tailTrace_405540 : CollatzResearch.WordTrace tailWord_405540 prefixEnd_405540 13711074543173567511767 := by
  unfold tailWord_405540
  simp only [CollatzResearch.WordTrace]
  refine ⟨7395629475402657781491037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9860839300536877041988049 7395629475402657781491037)
  ·
    refine ⟨2773361053275996668059139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7395629475402657781491037 2773361053275996668059139)
    ·
      refine ⟨4160041579913995002088709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2773361053275996668059139 4160041579913995002088709)
      ·
        refine ⟨780007796233874062891633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4160041579913995002088709 780007796233874062891633)
        ·
          refine ⟨585005847175405547168725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780007796233874062891633 585005847175405547168725)
          ·
            refine ⟨13711074543173567511767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 585005847175405547168725 13711074543173567511767)
            ·
              rfl

theorem cell19_405540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 7].length) (baseStart_405540 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405540 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405540 prefixEnd_405540 := by exact prefixLift 405540
  have htrace : WordTrace (prefixWord ++ tailWord_405540) baseStart_405540 baseEnd_405540 := by
    simpa [prefixWord, tailWord_405540, baseEnd_405540] using wordTrace_append hprefix tailTrace_405540
  have hstable : (prefixWord ++ tailWord_405540).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405540).length < 2 ^ (prefixWord ++ tailWord_405540).sum := by decide
  have hdescent : baseEnd_405540 < baseStart_405540 := by decide
  rcases family_descends (prefixWord ++ tailWord_405540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405574 : List Nat := [6, 1, 1, 1, 1, 1, 5, 3]
def baseStart_405574 : Nat := 118140960795 + 405574 * 2 ^ 59
def prefixEnd_405574 : Nat := 4983230072969 + 3 ^ 40 * 405574 * 2
def baseEnd_405574 : Nat := 123410016572860102850255

theorem tailTrace_405574 : CollatzResearch.WordTrace tailWord_405574 prefixEnd_405574 123410016572860102850255 := by
  unfold tailWord_405574
  simp only [CollatzResearch.WordTrace]
  refine ⟨462265594771316855303743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9861666021788092913146517 462265594771316855303743)
  ·
    refine ⟨693398392156975282955615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 462265594771316855303743 693398392156975282955615)
    ·
      refine ⟨1040097588235462924433423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 693398392156975282955615 1040097588235462924433423)
      ·
        refine ⟨1560146382353194386650135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1040097588235462924433423 1560146382353194386650135)
        ·
          refine ⟨2340219573529791579975203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1560146382353194386650135 2340219573529791579975203)
          ·
            refine ⟨3510329360294687369962805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2340219573529791579975203 3510329360294687369962805)
            ·
              refine ⟨329093377527626940934013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3510329360294687369962805 329093377527626940934013)
              ·
                refine ⟨123410016572860102850255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329093377527626940934013 123410016572860102850255)
                ·
                  rfl

theorem cell19_405574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_405574 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405574 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405574 prefixEnd_405574 := by exact prefixLift 405574
  have htrace : WordTrace (prefixWord ++ tailWord_405574) baseStart_405574 baseEnd_405574 := by
    simpa [prefixWord, tailWord_405574, baseEnd_405574] using wordTrace_append hprefix tailTrace_405574
  have hstable : (prefixWord ++ tailWord_405574).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405574).length < 2 ^ (prefixWord ++ tailWord_405574).sum := by decide
  have hdescent : baseEnd_405574 < baseStart_405574 := by decide
  rcases family_descends (prefixWord ++ tailWord_405574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405580 : List Nat := [2, 2, 1, 3, 1, 1, 2, 7]
def baseStart_405580 : Nat := 118140960795 + 405580 * 2 ^ 59
def prefixEnd_405580 : Nat := 4983230072969 + 3 ^ 40 * 405580 * 2
def baseEnd_405580 : Nat := 123411842281853866716905

theorem tailTrace_405580 : CollatzResearch.WordTrace tailWord_405580 prefixEnd_405580 123411842281853866716905 := by
  unfold tailWord_405580
  simp only [CollatzResearch.WordTrace]
  refine ⟨7396358935330201197219097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9861811913773601596292129 7396358935330201197219097)
  ·
    refine ⟨5547269201497650897914323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7396358935330201197219097 5547269201497650897914323)
    ·
      refine ⟨8320903802246476346871485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5547269201497650897914323 8320903802246476346871485)
      ·
        refine ⟨3120338925842428630076807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8320903802246476346871485 3120338925842428630076807)
        ·
          refine ⟨4680508388763642945115211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3120338925842428630076807 4680508388763642945115211)
          ·
            refine ⟨7020762583145464417672817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4680508388763642945115211 7020762583145464417672817)
            ·
              refine ⟨5265571937359098313254613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7020762583145464417672817 5265571937359098313254613)
              ·
                refine ⟨123411842281853866716905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5265571937359098313254613 123411842281853866716905)
                ·
                  rfl

theorem cell19_405580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_405580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405580 prefixEnd_405580 := by exact prefixLift 405580
  have htrace : WordTrace (prefixWord ++ tailWord_405580) baseStart_405580 baseEnd_405580 := by
    simpa [prefixWord, tailWord_405580, baseEnd_405580] using wordTrace_append hprefix tailTrace_405580
  have hstable : (prefixWord ++ tailWord_405580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405580).length < 2 ^ (prefixWord ++ tailWord_405580).sum := by decide
  have hdescent : baseEnd_405580 < baseStart_405580 := by decide
  rcases family_descends (prefixWord ++ tailWord_405580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405635 : List Nat := [1, 1, 1, 3, 3, 3, 4, 3]
def baseStart_405635 : Nat := 118140960795 + 405635 * 2 ^ 59
def prefixEnd_405635 : Nat := 4983230072969 + 3 ^ 40 * 405635 * 2
def baseEnd_405635 : Nat := 123428577947630035494533

theorem tailTrace_405635 : CollatzResearch.WordTrace tailWord_405635 prefixEnd_405635 123428577947630035494533 := by
  unfold tailWord_405635
  simp only [CollatzResearch.WordTrace]
  refine ⟨14794723885461146787690359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9863149256974097858460239 14794723885461146787690359)
  ·
    refine ⟨22192085828191720181535539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14794723885461146787690359 22192085828191720181535539)
    ·
      refine ⟨33288128742287580272303309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22192085828191720181535539 33288128742287580272303309)
      ·
        refine ⟨12483048278357842602113741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33288128742287580272303309 12483048278357842602113741)
        ·
          refine ⟨4681143104384190975792653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12483048278357842602113741 4681143104384190975792653)
          ·
            refine ⟨1755428664144071615922245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4681143104384190975792653 1755428664144071615922245)
            ·
              refine ⟨329142874527013427985421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1755428664144071615922245 329142874527013427985421)
              ·
                refine ⟨123428577947630035494533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329142874527013427985421 123428577947630035494533)
                ·
                  rfl

theorem cell19_405635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 3].length) (baseStart_405635 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405635 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405635 prefixEnd_405635 := by exact prefixLift 405635
  have htrace : WordTrace (prefixWord ++ tailWord_405635) baseStart_405635 baseEnd_405635 := by
    simpa [prefixWord, tailWord_405635, baseEnd_405635] using wordTrace_append hprefix tailTrace_405635
  have hstable : (prefixWord ++ tailWord_405635).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405635).length < 2 ^ (prefixWord ++ tailWord_405635).sum := by decide
  have hdescent : baseEnd_405635 < baseStart_405635 := by decide
  rcases family_descends (prefixWord ++ tailWord_405635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405671 : List Nat := [1, 1, 6, 2, 2, 1, 2, 4]
def baseStart_405671 : Nat := 118140960795 + 405671 * 2 ^ 59
def prefixEnd_405671 : Nat := 4983230072969 + 3 ^ 40 * 405671 * 2
def baseEnd_405671 : Nat := 123439532201592618694435

theorem tailTrace_405671 : CollatzResearch.WordTrace tailWord_405671 prefixEnd_405671 123439532201592618694435 := by
  unfold tailWord_405671
  simp only [CollatzResearch.WordTrace]
  refine ⟨14796036913330724936000867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9864024608887149957333911 14796036913330724936000867)
  ·
    refine ⟨22194055369996087404001301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14796036913330724936000867 22194055369996087404001301)
    ·
      refine ⟨1040346345468566597062561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22194055369996087404001301 1040346345468566597062561)
      ·
        refine ⟨780259759101424947796921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1040346345468566597062561 780259759101424947796921)
        ·
          refine ⟨585194819326068710847691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780259759101424947796921 585194819326068710847691)
          ·
            refine ⟨877792228989103066271537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 585194819326068710847691 877792228989103066271537)
            ·
              refine ⟨658344171741827299703653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 877792228989103066271537 658344171741827299703653)
              ·
                refine ⟨123439532201592618694435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 658344171741827299703653 123439532201592618694435)
                ·
                  rfl

theorem cell19_405671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 4].length) (baseStart_405671 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405671 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405671 prefixEnd_405671 := by exact prefixLift 405671
  have htrace : WordTrace (prefixWord ++ tailWord_405671) baseStart_405671 baseEnd_405671 := by
    simpa [prefixWord, tailWord_405671, baseEnd_405671] using wordTrace_append hprefix tailTrace_405671
  have hstable : (prefixWord ++ tailWord_405671).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405671).length < 2 ^ (prefixWord ++ tailWord_405671).sum := by decide
  have hdescent : baseEnd_405671 < baseStart_405671 := by decide
  rcases family_descends (prefixWord ++ tailWord_405671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405724 : List Nat := [2, 2, 5, 2, 2, 1, 1, 4]
def baseStart_405724 : Nat := 118140960795 + 405724 * 2 ^ 59
def prefixEnd_405724 : Nat := 4983230072969 + 3 ^ 40 * 405724 * 2
def baseEnd_405724 : Nat := 123455659297704199516513

theorem tailTrace_405724 : CollatzResearch.WordTrace tailWord_405724 prefixEnd_405724 123455659297704199516513 := by
  unfold tailWord_405724
  simp only [CollatzResearch.WordTrace]
  refine ⟨7398984991069357493840113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9865313321425809991786817 7398984991069357493840113)
  ·
    refine ⟨5549238743302018120380085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7398984991069357493840113 5549238743302018120380085)
    ·
      refine ⟨520241132184564198785633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5549238743302018120380085 520241132184564198785633)
      ·
        refine ⟨390180849138423149089225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 520241132184564198785633 390180849138423149089225)
        ·
          refine ⟨292635636853817361816919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 390180849138423149089225 292635636853817361816919)
          ·
            refine ⟨438953455280726042725379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 292635636853817361816919 438953455280726042725379)
            ·
              refine ⟨658430182921089064088069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 438953455280726042725379 658430182921089064088069)
              ·
                refine ⟨123455659297704199516513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 658430182921089064088069 123455659297704199516513)
                ·
                  rfl

theorem cell19_405724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_405724 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405724 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405724 prefixEnd_405724 := by exact prefixLift 405724
  have htrace : WordTrace (prefixWord ++ tailWord_405724) baseStart_405724 baseEnd_405724 := by
    simpa [prefixWord, tailWord_405724, baseEnd_405724] using wordTrace_append hprefix tailTrace_405724
  have hstable : (prefixWord ++ tailWord_405724).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405724).length < 2 ^ (prefixWord ++ tailWord_405724).sum := by decide
  have hdescent : baseEnd_405724 < baseStart_405724 := by decide
  rcases family_descends (prefixWord ++ tailWord_405724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405802 : List Nat := [3, 1, 4, 2, 2, 2, 2, 3]
def baseStart_405802 : Nat := 118140960795 + 405802 * 2 ^ 59
def prefixEnd_405802 : Nat := 4983230072969 + 3 ^ 40 * 405802 * 2
def baseEnd_405802 : Nat := 123479393514623129782967

theorem tailTrace_405802 : CollatzResearch.WordTrace tailWord_405802 prefixEnd_405802 123479393514623129782967 := by
  unfold tailWord_405802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3700203718964033577254915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9867209917237422872679773 3700203718964033577254915)
  ·
    refine ⟨5550305578446050365882373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3700203718964033577254915 5550305578446050365882373)
    ·
      refine ⟨1040682295958634443602945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5550305578446050365882373 1040682295958634443602945)
      ·
        refine ⟨780511721968975832702209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1040682295958634443602945 780511721968975832702209)
        ·
          refine ⟨585383791476731874526657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 780511721968975832702209 585383791476731874526657)
          ·
            refine ⟨439037843607548905894993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585383791476731874526657 439037843607548905894993)
            ·
              refine ⟨329278382705661679421245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439037843607548905894993 329278382705661679421245)
              ·
                refine ⟨123479393514623129782967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329278382705661679421245 123479393514623129782967)
                ·
                  rfl

theorem cell19_405802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 2, 3].length) (baseStart_405802 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405802 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405802 prefixEnd_405802 := by exact prefixLift 405802
  have htrace : WordTrace (prefixWord ++ tailWord_405802) baseStart_405802 baseEnd_405802 := by
    simpa [prefixWord, tailWord_405802, baseEnd_405802] using wordTrace_append hprefix tailTrace_405802
  have hstable : (prefixWord ++ tailWord_405802).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405802).length < 2 ^ (prefixWord ++ tailWord_405802).sum := by decide
  have hdescent : baseEnd_405802 < baseStart_405802 := by decide
  rcases family_descends (prefixWord ++ tailWord_405802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405844 : List Nat := [2, 4, 1, 1, 2, 3, 2, 4]
def baseStart_405844 : Nat := 118140960795 + 405844 * 2 ^ 59
def prefixEnd_405844 : Nat := 4983230072969 + 3 ^ 40 * 405844 * 2
def baseEnd_405844 : Nat := 123492173477579476849519

theorem tailTrace_405844 : CollatzResearch.WordTrace tailWord_405844 prefixEnd_405844 123492173477579476849519 := by
  unfold tailWord_405844
  simp only [CollatzResearch.WordTrace]
  refine ⟨7401173370851987741024293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9868231161135983654699057 7401173370851987741024293)
  ·
    refine ⟨1387720007034747701442055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7401173370851987741024293 1387720007034747701442055)
    ·
      refine ⟨2081580010552121552163083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1387720007034747701442055 2081580010552121552163083)
      ·
        refine ⟨3122370015828182328244625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2081580010552121552163083 3122370015828182328244625)
        ·
          refine ⟨2341777511871136746183469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3122370015828182328244625 2341777511871136746183469)
          ·
            refine ⟨878166566951676279818801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2341777511871136746183469 878166566951676279818801)
            ·
              refine ⟨658624925213757209864101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 878166566951676279818801 658624925213757209864101)
              ·
                refine ⟨123492173477579476849519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 658624925213757209864101 123492173477579476849519)
                ·
                  rfl

theorem cell19_405844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_405844 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405844 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405844 prefixEnd_405844 := by exact prefixLift 405844
  have htrace : WordTrace (prefixWord ++ tailWord_405844) baseStart_405844 baseEnd_405844 := by
    simpa [prefixWord, tailWord_405844, baseEnd_405844] using wordTrace_append hprefix tailTrace_405844
  have hstable : (prefixWord ++ tailWord_405844).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405844).length < 2 ^ (prefixWord ++ tailWord_405844).sum := by decide
  have hdescent : baseEnd_405844 < baseStart_405844 := by decide
  rcases family_descends (prefixWord ++ tailWord_405844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405920 : List Nat := [2, 1, 1, 4, 1, 4, 3, 3]
def baseStart_405920 : Nat := 118140960795 + 405920 * 2 ^ 59
def prefixEnd_405920 : Nat := 4983230072969 + 3 ^ 40 * 405920 * 2
def baseEnd_405920 : Nat := 123515299124833819160423

theorem tailTrace_405920 : CollatzResearch.WordTrace tailWord_405920 prefixEnd_405920 123515299124833819160423 := by
  unfold tailWord_405920
  simp only [CollatzResearch.WordTrace]
  refine ⟨7402559344714320230907607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9870079126285760307876809 7402559344714320230907607)
  ·
    refine ⟨11103839017071480346361411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7402559344714320230907607 11103839017071480346361411)
    ·
      refine ⟨16655758525607220519542117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11103839017071480346361411 16655758525607220519542117)
      ·
        refine ⟨3122954723551353847414147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16655758525607220519542117 3122954723551353847414147)
        ·
          refine ⟨4684432085327030771121221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3122954723551353847414147 4684432085327030771121221)
          ·
            refine ⟨878331015998818269585229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4684432085327030771121221 878331015998818269585229)
            ·
              refine ⟨329374130999556851094461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 878331015998818269585229 329374130999556851094461)
              ·
                refine ⟨123515299124833819160423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329374130999556851094461 123515299124833819160423)
                ·
                  rfl

theorem cell19_405920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 3, 3].length) (baseStart_405920 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405920 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405920 prefixEnd_405920 := by exact prefixLift 405920
  have htrace : WordTrace (prefixWord ++ tailWord_405920) baseStart_405920 baseEnd_405920 := by
    simpa [prefixWord, tailWord_405920, baseEnd_405920] using wordTrace_append hprefix tailTrace_405920
  have hstable : (prefixWord ++ tailWord_405920).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405920).length < 2 ^ (prefixWord ++ tailWord_405920).sum := by decide
  have hdescent : baseEnd_405920 < baseStart_405920 := by decide
  rcases family_descends (prefixWord ++ tailWord_405920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_405998 : List Nat := [4, 1, 2, 1, 2, 2, 7]
def baseStart_405998 : Nat := 118140960795 + 405998 * 2 ^ 59
def prefixEnd_405998 : Nat := 4983230072969 + 3 ^ 40 * 405998 * 2
def baseEnd_405998 : Nat := 41179677780584249808959

theorem tailTrace_405998 : CollatzResearch.WordTrace tailWord_405998 prefixEnd_405998 41179677780584249808959 := by
  unfold tailWord_405998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1850995447893257472894331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9871975722097373188769765 1850995447893257472894331)
  ·
    refine ⟨2776493171839886209341497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1850995447893257472894331 2776493171839886209341497)
    ·
      refine ⟨2082369878879914657006123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2776493171839886209341497 2082369878879914657006123)
      ·
        refine ⟨3123554818319871985509185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2082369878879914657006123 3123554818319871985509185)
        ·
          refine ⟨2342666113739903989131889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3123554818319871985509185 2342666113739903989131889)
          ·
            refine ⟨1756999585304927991848917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2342666113739903989131889 1756999585304927991848917)
            ·
              refine ⟨41179677780584249808959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1756999585304927991848917 41179677780584249808959)
              ·
                rfl

theorem cell19_405998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 7].length) (baseStart_405998 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_405998 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_405998 prefixEnd_405998 := by exact prefixLift 405998
  have htrace : WordTrace (prefixWord ++ tailWord_405998) baseStart_405998 baseEnd_405998 := by
    simpa [prefixWord, tailWord_405998, baseEnd_405998] using wordTrace_append hprefix tailTrace_405998
  have hstable : (prefixWord ++ tailWord_405998).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_405998).length < 2 ^ (prefixWord ++ tailWord_405998).sum := by decide
  have hdescent : baseEnd_405998 < baseStart_405998 := by decide
  rcases family_descends (prefixWord ++ tailWord_405998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406017 : List Nat := [1, 2, 4, 1, 3, 1, 1, 6]
def baseStart_406017 : Nat := 118140960795 + 406017 * 2 ^ 59
def prefixEnd_406017 : Nat := 4983230072969 + 3 ^ 40 * 406017 * 2
def baseEnd_406017 : Nat := 123544814753566335004603

theorem tailTrace_406017 : CollatzResearch.WordTrace tailWord_406017 prefixEnd_406017 123544814753566335004603 := by
  unfold tailWord_406017
  simp only [CollatzResearch.WordTrace]
  refine ⟨14808656570077226028096305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9872437713384817352064203 14808656570077226028096305)
  ·
    refine ⟨11106492427557919521072229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14808656570077226028096305 11106492427557919521072229)
    ·
      refine ⟨2082467330167109910201043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11106492427557919521072229 2082467330167109910201043)
      ·
        refine ⟨3123700995250664865301565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2082467330167109910201043 3123700995250664865301565)
        ·
          refine ⟨1171387873218999324488087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3123700995250664865301565 1171387873218999324488087)
          ·
            refine ⟨1757081809828498986732131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171387873218999324488087 1757081809828498986732131)
            ·
              refine ⟨2635622714742748480098197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1757081809828498986732131 2635622714742748480098197)
              ·
                refine ⟨123544814753566335004603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2635622714742748480098197 123544814753566335004603)
                ·
                  rfl

theorem cell19_406017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 6].length) (baseStart_406017 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406017 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406017 prefixEnd_406017 := by exact prefixLift 406017
  have htrace : WordTrace (prefixWord ++ tailWord_406017) baseStart_406017 baseEnd_406017 := by
    simpa [prefixWord, tailWord_406017, baseEnd_406017] using wordTrace_append hprefix tailTrace_406017
  have hstable : (prefixWord ++ tailWord_406017).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406017).length < 2 ^ (prefixWord ++ tailWord_406017).sum := by decide
  have hdescent : baseEnd_406017 < baseStart_406017 := by decide
  rcases family_descends (prefixWord ++ tailWord_406017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406068 : List Nat := [2, 5, 1, 3, 1, 2, 1, 4]
def baseStart_406068 : Nat := 118140960795 + 406068 * 2 ^ 59
def prefixEnd_406068 : Nat := 4983230072969 + 3 ^ 40 * 406068 * 2
def baseEnd_406068 : Nat := 123560333280013327871131

theorem tailTrace_406068 : CollatzResearch.WordTrace tailWord_406068 prefixEnd_406068 123560333280013327871131 := by
  unfold tailWord_406068
  simp only [CollatzResearch.WordTrace]
  refine ⟨7405258346446230869101429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9873677795261641158801905 7405258346446230869101429)
  ·
    refine ⟨694242969979334143978259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7405258346446230869101429 694242969979334143978259)
    ·
      refine ⟨1041364454969001215967389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 694242969979334143978259 1041364454969001215967389)
      ·
        refine ⟨390511670613375455987771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1041364454969001215967389 390511670613375455987771)
        ·
          refine ⟨585767505920063183981657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390511670613375455987771 585767505920063183981657)
          ·
            refine ⟨439325629440047387986243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 585767505920063183981657 439325629440047387986243)
            ·
              refine ⟨658988444160071081979365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439325629440047387986243 658988444160071081979365)
              ·
                refine ⟨123560333280013327871131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 658988444160071081979365 123560333280013327871131)
                ·
                  rfl

theorem cell19_406068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 2, 1, 4].length) (baseStart_406068 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406068 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406068 prefixEnd_406068 := by exact prefixLift 406068
  have htrace : WordTrace (prefixWord ++ tailWord_406068) baseStart_406068 baseEnd_406068 := by
    simpa [prefixWord, tailWord_406068, baseEnd_406068] using wordTrace_append hprefix tailTrace_406068
  have hstable : (prefixWord ++ tailWord_406068).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406068).length < 2 ^ (prefixWord ++ tailWord_406068).sum := by decide
  have hdescent : baseEnd_406068 < baseStart_406068 := by decide
  rcases family_descends (prefixWord ++ tailWord_406068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406070 : List Nat := [5, 1, 2, 1, 2, 3, 1, 4]
def baseStart_406070 : Nat := 118140960795 + 406070 * 2 ^ 59
def prefixEnd_406070 : Nat := 4983230072969 + 3 ^ 40 * 406070 * 2
def baseEnd_406070 : Nat := 123560941849677915826681

theorem tailTrace_406070 : CollatzResearch.WordTrace tailWord_406070 prefixEnd_406070 123560941849677915826681 := by
  unfold tailWord_406070
  simp only [CollatzResearch.WordTrace]
  refine ⟨925661852430326004985979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9873726425923477386517109 925661852430326004985979)
  ·
    refine ⟨1388492778645489007478969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 925661852430326004985979 1388492778645489007478969)
    ·
      refine ⟨1041369583984116755609227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1388492778645489007478969 1041369583984116755609227)
      ·
        refine ⟨1562054375976175133413841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1041369583984116755609227 1562054375976175133413841)
        ·
          refine ⟨1171540781982131350060381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1562054375976175133413841 1171540781982131350060381)
          ·
            refine ⟨439327793243299256272643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1171540781982131350060381 439327793243299256272643)
            ·
              refine ⟨658991689864948884408965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439327793243299256272643 658991689864948884408965)
              ·
                refine ⟨123560941849677915826681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 658991689864948884408965 123560941849677915826681)
                ·
                  rfl

theorem cell19_406070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_406070 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406070 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406070 prefixEnd_406070 := by exact prefixLift 406070
  have htrace : WordTrace (prefixWord ++ tailWord_406070) baseStart_406070 baseEnd_406070 := by
    simpa [prefixWord, tailWord_406070, baseEnd_406070] using wordTrace_append hprefix tailTrace_406070
  have hstable : (prefixWord ++ tailWord_406070).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406070).length < 2 ^ (prefixWord ++ tailWord_406070).sum := by decide
  have hdescent : baseEnd_406070 < baseStart_406070 := by decide
  rcases family_descends (prefixWord ++ tailWord_406070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406074 : List Nat := [3, 1, 1, 1, 3, 3, 3, 4]
def baseStart_406074 : Nat := 118140960795 + 406074 * 2 ^ 59
def prefixEnd_406074 : Nat := 4983230072969 + 3 ^ 40 * 406074 * 2
def baseEnd_406074 : Nat := 123562158989007091737781

theorem tailTrace_406074 : CollatzResearch.WordTrace tailWord_406074 prefixEnd_406074 123562158989007091737781 := by
  unfold tailWord_406074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3702683882717681190730319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9873823687247149841947517 3702683882717681190730319)
  ·
    refine ⟨5554025824076521786095479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3702683882717681190730319 5554025824076521786095479)
    ·
      refine ⟨8331038736114782679143219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5554025824076521786095479 8331038736114782679143219)
      ·
        refine ⟨12496558104172174018714829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8331038736114782679143219 12496558104172174018714829)
        ·
          refine ⟨4686209289064565257018061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12496558104172174018714829 4686209289064565257018061)
          ·
            refine ⟨1757328483399211971381773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4686209289064565257018061 1757328483399211971381773)
            ·
              refine ⟨658998181274704489268165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1757328483399211971381773 658998181274704489268165)
              ·
                refine ⟨123562158989007091737781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 658998181274704489268165 123562158989007091737781)
                ·
                  rfl

theorem cell19_406074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_406074 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406074 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406074 prefixEnd_406074 := by exact prefixLift 406074
  have htrace : WordTrace (prefixWord ++ tailWord_406074) baseStart_406074 baseEnd_406074 := by
    simpa [prefixWord, tailWord_406074, baseEnd_406074] using wordTrace_append hprefix tailTrace_406074
  have hstable : (prefixWord ++ tailWord_406074).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406074).length < 2 ^ (prefixWord ++ tailWord_406074).sum := by decide
  have hdescent : baseEnd_406074 < baseStart_406074 := by decide
  rcases family_descends (prefixWord ++ tailWord_406074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406095 : List Nat := [1, 1, 2, 1, 1, 2, 4, 7]
def baseStart_406095 : Nat := 118140960795 + 406095 * 2 ^ 59
def prefixEnd_406095 : Nat := 4983230072969 + 3 ^ 40 * 406095 * 2
def baseEnd_406095 : Nat := 123568548970485265271057

theorem tailTrace_406095 : CollatzResearch.WordTrace tailWord_406095 prefixEnd_406095 123568548970485265271057 := by
  unfold tailWord_406095
  simp only [CollatzResearch.WordTrace]
  refine ⟨14811501463794645349435739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9874334309196430232957159 14811501463794645349435739)
  ·
    refine ⟨22217252195691968024153609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14811501463794645349435739 22217252195691968024153609)
    ·
      refine ⟨16662939146768976018115207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22217252195691968024153609 16662939146768976018115207)
      ·
        refine ⟨24994408720153464027172811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16662939146768976018115207 24994408720153464027172811)
        ·
          refine ⟨37491613080230196040759217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24994408720153464027172811 37491613080230196040759217)
          ·
            refine ⟨28118709810172647030569413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37491613080230196040759217 28118709810172647030569413)
            ·
              refine ⟨5272258089407371318231765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28118709810172647030569413 5272258089407371318231765)
              ·
                refine ⟨123568548970485265271057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5272258089407371318231765 123568548970485265271057)
                ·
                  rfl

theorem cell19_406095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 7].length) (baseStart_406095 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406095 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406095 prefixEnd_406095 := by exact prefixLift 406095
  have htrace : WordTrace (prefixWord ++ tailWord_406095) baseStart_406095 baseEnd_406095 := by
    simpa [prefixWord, tailWord_406095, baseEnd_406095] using wordTrace_append hprefix tailTrace_406095
  have hstable : (prefixWord ++ tailWord_406095).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406095).length < 2 ^ (prefixWord ++ tailWord_406095).sum := by decide
  have hdescent : baseEnd_406095 < baseStart_406095 := by decide
  rcases family_descends (prefixWord ++ tailWord_406095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406148 : List Nat := [2, 3, 2, 1, 3, 1, 4, 3]
def baseStart_406148 : Nat := 118140960795 + 406148 * 2 ^ 59
def prefixEnd_406148 : Nat := 4983230072969 + 3 ^ 40 * 406148 * 2
def baseEnd_406148 : Nat := 123584676066596846093135

theorem tailTrace_406148 : CollatzResearch.WordTrace tailWord_406148 prefixEnd_406148 123584676066596846093135 := by
  unfold tailWord_406148
  simp only [CollatzResearch.WordTrace]
  refine ⟨7406717266301317700557549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9875623021735090267410065 7406717266301317700557549)
  ·
    refine ⟨2777518974862994137709081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7406717266301317700557549 2777518974862994137709081)
    ·
      refine ⟨2083139231147245603281811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2777518974862994137709081 2083139231147245603281811)
      ·
        refine ⟨3124708846720868404922717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2083139231147245603281811 3124708846720868404922717)
        ·
          refine ⟨1171765817520325651846019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3124708846720868404922717 1171765817520325651846019)
          ·
            refine ⟨1757648726280488477769029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1171765817520325651846019 1757648726280488477769029)
            ·
              refine ⟨329559136177591589581693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1757648726280488477769029 329559136177591589581693)
              ·
                refine ⟨123584676066596846093135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329559136177591589581693 123584676066596846093135)
                ·
                  rfl

theorem cell19_406148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 4, 3].length) (baseStart_406148 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406148 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406148 prefixEnd_406148 := by exact prefixLift 406148
  have htrace : WordTrace (prefixWord ++ tailWord_406148) baseStart_406148 baseEnd_406148 := by
    simpa [prefixWord, tailWord_406148, baseEnd_406148] using wordTrace_append hprefix tailTrace_406148
  have hstable : (prefixWord ++ tailWord_406148).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406148).length < 2 ^ (prefixWord ++ tailWord_406148).sum := by decide
  have hdescent : baseEnd_406148 < baseStart_406148 := by decide
  rcases family_descends (prefixWord ++ tailWord_406148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406226 : List Nat := [3, 2, 2, 2, 3, 7]
def baseStart_406226 : Nat := 118140960795 + 406226 * 2 ^ 59
def prefixEnd_406226 : Nat := 4983230072969 + 3 ^ 40 * 406226 * 2
def baseEnd_406226 : Nat := 13734267809279530706621

theorem tailTrace_406226 : CollatzResearch.WordTrace tailWord_406226 prefixEnd_406226 13734267809279530706621 := by
  unfold tailWord_406226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3704069856580013680613633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9877519617546703148303021 3704069856580013680613633)
  ·
    refine ⟨2778052392435010260460225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3704069856580013680613633 2778052392435010260460225)
    ·
      refine ⟨2083539294326257695345169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2778052392435010260460225 2083539294326257695345169)
      ·
        refine ⟨1562654470744693271508877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2083539294326257695345169 1562654470744693271508877)
        ·
          refine ⟨585995426529259976815829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1562654470744693271508877 585995426529259976815829)
          ·
            refine ⟨13734267809279530706621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 585995426529259976815829 13734267809279530706621)
            ·
              rfl

theorem cell19_406226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 7].length) (baseStart_406226 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406226 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406226 prefixEnd_406226 := by exact prefixLift 406226
  have htrace : WordTrace (prefixWord ++ tailWord_406226) baseStart_406226 baseEnd_406226 := by
    simpa [prefixWord, tailWord_406226, baseEnd_406226] using wordTrace_append hprefix tailTrace_406226
  have hstable : (prefixWord ++ tailWord_406226).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406226).length < 2 ^ (prefixWord ++ tailWord_406226).sum := by decide
  have hdescent : baseEnd_406226 < baseStart_406226 := by decide
  rcases family_descends (prefixWord ++ tailWord_406226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406243 : List Nat := [1, 1, 1, 7, 1, 3, 1, 4]
def baseStart_406243 : Nat := 118140960795 + 406243 * 2 ^ 59
def prefixEnd_406243 : Nat := 4983230072969 + 3 ^ 40 * 406243 * 2
def baseEnd_406243 : Nat := 123613583125664773981765

theorem tailTrace_406243 : CollatzResearch.WordTrace tailWord_406243 prefixEnd_406243 123613583125664773981765 := by
  unfold tailWord_406243
  simp only [CollatzResearch.WordTrace]
  refine ⟨14816899467258466625823383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9877932978172311083882255 14816899467258466625823383)
  ·
    refine ⟨22225349200887699938735075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14816899467258466625823383 22225349200887699938735075)
    ·
      refine ⟨33338023801331549908102613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22225349200887699938735075 33338023801331549908102613)
      ·
        refine ⟨781359932843708200971155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 33338023801331549908102613 781359932843708200971155)
        ·
          refine ⟨1172039899265562301456733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781359932843708200971155 1172039899265562301456733)
          ·
            refine ⟨439514962224585863046275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1172039899265562301456733 439514962224585863046275)
            ·
              refine ⟨659272443336878794569413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 439514962224585863046275 659272443336878794569413)
              ·
                refine ⟨123613583125664773981765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 659272443336878794569413 123613583125664773981765)
                ·
                  rfl

theorem cell19_406243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 4].length) (baseStart_406243 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406243 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406243 prefixEnd_406243 := by exact prefixLift 406243
  have htrace : WordTrace (prefixWord ++ tailWord_406243) baseStart_406243 baseEnd_406243 := by
    simpa [prefixWord, tailWord_406243, baseEnd_406243] using wordTrace_append hprefix tailTrace_406243
  have hstable : (prefixWord ++ tailWord_406243).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406243).length < 2 ^ (prefixWord ++ tailWord_406243).sum := by decide
  have hdescent : baseEnd_406243 < baseStart_406243 := by decide
  rcases family_descends (prefixWord ++ tailWord_406243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406245 : List Nat := [1, 3, 1, 4, 1, 2, 3, 4]
def baseStart_406245 : Nat := 118140960795 + 406245 * 2 ^ 59
def prefixEnd_406245 : Nat := 4983230072969 + 3 ^ 40 * 406245 * 2
def baseEnd_406245 : Nat := 123614191695329361937315

theorem tailTrace_406245 : CollatzResearch.WordTrace tailWord_406245 prefixEnd_406245 123614191695329361937315 := by
  unfold tailWord_406245
  simp only [CollatzResearch.WordTrace]
  refine ⟨14816972413251220967396189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9877981608834147311597459 14816972413251220967396189)
  ·
    refine ⟨5556364654969207862773571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14816972413251220967396189 5556364654969207862773571)
    ·
      refine ⟨8334546982453811794160357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5556364654969207862773571 8334546982453811794160357)
      ·
        refine ⟨1562727559210089711405067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8334546982453811794160357 1562727559210089711405067)
        ·
          refine ⟨2344091338815134567107601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1562727559210089711405067 2344091338815134567107601)
          ·
            refine ⟨1758068504111350925330701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2344091338815134567107601 1758068504111350925330701)
            ·
              refine ⟨659275689041756596999013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1758068504111350925330701 659275689041756596999013)
              ·
                refine ⟨123614191695329361937315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 659275689041756596999013 123614191695329361937315)
                ·
                  rfl

theorem cell19_406245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 4].length) (baseStart_406245 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406245 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406245 prefixEnd_406245 := by exact prefixLift 406245
  have htrace : WordTrace (prefixWord ++ tailWord_406245) baseStart_406245 baseEnd_406245 := by
    simpa [prefixWord, tailWord_406245, baseEnd_406245] using wordTrace_append hprefix tailTrace_406245
  have hstable : (prefixWord ++ tailWord_406245).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406245).length < 2 ^ (prefixWord ++ tailWord_406245).sum := by decide
  have hdescent : baseEnd_406245 < baseStart_406245 := by decide
  rcases family_descends (prefixWord ++ tailWord_406245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406262 : List Nat := [5, 1, 1, 1, 1, 2, 5, 3]
def baseStart_406262 : Nat := 118140960795 + 406262 * 2 ^ 59
def prefixEnd_406262 : Nat := 4983230072969 + 3 ^ 40 * 406262 * 2
def baseEnd_406262 : Nat := 123619364537478359559491

theorem tailTrace_406262 : CollatzResearch.WordTrace tailWord_406262 prefixEnd_406262 123619364537478359559491 := by
  unfold tailWord_406262
  simp only [CollatzResearch.WordTrace]
  refine ⟨926099528386852054422815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9878394969459755247176693 926099528386852054422815)
  ·
    refine ⟨1389149292580278081634223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 926099528386852054422815 1389149292580278081634223)
    ·
      refine ⟨2083723938870417122451335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1389149292580278081634223 2083723938870417122451335)
      ·
        refine ⟨3125585908305625683677003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2083723938870417122451335 3125585908305625683677003)
        ·
          refine ⟨4688378862458438525515505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3125585908305625683677003 4688378862458438525515505)
          ·
            refine ⟨3516284146843828894136629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4688378862458438525515505 3516284146843828894136629)
            ·
              refine ⟨329651638766608958825309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3516284146843828894136629 329651638766608958825309)
              ·
                refine ⟨123619364537478359559491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329651638766608958825309 123619364537478359559491)
                ·
                  rfl

theorem cell19_406262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_406262 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406262 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406262 prefixEnd_406262 := by exact prefixLift 406262
  have htrace : WordTrace (prefixWord ++ tailWord_406262) baseStart_406262 baseEnd_406262 := by
    simpa [prefixWord, tailWord_406262, baseEnd_406262] using wordTrace_append hprefix tailTrace_406262
  have hstable : (prefixWord ++ tailWord_406262).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406262).length < 2 ^ (prefixWord ++ tailWord_406262).sum := by decide
  have hdescent : baseEnd_406262 < baseStart_406262 := by decide
  rcases family_descends (prefixWord ++ tailWord_406262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406264 : List Nat := [2, 1, 2, 1, 1, 2, 7, 3]
def baseStart_406264 : Nat := 118140960795 + 406264 * 2 ^ 59
def prefixEnd_406264 : Nat := 4983230072969 + 3 ^ 40 * 406264 * 2
def baseEnd_406264 : Nat := 123619973107142947515041

theorem tailTrace_406264 : CollatzResearch.WordTrace tailWord_406264 prefixEnd_406264 123619973107142947515041 := by
  unfold tailWord_406264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7408832700091193606168923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9878443600121591474891897 7408832700091193606168923)
  ·
    refine ⟨11113249050136790409253385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7408832700091193606168923 11113249050136790409253385)
    ·
      refine ⟨8334936787602592806940039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11113249050136790409253385 8334936787602592806940039)
      ·
        refine ⟨12502405181403889210410059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8334936787602592806940039 12502405181403889210410059)
        ·
          refine ⟨18753607772105833815615089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12502405181403889210410059 18753607772105833815615089)
          ·
            refine ⟨14065205829079375361711317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18753607772105833815615089 14065205829079375361711317)
            ·
              refine ⟨329653261619047860040109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 14065205829079375361711317 329653261619047860040109)
              ·
                refine ⟨123619973107142947515041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329653261619047860040109 123619973107142947515041)
                ·
                  rfl

theorem cell19_406264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_406264 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406264 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406264 prefixEnd_406264 := by exact prefixLift 406264
  have htrace : WordTrace (prefixWord ++ tailWord_406264) baseStart_406264 baseEnd_406264 := by
    simpa [prefixWord, tailWord_406264, baseEnd_406264] using wordTrace_append hprefix tailTrace_406264
  have hstable : (prefixWord ++ tailWord_406264).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406264).length < 2 ^ (prefixWord ++ tailWord_406264).sum := by decide
  have hdescent : baseEnd_406264 < baseStart_406264 := by decide
  rcases family_descends (prefixWord ++ tailWord_406264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406266 : List Nat := [3, 1, 1, 1, 1, 3, 2, 7]
def baseStart_406266 : Nat := 118140960795 + 406266 * 2 ^ 59
def prefixEnd_406266 : Nat := 4983230072969 + 3 ^ 40 * 406266 * 2
def baseEnd_406266 : Nat := 123620581676807535470591

theorem tailTrace_406266 : CollatzResearch.WordTrace tailWord_406266 prefixEnd_406266 123620581676807535470591 := by
  unfold tailWord_406266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3704434586543785388477663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9878492230783427702607101 3704434586543785388477663)
  ·
    refine ⟨5556651879815678082716495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3704434586543785388477663 5556651879815678082716495)
    ·
      refine ⟨8334977819723517124074743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5556651879815678082716495 8334977819723517124074743)
      ·
        refine ⟨12502466729585275686112115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8334977819723517124074743 12502466729585275686112115)
        ·
          refine ⟨18753700094377913529168173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12502466729585275686112115 18753700094377913529168173)
          ·
            refine ⟨7032637535391717573438065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18753700094377913529168173 7032637535391717573438065)
            ·
              refine ⟨5274478151543788180078549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7032637535391717573438065 5274478151543788180078549)
              ·
                refine ⟨123620581676807535470591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5274478151543788180078549 123620581676807535470591)
                ·
                  rfl

theorem cell19_406266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_406266 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406266 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406266 prefixEnd_406266 := by exact prefixLift 406266
  have htrace : WordTrace (prefixWord ++ tailWord_406266) baseStart_406266 baseEnd_406266 := by
    simpa [prefixWord, tailWord_406266, baseEnd_406266] using wordTrace_append hprefix tailTrace_406266
  have hstable : (prefixWord ++ tailWord_406266).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406266).length < 2 ^ (prefixWord ++ tailWord_406266).sum := by decide
  have hdescent : baseEnd_406266 < baseStart_406266 := by decide
  rcases family_descends (prefixWord ++ tailWord_406266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406317 : List Nat := [1, 5, 3, 2, 1, 1, 1, 5]
def baseStart_406317 : Nat := 118140960795 + 406317 * 2 ^ 59
def prefixEnd_406317 : Nat := 4983230072969 + 3 ^ 40 * 406317 * 2
def baseEnd_406317 : Nat := 123636100203254528337119

theorem tailTrace_406317 : CollatzResearch.WordTrace tailWord_406317 prefixEnd_406317 123636100203254528337119 := by
  unfold tailWord_406317
  simp only [CollatzResearch.WordTrace]
  refine ⟨14819598468990377264017205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9879732312660251509344803 14819598468990377264017205)
  ·
    refine ⟨1389337356467847868501613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14819598468990377264017205 1389337356467847868501613)
    ·
      refine ⟨521001508675442950688105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1389337356467847868501613 521001508675442950688105)
      ·
        refine ⟨390751131506582213016079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521001508675442950688105 390751131506582213016079)
        ·
          refine ⟨586126697259873319524119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 390751131506582213016079 586126697259873319524119)
          ·
            refine ⟨879190045889809979286179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 586126697259873319524119 879190045889809979286179)
            ·
              refine ⟨1318785068834714968929269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879190045889809979286179 1318785068834714968929269)
              ·
                refine ⟨123636100203254528337119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1318785068834714968929269 123636100203254528337119)
                ·
                  rfl

theorem cell19_406317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 5].length) (baseStart_406317 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406317 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406317 prefixEnd_406317 := by exact prefixLift 406317
  have htrace : WordTrace (prefixWord ++ tailWord_406317) baseStart_406317 baseEnd_406317 := by
    simpa [prefixWord, tailWord_406317, baseEnd_406317] using wordTrace_append hprefix tailTrace_406317
  have hstable : (prefixWord ++ tailWord_406317).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406317).length < 2 ^ (prefixWord ++ tailWord_406317).sum := by decide
  have hdescent : baseEnd_406317 < baseStart_406317 := by decide
  rcases family_descends (prefixWord ++ tailWord_406317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406359 : List Nat := [1, 1, 3, 2, 4, 2, 2, 4]
def baseStart_406359 : Nat := 118140960795 + 406359 * 2 ^ 59
def prefixEnd_406359 : Nat := 4983230072969 + 3 ^ 40 * 406359 * 2
def baseEnd_406359 : Nat := 123648880166210875403671

theorem tailTrace_406359 : CollatzResearch.WordTrace tailWord_406359 prefixEnd_406359 123648880166210875403671 := by
  unfold tailWord_406359
  simp only [CollatzResearch.WordTrace]
  refine ⟨14821130334838218437046131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9880753556558812291364087 14821130334838218437046131)
  ·
    refine ⟨22231695502257327655569197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14821130334838218437046131 22231695502257327655569197)
    ·
      refine ⟨8336885813346497870838449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22231695502257327655569197 8336885813346497870838449)
      ·
        refine ⟨6252664360009873403128837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8336885813346497870838449 6252664360009873403128837)
        ·
          refine ⟨1172374567501851263086657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6252664360009873403128837 1172374567501851263086657)
          ·
            refine ⟨879280925626388447314993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1172374567501851263086657 879280925626388447314993)
            ·
              refine ⟨659460694219791335486245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 879280925626388447314993 659460694219791335486245)
              ·
                refine ⟨123648880166210875403671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 659460694219791335486245 123648880166210875403671)
                ·
                  rfl

theorem cell19_406359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_406359 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406359 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406359 prefixEnd_406359 := by exact prefixLift 406359
  have htrace : WordTrace (prefixWord ++ tailWord_406359) baseStart_406359 baseEnd_406359 := by
    simpa [prefixWord, tailWord_406359, baseEnd_406359] using wordTrace_append hprefix tailTrace_406359
  have hstable : (prefixWord ++ tailWord_406359).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406359).length < 2 ^ (prefixWord ++ tailWord_406359).sum := by decide
  have hdescent : baseEnd_406359 < baseStart_406359 := by decide
  rcases family_descends (prefixWord ++ tailWord_406359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406361 : List Nat := [1, 2, 1, 2, 2, 4, 1, 6]
def baseStart_406361 : Nat := 118140960795 + 406361 * 2 ^ 59
def prefixEnd_406361 : Nat := 4983230072969 + 3 ^ 40 * 406361 * 2
def baseEnd_406361 : Nat := 123649488735875463359221

theorem tailTrace_406361 : CollatzResearch.WordTrace tailWord_406361 prefixEnd_406361 123649488735875463359221 := by
  unfold tailWord_406361
  simp only [CollatzResearch.WordTrace]
  refine ⟨14821203280830972778618937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9880802187220648519079291 14821203280830972778618937)
  ·
    refine ⟨11115902460623229583964203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14821203280830972778618937 11115902460623229583964203)
    ·
      refine ⟨16673853690934844375946305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11115902460623229583964203 16673853690934844375946305)
      ·
        refine ⟨12505390268201133281959729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16673853690934844375946305 12505390268201133281959729)
        ·
          refine ⟨9379042701150849961469797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12505390268201133281959729 9379042701150849961469797)
          ·
            refine ⟨1758570506465784367775587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9379042701150849961469797 1758570506465784367775587)
            ·
              refine ⟨2637855759698676551663381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1758570506465784367775587 2637855759698676551663381)
              ·
                refine ⟨123649488735875463359221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2637855759698676551663381 123649488735875463359221)
                ·
                  rfl

theorem cell19_406361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_406361 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406361 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406361 prefixEnd_406361 := by exact prefixLift 406361
  have htrace : WordTrace (prefixWord ++ tailWord_406361) baseStart_406361 baseEnd_406361 := by
    simpa [prefixWord, tailWord_406361, baseEnd_406361] using wordTrace_append hprefix tailTrace_406361
  have hstable : (prefixWord ++ tailWord_406361).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406361).length < 2 ^ (prefixWord ++ tailWord_406361).sum := by decide
  have hdescent : baseEnd_406361 < baseStart_406361 := by decide
  rcases family_descends (prefixWord ++ tailWord_406361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406380 : List Nat := [2, 2, 1, 1, 4, 1, 1, 7]
def baseStart_406380 : Nat := 118140960795 + 406380 * 2 ^ 59
def prefixEnd_406380 : Nat := 4983230072969 + 3 ^ 40 * 406380 * 2
def baseEnd_406380 : Nat := 123655270147689048936947

theorem tailTrace_406380 : CollatzResearch.WordTrace tailWord_406380 prefixEnd_406380 123655270147689048936947 := by
  unfold tailWord_406380
  simp only [CollatzResearch.WordTrace]
  refine ⟨7410948133881069511780297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9881264178508092682373729 7410948133881069511780297)
  ·
    refine ⟨5558211100410802133835223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7410948133881069511780297 5558211100410802133835223)
    ·
      refine ⟨8337316650616203200752835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5558211100410802133835223 8337316650616203200752835)
      ·
        refine ⟨12505974975924304801129253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8337316650616203200752835 12505974975924304801129253)
        ·
          refine ⟨2344870307985807150211735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12505974975924304801129253 2344870307985807150211735)
          ·
            refine ⟨3517305461978710725317603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2344870307985807150211735 3517305461978710725317603)
            ·
              refine ⟨5275958192968066087976405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3517305461978710725317603 5275958192968066087976405)
              ·
                refine ⟨123655270147689048936947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5275958192968066087976405 123655270147689048936947)
                ·
                  rfl

theorem cell19_406380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_406380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406380 prefixEnd_406380 := by exact prefixLift 406380
  have htrace : WordTrace (prefixWord ++ tailWord_406380) baseStart_406380 baseEnd_406380 := by
    simpa [prefixWord, tailWord_406380, baseEnd_406380] using wordTrace_append hprefix tailTrace_406380
  have hstable : (prefixWord ++ tailWord_406380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406380).length < 2 ^ (prefixWord ++ tailWord_406380).sum := by decide
  have hdescent : baseEnd_406380 < baseStart_406380 := by decide
  rcases family_descends (prefixWord ++ tailWord_406380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406433 : List Nat := [1, 2, 3, 4, 1, 2, 3, 3]
def baseStart_406433 : Nat := 118140960795 + 406433 * 2 ^ 59
def prefixEnd_406433 : Nat := 4983230072969 + 3 ^ 40 * 406433 * 2
def baseEnd_406433 : Nat := 123671397243800629759025

theorem tailTrace_406433 : CollatzResearch.WordTrace tailWord_406433 prefixEnd_406433 123671397243800629759025 := by
  unfold tailWord_406433
  simp only [CollatzResearch.WordTrace]
  refine ⟨14823829336570129075239953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9882552891046752716826635 14823829336570129075239953)
  ·
    refine ⟨11117872002427596806429965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14823829336570129075239953 11117872002427596806429965)
    ·
      refine ⟨4169202000910348802411237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11117872002427596806429965 4169202000910348802411237)
      ·
        refine ⟨781725375170690400452107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4169202000910348802411237 781725375170690400452107)
        ·
          refine ⟨1172588062756035600678161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781725375170690400452107 1172588062756035600678161)
          ·
            refine ⟨879441047067026700508621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1172588062756035600678161 879441047067026700508621)
            ·
              refine ⟨329790392650135012690733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 879441047067026700508621 329790392650135012690733)
              ·
                refine ⟨123671397243800629759025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329790392650135012690733 123671397243800629759025)
                ·
                  rfl

theorem cell19_406433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 3, 3].length) (baseStart_406433 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406433 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406433 prefixEnd_406433 := by exact prefixLift 406433
  have htrace : WordTrace (prefixWord ++ tailWord_406433) baseStart_406433 baseEnd_406433 := by
    simpa [prefixWord, tailWord_406433, baseEnd_406433] using wordTrace_append hprefix tailTrace_406433
  have hstable : (prefixWord ++ tailWord_406433).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406433).length < 2 ^ (prefixWord ++ tailWord_406433).sum := by decide
  have hdescent : baseEnd_406433 < baseStart_406433 := by decide
  rcases family_descends (prefixWord ++ tailWord_406433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406452 : List Nat := [2, 5, 2, 1, 1, 2, 6]
def baseStart_406452 : Nat := 118140960795 + 406452 * 2 ^ 59
def prefixEnd_406452 : Nat := 4983230072969 + 3 ^ 40 * 406452 * 2
def baseEnd_406452 : Nat := 41225726218538071778917

theorem tailTrace_406452 : CollatzResearch.WordTrace tailWord_406452 prefixEnd_406452 41225726218538071778917 := by
  unfold tailWord_406452
  simp only [CollatzResearch.WordTrace]
  refine ⟨7412261161750647660090805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9883014882334196880121073 7412261161750647660090805)
  ·
    refine ⟨694899483914123218133513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7412261161750647660090805 694899483914123218133513)
    ·
      refine ⟨521174612935592413600135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 694899483914123218133513 521174612935592413600135)
      ·
        refine ⟨781761919403388620400203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 521174612935592413600135 781761919403388620400203)
        ·
          refine ⟨1172642879105082930600305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 781761919403388620400203 1172642879105082930600305)
          ·
            refine ⟨879482159328812197950229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1172642879105082930600305 879482159328812197950229)
            ·
              refine ⟨41225726218538071778917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 879482159328812197950229 41225726218538071778917)
              ·
                rfl

theorem cell19_406452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 6].length) (baseStart_406452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406452 prefixEnd_406452 := by exact prefixLift 406452
  have htrace : WordTrace (prefixWord ++ tailWord_406452) baseStart_406452 baseEnd_406452 := by
    simpa [prefixWord, tailWord_406452, baseEnd_406452] using wordTrace_append hprefix tailTrace_406452
  have hstable : (prefixWord ++ tailWord_406452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406452).length < 2 ^ (prefixWord ++ tailWord_406452).sum := by decide
  have hdescent : baseEnd_406452 < baseStart_406452 := by decide
  rcases family_descends (prefixWord ++ tailWord_406452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406456 : List Nat := [2, 1, 2, 1, 2, 5, 6]
def baseStart_406456 : Nat := 118140960795 + 406456 * 2 ^ 59
def prefixEnd_406456 : Nat := 4983230072969 + 3 ^ 40 * 406456 * 2
def baseEnd_406456 : Nat := 41226131931647797082617

theorem tailTrace_406456 : CollatzResearch.WordTrace tailWord_406456 prefixEnd_406456 41226131931647797082617 := by
  unfold tailWord_406456
  simp only [CollatzResearch.WordTrace]
  refine ⟨7412334107743402001663611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9883112143657869335551481 7412334107743402001663611)
  ·
    refine ⟨11118501161615103002495417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7412334107743402001663611 11118501161615103002495417)
    ·
      refine ⟨8338875871211327251871563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11118501161615103002495417 8338875871211327251871563)
      ·
        refine ⟨12508313806816990877807345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8338875871211327251871563 12508313806816990877807345)
        ·
          refine ⟨9381235355112743158355509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12508313806816990877807345 9381235355112743158355509)
          ·
            refine ⟨879490814541819671095829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9381235355112743158355509 879490814541819671095829)
            ·
              refine ⟨41226131931647797082617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 879490814541819671095829 41226131931647797082617)
              ·
                rfl

theorem cell19_406456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 6].length) (baseStart_406456 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406456 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406456 prefixEnd_406456 := by exact prefixLift 406456
  have htrace : WordTrace (prefixWord ++ tailWord_406456) baseStart_406456 baseEnd_406456 := by
    simpa [prefixWord, tailWord_406456, baseEnd_406456] using wordTrace_append hprefix tailTrace_406456
  have hstable : (prefixWord ++ tailWord_406456).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406456).length < 2 ^ (prefixWord ++ tailWord_406456).sum := by decide
  have hdescent : baseEnd_406456 < baseStart_406456 := by decide
  rcases family_descends (prefixWord ++ tailWord_406456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406490 : List Nat := [3, 1, 1, 2, 4, 3, 2, 3]
def baseStart_406490 : Nat := 118140960795 + 406490 * 2 ^ 59
def prefixEnd_406490 : Nat := 4983230072969 + 3 ^ 40 * 406490 * 2
def baseEnd_406490 : Nat := 123688741479241386492203

theorem tailTrace_406490 : CollatzResearch.WordTrace tailWord_406490 prefixEnd_406490 123688741479241386492203 := by
  unfold tailWord_406490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3706477074340906952516231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9883938864909085206709949 3706477074340906952516231)
  ·
    refine ⟨5559715611511360428774347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3706477074340906952516231 5559715611511360428774347)
    ·
      refine ⟨8339573417267040643161521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5559715611511360428774347 8339573417267040643161521)
      ·
        refine ⟨6254680062950280482371141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8339573417267040643161521 6254680062950280482371141)
        ·
          refine ⟨1172752511803177590444589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6254680062950280482371141 1172752511803177590444589)
          ·
            refine ⟨439782191926191596416721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1172752511803177590444589 439782191926191596416721)
            ·
              refine ⟨329836643944643697312541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439782191926191596416721 329836643944643697312541)
              ·
                refine ⟨123688741479241386492203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329836643944643697312541 123688741479241386492203)
                ·
                  rfl

theorem cell19_406490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 3].length) (baseStart_406490 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406490 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406490 prefixEnd_406490 := by exact prefixLift 406490
  have htrace : WordTrace (prefixWord ++ tailWord_406490) baseStart_406490 baseEnd_406490 := by
    simpa [prefixWord, tailWord_406490, baseEnd_406490] using wordTrace_append hprefix tailTrace_406490
  have hstable : (prefixWord ++ tailWord_406490).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406490).length < 2 ^ (prefixWord ++ tailWord_406490).sum := by decide
  have hdescent : baseEnd_406490 < baseStart_406490 := by decide
  rcases family_descends (prefixWord ++ tailWord_406490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406513 : List Nat := [1, 2, 2, 2, 4, 1, 7]
def baseStart_406513 : Nat := 118140960795 + 406513 * 2 ^ 59
def prefixEnd_406513 : Nat := 4983230072969 + 3 ^ 40 * 406513 * 2
def baseEnd_406513 : Nat := 41231913343461382660343

theorem tailTrace_406513 : CollatzResearch.WordTrace tailWord_406513 prefixEnd_406513 41231913343461382660343 := by
  unfold tailWord_406513
  simp only [CollatzResearch.WordTrace]
  refine ⟨14826747176280302738152193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9884498117520201825434795 14826747176280302738152193)
  ·
    refine ⟨11120060382210227053614145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14826747176280302738152193 11120060382210227053614145)
    ·
      refine ⟨8340045286657670290210609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11120060382210227053614145 8340045286657670290210609)
      ·
        refine ⟨6255033964993252717657957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8340045286657670290210609 6255033964993252717657957)
        ·
          refine ⟨1172818868436234884560867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6255033964993252717657957 1172818868436234884560867)
          ·
            refine ⟨1759228302654352326841301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1172818868436234884560867 1759228302654352326841301)
            ·
              refine ⟨41231913343461382660343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1759228302654352326841301 41231913343461382660343)
              ·
                rfl

theorem cell19_406513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 7].length) (baseStart_406513 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406513 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406513 prefixEnd_406513 := by exact prefixLift 406513
  have htrace : WordTrace (prefixWord ++ tailWord_406513) baseStart_406513 baseEnd_406513 := by
    simpa [prefixWord, tailWord_406513, baseEnd_406513] using wordTrace_append hprefix tailTrace_406513
  have hstable : (prefixWord ++ tailWord_406513).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406513).length < 2 ^ (prefixWord ++ tailWord_406513).sum := by decide
  have hdescent : baseEnd_406513 < baseStart_406513 := by decide
  rcases family_descends (prefixWord ++ tailWord_406513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406570 : List Nat := [3, 1, 4, 1, 10]
def baseStart_406570 : Nat := 118140960795 + 406570 * 2 ^ 59
def prefixEnd_406570 : Nat := 4983230072969 + 3 ^ 40 * 406570 * 2
def baseEnd_406570 : Nat := 4581966083919440915341

theorem tailTrace_406570 : CollatzResearch.WordTrace tailWord_406570 prefixEnd_406570 4581966083919440915341 := by
  unfold tailWord_406570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3707206534268450368244291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9885884091382534315318109 3707206534268450368244291)
  ·
    refine ⟨5560809801402675552366437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3707206534268450368244291 5560809801402675552366437)
    ·
      refine ⟨1042651837763001666068707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5560809801402675552366437 1042651837763001666068707)
      ·
        refine ⟨1563977756644502499103061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1042651837763001666068707 1563977756644502499103061)
        ·
          refine ⟨4581966083919440915341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1563977756644502499103061 4581966083919440915341)
          ·
            rfl

theorem cell19_406570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 10].length) (baseStart_406570 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406570 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406570 prefixEnd_406570 := by exact prefixLift 406570
  have htrace : WordTrace (prefixWord ++ tailWord_406570) baseStart_406570 baseEnd_406570 := by
    simpa [prefixWord, tailWord_406570, baseEnd_406570] using wordTrace_append hprefix tailTrace_406570
  have hstable : (prefixWord ++ tailWord_406570).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406570).length < 2 ^ (prefixWord ++ tailWord_406570).sum := by decide
  have hdescent : baseEnd_406570 < baseStart_406570 := by decide
  rcases family_descends (prefixWord ++ tailWord_406570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406606 : List Nat := [4, 1, 1, 1, 1, 3, 5, 3]
def baseStart_406606 : Nat := 118140960795 + 406606 * 2 ^ 59
def prefixEnd_406606 : Nat := 4983230072969 + 3 ^ 40 * 406606 * 2
def baseEnd_406606 : Nat := 123724038519787487914109

theorem tailTrace_406606 : CollatzResearch.WordTrace tailWord_406606 prefixEnd_406606 123724038519787487914109 := by
  unfold tailWord_406606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1853767395617922452660959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9886759443295586414191781 1853767395617922452660959)
  ·
    refine ⟨2780651093426883678991439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1853767395617922452660959 2780651093426883678991439)
    ·
      refine ⟨4170976640140325518487159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2780651093426883678991439 4170976640140325518487159)
      ·
        refine ⟨6256464960210488277730739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4170976640140325518487159 6256464960210488277730739)
        ·
          refine ⟨9384697440315732416596109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6256464960210488277730739 9384697440315732416596109)
          ·
            refine ⟨3519261540118399656223541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9384697440315732416596109 3519261540118399656223541)
            ·
              refine ⟨329930769386099967770957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3519261540118399656223541 329930769386099967770957)
              ·
                refine ⟨123724038519787487914109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329930769386099967770957 123724038519787487914109)
                ·
                  rfl

theorem cell19_406606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_406606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406606 prefixEnd_406606 := by exact prefixLift 406606
  have htrace : WordTrace (prefixWord ++ tailWord_406606) baseStart_406606 baseEnd_406606 := by
    simpa [prefixWord, tailWord_406606, baseEnd_406606] using wordTrace_append hprefix tailTrace_406606
  have hstable : (prefixWord ++ tailWord_406606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406606).length < 2 ^ (prefixWord ++ tailWord_406606).sum := by decide
  have hdescent : baseEnd_406606 < baseStart_406606 := by decide
  rcases family_descends (prefixWord ++ tailWord_406606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406661 : List Nat := [1, 3, 1, 1, 6, 2, 2, 3]
def baseStart_406661 : Nat := 118140960795 + 406661 * 2 ^ 59
def prefixEnd_406661 : Nat := 4983230072969 + 3 ^ 40 * 406661 * 2
def baseEnd_406661 : Nat := 123740774185563656691737

theorem tailTrace_406661 : CollatzResearch.WordTrace tailWord_406661 prefixEnd_406661 123740774185563656691737 := by
  unfold tailWord_406661
  simp only [CollatzResearch.WordTrace]
  refine ⟨14832145179744124014539837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9888096786496082676359891 14832145179744124014539837)
  ·
    refine ⟨5562054442404046505452439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14832145179744124014539837 5562054442404046505452439)
    ·
      refine ⟨8343081663606069758178659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5562054442404046505452439 8343081663606069758178659)
      ·
        refine ⟨12514622495409104637267989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8343081663606069758178659 12514622495409104637267989)
        ·
          refine ⟨586622929472301779871937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12514622495409104637267989 586622929472301779871937)
          ·
            refine ⟨439967197104226334903953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 586622929472301779871937 439967197104226334903953)
            ·
              refine ⟨329975397828169751177965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 439967197104226334903953 329975397828169751177965)
              ·
                refine ⟨123740774185563656691737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 329975397828169751177965 123740774185563656691737)
                ·
                  rfl

theorem cell19_406661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 2, 2, 3].length) (baseStart_406661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406661 prefixEnd_406661 := by exact prefixLift 406661
  have htrace : WordTrace (prefixWord ++ tailWord_406661) baseStart_406661 baseEnd_406661 := by
    simpa [prefixWord, tailWord_406661, baseEnd_406661] using wordTrace_append hprefix tailTrace_406661
  have hstable : (prefixWord ++ tailWord_406661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406661).length < 2 ^ (prefixWord ++ tailWord_406661).sum := by decide
  have hdescent : baseEnd_406661 < baseStart_406661 := by decide
  rcases family_descends (prefixWord ++ tailWord_406661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406665 : List Nat := [1, 2, 1, 1, 4, 4, 1, 5]
def baseStart_406665 : Nat := 118140960795 + 406665 * 2 ^ 59
def prefixEnd_406665 : Nat := 4983230072969 + 3 ^ 40 * 406665 * 2
def baseEnd_406665 : Nat := 123741991324892832602837

theorem tailTrace_406665 : CollatzResearch.WordTrace tailWord_406665 prefixEnd_406665 123741991324892832602837 := by
  unfold tailWord_406665
  simp only [CollatzResearch.WordTrace]
  refine ⟨14832291071729632697685449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9888194047819755131790299 14832291071729632697685449)
  ·
    refine ⟨11124218303797224523264087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14832291071729632697685449 11124218303797224523264087)
    ·
      refine ⟨16686327455695836784896131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11124218303797224523264087 16686327455695836784896131)
      ·
        refine ⟨25029491183543755177344197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16686327455695836784896131 25029491183543755177344197)
        ·
          refine ⟨4693029596914454095752037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25029491183543755177344197 4693029596914454095752037)
          ·
            refine ⟨879943049421460142953507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4693029596914454095752037 879943049421460142953507)
            ·
              refine ⟨1319914574132190214430261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 879943049421460142953507 1319914574132190214430261)
              ·
                refine ⟨123741991324892832602837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1319914574132190214430261 123741991324892832602837)
                ·
                  rfl

theorem cell19_406665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_406665 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406665 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406665 prefixEnd_406665 := by exact prefixLift 406665
  have htrace : WordTrace (prefixWord ++ tailWord_406665) baseStart_406665 baseEnd_406665 := by
    simpa [prefixWord, tailWord_406665, baseEnd_406665] using wordTrace_append hprefix tailTrace_406665
  have hstable : (prefixWord ++ tailWord_406665).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406665).length < 2 ^ (prefixWord ++ tailWord_406665).sum := by decide
  have hdescent : baseEnd_406665 < baseStart_406665 := by decide
  rcases family_descends (prefixWord ++ tailWord_406665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406682 : List Nat := [3, 1, 1, 5, 1, 3, 5]
def baseStart_406682 : Nat := 118140960795 + 406682 * 2 ^ 59
def prefixEnd_406682 : Nat := 4983230072969 + 3 ^ 40 * 406682 * 2
def baseEnd_406682 : Nat := 41249054722347276741671

theorem tailTrace_406682 : CollatzResearch.WordTrace tailWord_406682 prefixEnd_406682 41249054722347276741671 := by
  unfold tailWord_406682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3708227778167011150263575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9888607408445363067369533 3708227778167011150263575)
  ·
    refine ⟨5562341667250516725395363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3708227778167011150263575 5562341667250516725395363)
    ·
      refine ⟨8343512500875775088093045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5562341667250516725395363 8343512500875775088093045)
      ·
        refine ⟨782204296957103914508723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8343512500875775088093045 782204296957103914508723)
        ·
          refine ⟨1173306445435655871763085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782204296957103914508723 1173306445435655871763085)
          ·
            refine ⟨439989917038370951911157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1173306445435655871763085 439989917038370951911157)
            ·
              refine ⟨41249054722347276741671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 439989917038370951911157 41249054722347276741671)
              ·
                rfl

theorem cell19_406682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 3, 5].length) (baseStart_406682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406682 prefixEnd_406682 := by exact prefixLift 406682
  have htrace : WordTrace (prefixWord ++ tailWord_406682) baseStart_406682 baseEnd_406682 := by
    simpa [prefixWord, tailWord_406682, baseEnd_406682] using wordTrace_append hprefix tailTrace_406682
  have hstable : (prefixWord ++ tailWord_406682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406682).length < 2 ^ (prefixWord ++ tailWord_406682).sum := by decide
  have hdescent : baseEnd_406682 < baseStart_406682 := by decide
  rcases family_descends (prefixWord ++ tailWord_406682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406684 : List Nat := [2, 2, 3, 2, 1, 2, 7]
def baseStart_406684 : Nat := 118140960795 + 406684 * 2 ^ 59
def prefixEnd_406684 : Nat := 4983230072969 + 3 ^ 40 * 406684 * 2
def baseEnd_406684 : Nat := 41249257578902139393521

theorem tailTrace_406684 : CollatzResearch.WordTrace tailWord_406684 prefixEnd_406684 41249257578902139393521 := by
  unfold tailWord_406684
  simp only [CollatzResearch.WordTrace]
  refine ⟨7416492029330399471313553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9888656039107199295084737 7416492029330399471313553)
  ·
    refine ⟨5562369021997799603485165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7416492029330399471313553 5562369021997799603485165)
    ·
      refine ⟨2085888383249174851306937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5562369021997799603485165 2085888383249174851306937)
      ·
        refine ⟨1564416287436881138480203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2085888383249174851306937 1564416287436881138480203)
        ·
          refine ⟨2346624431155321707720305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1564416287436881138480203 2346624431155321707720305)
          ·
            refine ⟨1759968323366491280790229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2346624431155321707720305 1759968323366491280790229)
            ·
              refine ⟨41249257578902139393521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1759968323366491280790229 41249257578902139393521)
              ·
                rfl

theorem cell19_406684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 7].length) (baseStart_406684 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406684 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406684 prefixEnd_406684 := by exact prefixLift 406684
  have htrace : WordTrace (prefixWord ++ tailWord_406684) baseStart_406684 baseEnd_406684 := by
    simpa [prefixWord, tailWord_406684, baseEnd_406684] using wordTrace_append hprefix tailTrace_406684
  have hstable : (prefixWord ++ tailWord_406684).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406684).length < 2 ^ (prefixWord ++ tailWord_406684).sum := by decide
  have hdescent : baseEnd_406684 < baseStart_406684 := by decide
  rcases family_descends (prefixWord ++ tailWord_406684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406741 : List Nat := [1, 3, 2, 4, 1, 8]
def baseStart_406741 : Nat := 118140960795 + 406741 * 2 ^ 59
def prefixEnd_406741 : Nat := 4983230072969 + 3 ^ 40 * 406741 * 2
def baseEnd_406741 : Nat := 13751679663571908323749

theorem tailTrace_406741 : CollatzResearch.WordTrace tailWord_406741 prefixEnd_406741 13751679663571908323749 := by
  unfold tailWord_406741
  simp only [CollatzResearch.WordTrace]
  refine ⟨14835063019454297677452077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9890042012969531784968051 14835063019454297677452077)
  ·
    refine ⟨5563148632295361629044529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14835063019454297677452077 5563148632295361629044529)
    ·
      refine ⟨4172361474221521221783397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5563148632295361629044529 4172361474221521221783397)
      ·
        refine ⟨782317776416535229084387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4172361474221521221783397 782317776416535229084387)
        ·
          refine ⟨1173476664624802843626581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782317776416535229084387 1173476664624802843626581)
          ·
            refine ⟨13751679663571908323749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1173476664624802843626581 13751679663571908323749)
            ·
              rfl

theorem cell19_406741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 8].length) (baseStart_406741 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406741 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406741 prefixEnd_406741 := by exact prefixLift 406741
  have htrace : WordTrace (prefixWord ++ tailWord_406741) baseStart_406741 baseEnd_406741 := by
    simpa [prefixWord, tailWord_406741, baseEnd_406741] using wordTrace_append hprefix tailTrace_406741
  have hstable : (prefixWord ++ tailWord_406741).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406741).length < 2 ^ (prefixWord ++ tailWord_406741).sum := by decide
  have hdescent : baseEnd_406741 < baseStart_406741 := by decide
  rcases family_descends (prefixWord ++ tailWord_406741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406798 : List Nat := [4, 1, 1, 2, 1, 4, 6]
def baseStart_406798 : Nat := 118140960795 + 406798 * 2 ^ 59
def prefixEnd_406798 : Nat := 4983230072969 + 3 ^ 40 * 406798 * 2
def baseEnd_406798 : Nat := 41260820402529310548973

theorem tailTrace_406798 : CollatzResearch.WordTrace tailWord_406798 prefixEnd_406798 41260820402529310548973 := by
  unfold tailWord_406798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1854642747530974551534631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9891427986831864274851365 1854642747530974551534631)
  ·
    refine ⟨2781964121296461827301947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1854642747530974551534631 2781964121296461827301947)
    ·
      refine ⟨4172946181944692740952921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2781964121296461827301947 4172946181944692740952921)
      ·
        refine ⟨3129709636458519555714691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4172946181944692740952921 3129709636458519555714691)
        ·
          refine ⟨4694564454687779333572037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3129709636458519555714691 4694564454687779333572037)
          ·
            refine ⟨880230835253958625044757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4694564454687779333572037 880230835253958625044757)
            ·
              refine ⟨41260820402529310548973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 880230835253958625044757 41260820402529310548973)
              ·
                rfl

theorem cell19_406798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 6].length) (baseStart_406798 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406798 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406798 prefixEnd_406798 := by exact prefixLift 406798
  have htrace : WordTrace (prefixWord ++ tailWord_406798) baseStart_406798 baseEnd_406798 := by
    simpa [prefixWord, tailWord_406798, baseEnd_406798] using wordTrace_append hprefix tailTrace_406798
  have hstable : (prefixWord ++ tailWord_406798).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406798).length < 2 ^ (prefixWord ++ tailWord_406798).sum := by decide
  have hdescent : baseEnd_406798 < baseStart_406798 := by decide
  rcases family_descends (prefixWord ++ tailWord_406798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406834 : List Nat := [3, 2, 1, 1, 4, 1, 4, 3]
def baseStart_406834 : Nat := 118140960795 + 406834 * 2 ^ 59
def prefixEnd_406834 : Nat := 4983230072969 + 3 ^ 40 * 406834 * 2
def baseEnd_406834 : Nat := 123793415461550514846821

theorem tailTrace_406834 : CollatzResearch.WordTrace tailWord_406834 prefixEnd_406834 123793415461550514846821 := by
  unfold tailWord_406834
  simp only [CollatzResearch.WordTrace]
  refine ⟨3709613752029343640146889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9892303338744916373725037 3709613752029343640146889)
  ·
    refine ⟨2782210314022007730110167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3709613752029343640146889 2782210314022007730110167)
    ·
      refine ⟨4173315471033011595165251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2782210314022007730110167 4173315471033011595165251)
      ·
        refine ⟨6259973206549517392747877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4173315471033011595165251 6259973206549517392747877)
        ·
          refine ⟨1173744976228034511140227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6259973206549517392747877 1173744976228034511140227)
          ·
            refine ⟨1760617464342051766710341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1173744976228034511140227 1760617464342051766710341)
            ·
              refine ⟨330115774564134706258189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1760617464342051766710341 330115774564134706258189)
              ·
                refine ⟨123793415461550514846821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330115774564134706258189 123793415461550514846821)
                ·
                  rfl

theorem cell19_406834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_406834 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406834 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406834 prefixEnd_406834 := by exact prefixLift 406834
  have htrace : WordTrace (prefixWord ++ tailWord_406834) baseStart_406834 baseEnd_406834 := by
    simpa [prefixWord, tailWord_406834, baseEnd_406834] using wordTrace_append hprefix tailTrace_406834
  have hstable : (prefixWord ++ tailWord_406834).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406834).length < 2 ^ (prefixWord ++ tailWord_406834).sum := by decide
  have hdescent : baseEnd_406834 < baseStart_406834 := by decide
  rcases family_descends (prefixWord ++ tailWord_406834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406855 : List Nat := [1, 1, 4, 1, 2, 5, 5]
def baseStart_406855 : Nat := 118140960795 + 406855 * 2 ^ 59
def prefixEnd_406855 : Nat := 4983230072969 + 3 ^ 40 * 406855 * 2
def baseEnd_406855 : Nat := 41266601814342896126699

theorem tailTrace_406855 : CollatzResearch.WordTrace tailWord_406855 prefixEnd_406855 41266601814342896126699 := by
  unfold tailWord_406855
  simp only [CollatzResearch.WordTrace]
  refine ⟨14839220941041295147102019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9892813960694196764734679 14839220941041295147102019)
  ·
    refine ⟨22258831411561942720653029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14839220941041295147102019 22258831411561942720653029)
    ·
      refine ⟨4173530889667864260122443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22258831411561942720653029 4173530889667864260122443)
      ·
        refine ⟨6260296334501796390183665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4173530889667864260122443 6260296334501796390183665)
        ·
          refine ⟨4695222250876347292637749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6260296334501796390183665 4695222250876347292637749)
          ·
            refine ⟨440177086019657558684789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4695222250876347292637749 440177086019657558684789)
            ·
              refine ⟨41266601814342896126699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 440177086019657558684789 41266601814342896126699)
              ·
                rfl

theorem cell19_406855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5, 5].length) (baseStart_406855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406855 prefixEnd_406855 := by exact prefixLift 406855
  have htrace : WordTrace (prefixWord ++ tailWord_406855) baseStart_406855 baseEnd_406855 := by
    simpa [prefixWord, tailWord_406855, baseEnd_406855] using wordTrace_append hprefix tailTrace_406855
  have hstable : (prefixWord ++ tailWord_406855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406855).length < 2 ^ (prefixWord ++ tailWord_406855).sum := by decide
  have hdescent : baseEnd_406855 < baseStart_406855 := by decide
  rcases family_descends (prefixWord ++ tailWord_406855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406857 : List Nat := [1, 2, 1, 1, 2, 3, 9]
def baseStart_406857 : Nat := 118140960795 + 406857 * 2 ^ 59
def prefixEnd_406857 : Nat := 4983230072969 + 3 ^ 40 * 406857 * 2
def baseEnd_406857 : Nat := 41266804670897758778549

theorem tailTrace_406857 : CollatzResearch.WordTrace tailWord_406857 prefixEnd_406857 41266804670897758778549 := by
  unfold tailWord_406857
  simp only [CollatzResearch.WordTrace]
  refine ⟨14839293887034049488674825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9892862591356032992449883 14839293887034049488674825)
  ·
    refine ⟨11129470415275537116506119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14839293887034049488674825 11129470415275537116506119)
    ·
      refine ⟨16694205622913305674759179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11129470415275537116506119 16694205622913305674759179)
      ·
        refine ⟨25041308434369958512138769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16694205622913305674759179 25041308434369958512138769)
        ·
          refine ⟨18780981325777468884104077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25041308434369958512138769 18780981325777468884104077)
          ·
            refine ⟨7042867997166550831539029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18780981325777468884104077 7042867997166550831539029)
            ·
              refine ⟨41266804670897758778549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7042867997166550831539029 41266804670897758778549)
              ·
                rfl

theorem cell19_406857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_406857 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406857 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406857 prefixEnd_406857 := by exact prefixLift 406857
  have htrace : WordTrace (prefixWord ++ tailWord_406857) baseStart_406857 baseEnd_406857 := by
    simpa [prefixWord, tailWord_406857, baseEnd_406857] using wordTrace_append hprefix tailTrace_406857
  have hstable : (prefixWord ++ tailWord_406857).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406857).length < 2 ^ (prefixWord ++ tailWord_406857).sum := by decide
  have hdescent : baseEnd_406857 < baseStart_406857 := by decide
  rcases family_descends (prefixWord ++ tailWord_406857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406893 : List Nat := [1, 5, 1, 1, 1, 3, 2, 5]
def baseStart_406893 : Nat := 118140960795 + 406893 * 2 ^ 59
def prefixEnd_406893 : Nat := 4983230072969 + 3 ^ 40 * 406893 * 2
def baseEnd_406893 : Nat := 123811368266655859535549

theorem tailTrace_406893 : CollatzResearch.WordTrace tailWord_406893 prefixEnd_406893 123811368266655859535549 := by
  unfold tailWord_406893
  simp only [CollatzResearch.WordTrace]
  refine ⟨14840606914903627636985333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9893737943269085091323555 14840606914903627636985333)
  ·
    refine ⟨1391306898272215090967375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14840606914903627636985333 1391306898272215090967375)
    ·
      refine ⟨2086960347408322636451063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1391306898272215090967375 2086960347408322636451063)
      ·
        refine ⟨3130440521112483954676595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2086960347408322636451063 3130440521112483954676595)
        ·
          refine ⟨4695660781668725932014893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3130440521112483954676595 4695660781668725932014893)
          ·
            refine ⟨1760872793125772224505585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4695660781668725932014893 1760872793125772224505585)
            ·
              refine ⟨1320654594844329168379189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1760872793125772224505585 1320654594844329168379189)
              ·
                refine ⟨123811368266655859535549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1320654594844329168379189 123811368266655859535549)
                ·
                  rfl

theorem cell19_406893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_406893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406893 prefixEnd_406893 := by exact prefixLift 406893
  have htrace : WordTrace (prefixWord ++ tailWord_406893) baseStart_406893 baseEnd_406893 := by
    simpa [prefixWord, tailWord_406893, baseEnd_406893] using wordTrace_append hprefix tailTrace_406893
  have hstable : (prefixWord ++ tailWord_406893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406893).length < 2 ^ (prefixWord ++ tailWord_406893).sum := by decide
  have hdescent : baseEnd_406893 < baseStart_406893 := by decide
  rcases family_descends (prefixWord ++ tailWord_406893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406895 : List Nat := [1, 1, 2, 1, 3, 1, 3, 7]
def baseStart_406895 : Nat := 118140960795 + 406895 * 2 ^ 59
def prefixEnd_406895 : Nat := 4983230072969 + 3 ^ 40 * 406895 * 2
def baseEnd_406895 : Nat := 123811976836320447491099

theorem tailTrace_406895 : CollatzResearch.WordTrace tailWord_406895 prefixEnd_406895 123811976836320447491099 := by
  unfold tailWord_406895
  simp only [CollatzResearch.WordTrace]
  refine ⟨14840679860896381978558139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9893786573930921319038759 14840679860896381978558139)
  ·
    refine ⟨22261019791344572967837209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14840679860896381978558139 22261019791344572967837209)
    ·
      refine ⟨16695764843508429725877907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22261019791344572967837209 16695764843508429725877907)
      ·
        refine ⟨25043647265262644588816861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16695764843508429725877907 25043647265262644588816861)
        ·
          refine ⟨9391367724473491720806323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25043647265262644588816861 9391367724473491720806323)
          ·
            refine ⟨14087051586710237581209485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9391367724473491720806323 14087051586710237581209485)
            ·
              refine ⟨5282644345016339092953557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14087051586710237581209485 5282644345016339092953557)
              ·
                refine ⟨123811976836320447491099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5282644345016339092953557 123811976836320447491099)
                ·
                  rfl

theorem cell19_406895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 7].length) (baseStart_406895 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406895 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406895 prefixEnd_406895 := by exact prefixLift 406895
  have htrace : WordTrace (prefixWord ++ tailWord_406895) baseStart_406895 baseEnd_406895 := by
    simpa [prefixWord, tailWord_406895, baseEnd_406895] using wordTrace_append hprefix tailTrace_406895
  have hstable : (prefixWord ++ tailWord_406895).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406895).length < 2 ^ (prefixWord ++ tailWord_406895).sum := by decide
  have hdescent : baseEnd_406895 < baseStart_406895 := by decide
  rcases family_descends (prefixWord ++ tailWord_406895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406910 : List Nat := [4, 2, 3, 2, 8]
def baseStart_406910 : Nat := 118140960795 + 406910 * 2 ^ 59
def prefixEnd_406910 : Nat := 4983230072969 + 3 ^ 40 * 406910 * 2
def baseEnd_406910 : Nat := 4585797818844624339175

theorem tailTrace_406910 : CollatzResearch.WordTrace tailWord_406910 prefixEnd_406910 4585797818844624339175 := by
  unfold tailWord_406910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1855153369480254942544273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9894151303894693026902789 1855153369480254942544273)
  ·
    refine ⟨1391365027110191206908205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1855153369480254942544273 1391365027110191206908205)
    ·
      refine ⟨521761885166321702590577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1391365027110191206908205 521761885166321702590577)
      ·
        refine ⟨391321413874741276942933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 521761885166321702590577 391321413874741276942933)
        ·
          refine ⟨4585797818844624339175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 391321413874741276942933 4585797818844624339175)
          ·
            rfl

theorem cell19_406910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 8].length) (baseStart_406910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406910 prefixEnd_406910 := by exact prefixLift 406910
  have htrace : WordTrace (prefixWord ++ tailWord_406910) baseStart_406910 baseEnd_406910 := by
    simpa [prefixWord, tailWord_406910, baseEnd_406910] using wordTrace_append hprefix tailTrace_406910
  have hstable : (prefixWord ++ tailWord_406910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406910).length < 2 ^ (prefixWord ++ tailWord_406910).sum := by decide
  have hdescent : baseEnd_406910 < baseStart_406910 := by decide
  rcases family_descends (prefixWord ++ tailWord_406910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_406969 : List Nat := [1, 2, 1, 4, 4, 1, 6]
def baseStart_406969 : Nat := 118140960795 + 406969 * 2 ^ 59
def prefixEnd_406969 : Nat := 4983230072969 + 3 ^ 40 * 406969 * 2
def baseEnd_406969 : Nat := 41278164637970067282151

theorem tailTrace_406969 : CollatzResearch.WordTrace tailWord_406969 prefixEnd_406969 41278164637970067282151 := by
  unfold tailWord_406969
  simp only [CollatzResearch.WordTrace]
  refine ⟨14843378862628292616751961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9895585908418861744501307 14843378862628292616751961)
  ·
    refine ⟨11132534146971219462563971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14843378862628292616751961 11132534146971219462563971)
    ·
      refine ⟨16698801220456829193845957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11132534146971219462563971 16698801220456829193845957)
      ·
        refine ⟨3131025228835655473846117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16698801220456829193845957 3131025228835655473846117)
        ·
          refine ⟨587067230406685401346147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3131025228835655473846117 587067230406685401346147)
          ·
            refine ⟨880600845610028102019221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587067230406685401346147 880600845610028102019221)
            ·
              refine ⟨41278164637970067282151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 880600845610028102019221 41278164637970067282151)
              ·
                rfl

theorem cell19_406969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 6].length) (baseStart_406969 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_406969 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_406969 prefixEnd_406969 := by exact prefixLift 406969
  have htrace : WordTrace (prefixWord ++ tailWord_406969) baseStart_406969 baseEnd_406969 := by
    simpa [prefixWord, tailWord_406969, baseEnd_406969] using wordTrace_append hprefix tailTrace_406969
  have hstable : (prefixWord ++ tailWord_406969).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_406969).length < 2 ^ (prefixWord ++ tailWord_406969).sum := by decide
  have hdescent : baseEnd_406969 < baseStart_406969 := by decide
  rcases family_descends (prefixWord ++ tailWord_406969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407005 : List Nat := [1, 4, 3, 1, 1, 2, 4, 3]
def baseStart_407005 : Nat := 118140960795 + 407005 * 2 ^ 59
def prefixEnd_407005 : Nat := 4983230072969 + 3 ^ 40 * 407005 * 2
def baseEnd_407005 : Nat := 123845448167872785046355

theorem tailTrace_407005 : CollatzResearch.WordTrace tailWord_407005 prefixEnd_407005 123845448167872785046355 := by
  unfold tailWord_407005
  simp only [CollatzResearch.WordTrace]
  refine ⟨14844691890497870765062469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9896461260331913843374979 14844691890497870765062469)
  ·
    refine ⟨2783379729468350768449213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14844691890497870765062469 2783379729468350768449213)
    ·
      refine ⟨1043767398550631538168455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2783379729468350768449213 1043767398550631538168455)
      ·
        refine ⟨1565651097825947307252683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1043767398550631538168455 1565651097825947307252683)
        ·
          refine ⟨2348476646738920960879025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1565651097825947307252683 2348476646738920960879025)
          ·
            refine ⟨1761357485054190720659269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2348476646738920960879025 1761357485054190720659269)
            ·
              refine ⟨330254528447660760123613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1761357485054190720659269 330254528447660760123613)
              ·
                refine ⟨123845448167872785046355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330254528447660760123613 123845448167872785046355)
                ·
                  rfl

theorem cell19_407005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 3].length) (baseStart_407005 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407005 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407005 prefixEnd_407005 := by exact prefixLift 407005
  have htrace : WordTrace (prefixWord ++ tailWord_407005) baseStart_407005 baseEnd_407005 := by
    simpa [prefixWord, tailWord_407005, baseEnd_407005] using wordTrace_append hprefix tailTrace_407005
  have hstable : (prefixWord ++ tailWord_407005).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407005).length < 2 ^ (prefixWord ++ tailWord_407005).sum := by decide
  have hdescent : baseEnd_407005 < baseStart_407005 := by decide
  rcases family_descends (prefixWord ++ tailWord_407005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407026 : List Nat := [3, 2, 1, 4, 1, 1, 7]
def baseStart_407026 : Nat := 118140960795 + 407026 * 2 ^ 59
def prefixEnd_407026 : Nat := 4983230072969 + 3 ^ 40 * 407026 * 2
def baseEnd_407026 : Nat := 41283946049783652859877

theorem tailTrace_407026 : CollatzResearch.WordTrace tailWord_407026 prefixEnd_407026 41283946049783652859877 := by
  unfold tailWord_407026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3711364455855447837894233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9896971882281194234384621 3711364455855447837894233)
  ·
    refine ⟨2783523341891585878420675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3711364455855447837894233 2783523341891585878420675)
    ·
      refine ⟨4175285012837378817631013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2783523341891585878420675 4175285012837378817631013)
      ·
        refine ⟨782865939907008528305815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4175285012837378817631013 782865939907008528305815)
        ·
          refine ⟨1174298909860512792458723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 782865939907008528305815 1174298909860512792458723)
          ·
            refine ⟨1761448364790769188688085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1174298909860512792458723 1761448364790769188688085)
            ·
              refine ⟨41283946049783652859877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1761448364790769188688085 41283946049783652859877)
              ·
                rfl

theorem cell19_407026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 7].length) (baseStart_407026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407026 prefixEnd_407026 := by exact prefixLift 407026
  have htrace : WordTrace (prefixWord ++ tailWord_407026) baseStart_407026 baseEnd_407026 := by
    simpa [prefixWord, tailWord_407026, baseEnd_407026] using wordTrace_append hprefix tailTrace_407026
  have hstable : (prefixWord ++ tailWord_407026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407026).length < 2 ^ (prefixWord ++ tailWord_407026).sum := by decide
  have hdescent : baseEnd_407026 < baseStart_407026 := by decide
  rcases family_descends (prefixWord ++ tailWord_407026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407100 : List Nat := [2, 2, 2, 2, 4, 2, 1, 4]
def baseStart_407100 : Nat := 118140960795 + 407100 * 2 ^ 59
def prefixEnd_407100 : Nat := 4983230072969 + 3 ^ 40 * 407100 * 2
def baseEnd_407100 : Nat := 123874355226940712934985

theorem tailTrace_407100 : CollatzResearch.WordTrace tailWord_407100 prefixEnd_407100 123874355226940712934985 := by
  unfold tailWord_407100
  simp only [CollatzResearch.WordTrace]
  refine ⟨7424078412576850994885377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9898771216769134659847169 7424078412576850994885377)
  ·
    refine ⟨5568058809432638246164033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7424078412576850994885377 5568058809432638246164033)
    ·
      refine ⟨4176044107074478684623025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5568058809432638246164033 4176044107074478684623025)
      ·
        refine ⟨3132033080305859013467269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4176044107074478684623025 3132033080305859013467269)
        ·
          refine ⟨587256202557348565025113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3132033080305859013467269 587256202557348565025113)
          ·
            refine ⟨440442151918011423768835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 587256202557348565025113 440442151918011423768835)
            ·
              refine ⟨660663227877017135653253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440442151918011423768835 660663227877017135653253)
              ·
                refine ⟨123874355226940712934985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 660663227877017135653253 123874355226940712934985)
                ·
                  rfl

theorem cell19_407100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_407100 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407100 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407100 prefixEnd_407100 := by exact prefixLift 407100
  have htrace : WordTrace (prefixWord ++ tailWord_407100) baseStart_407100 baseEnd_407100 := by
    simpa [prefixWord, tailWord_407100, baseEnd_407100] using wordTrace_append hprefix tailTrace_407100
  have hstable : (prefixWord ++ tailWord_407100).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407100).length < 2 ^ (prefixWord ++ tailWord_407100).sum := by decide
  have hdescent : baseEnd_407100 < baseStart_407100 := by decide
  rcases family_descends (prefixWord ++ tailWord_407100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407117 : List Nat := [1, 6, 1, 1, 3, 1, 3, 3]
def baseStart_407117 : Nat := 118140960795 + 407117 * 2 ^ 59
def prefixEnd_407117 : Nat := 4983230072969 + 3 ^ 40 * 407117 * 2
def baseEnd_407117 : Nat := 123879528069089710557161

theorem tailTrace_407117 : CollatzResearch.WordTrace tailWord_407117 prefixEnd_407117 123879528069089710557161 := by
  unfold tailWord_407117
  simp only [CollatzResearch.WordTrace]
  refine ⟨14848776866092113893139605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9899184577394742595426403 14848776866092113893139605)
  ·
    refine ⟨696036415598067838740919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14848776866092113893139605 696036415598067838740919)
    ·
      refine ⟨1044054623397101758111379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 696036415598067838740919 1044054623397101758111379)
      ·
        refine ⟨1566081935095652637167069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044054623397101758111379 1566081935095652637167069)
        ·
          refine ⟨587280725660869738937651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1566081935095652637167069 587280725660869738937651)
          ·
            refine ⟨880921088491304608406477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587280725660869738937651 880921088491304608406477)
            ·
              refine ⟨330345408184239228152429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 880921088491304608406477 330345408184239228152429)
              ·
                refine ⟨123879528069089710557161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330345408184239228152429 123879528069089710557161)
                ·
                  rfl

theorem cell19_407117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 3].length) (baseStart_407117 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407117 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407117 prefixEnd_407117 := by exact prefixLift 407117
  have htrace : WordTrace (prefixWord ++ tailWord_407117) baseStart_407117 baseEnd_407117 := by
    simpa [prefixWord, tailWord_407117, baseEnd_407117] using wordTrace_append hprefix tailTrace_407117
  have hstable : (prefixWord ++ tailWord_407117).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407117).length < 2 ^ (prefixWord ++ tailWord_407117).sum := by decide
  have hdescent : baseEnd_407117 < baseStart_407117 := by decide
  rcases family_descends (prefixWord ++ tailWord_407117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407121 : List Nat := [1, 2, 2, 1, 3, 2, 5, 3]
def baseStart_407121 : Nat := 118140960795 + 407121 * 2 ^ 59
def prefixEnd_407121 : Nat := 4983230072969 + 3 ^ 40 * 407121 * 2
def baseEnd_407121 : Nat := 123880745208418886468261

theorem tailTrace_407121 : CollatzResearch.WordTrace tailWord_407121 prefixEnd_407121 123880745208418886468261 := by
  unfold tailWord_407121
  simp only [CollatzResearch.WordTrace]
  refine ⟨14848922758077622576285217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9899281838718415050856811 14848922758077622576285217)
  ·
    refine ⟨11136692068558216932213913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14848922758077622576285217 11136692068558216932213913)
    ·
      refine ⟨8352519051418662699160435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11136692068558216932213913 8352519051418662699160435)
      ·
        refine ⟨12528778577127994048740653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8352519051418662699160435 12528778577127994048740653)
        ·
          refine ⟨4698291966422997768277745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12528778577127994048740653 4698291966422997768277745)
          ·
            refine ⟨3523718974817248326208309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4698291966422997768277745 3523718974817248326208309)
            ·
              refine ⟨330348653889117030582029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3523718974817248326208309 330348653889117030582029)
              ·
                refine ⟨123880745208418886468261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330348653889117030582029 123880745208418886468261)
                ·
                  rfl

theorem cell19_407121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 5, 3].length) (baseStart_407121 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407121 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407121 prefixEnd_407121 := by exact prefixLift 407121
  have htrace : WordTrace (prefixWord ++ tailWord_407121) baseStart_407121 baseEnd_407121 := by
    simpa [prefixWord, tailWord_407121, baseEnd_407121] using wordTrace_append hprefix tailTrace_407121
  have hstable : (prefixWord ++ tailWord_407121).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407121).length < 2 ^ (prefixWord ++ tailWord_407121).sum := by decide
  have hdescent : baseEnd_407121 < baseStart_407121 := by decide
  rcases family_descends (prefixWord ++ tailWord_407121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407161 : List Nat := [1, 2, 1, 3, 3, 1, 2, 6]
def baseStart_407161 : Nat := 118140960795 + 407161 * 2 ^ 59
def prefixEnd_407161 : Nat := 4983230072969 + 3 ^ 40 * 407161 * 2
def baseEnd_407161 : Nat := 123892916601710645579263

theorem tailTrace_407161 : CollatzResearch.WordTrace tailWord_407161 prefixEnd_407161 123892916601710645579263 := by
  unfold tailWord_407161
  simp only [CollatzResearch.WordTrace]
  refine ⟨14850381677932709407741337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9900254451955139605160891 14850381677932709407741337)
  ·
    refine ⟨11137786258449532055806003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14850381677932709407741337 11137786258449532055806003)
    ·
      refine ⟨16706679387674298083709005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11137786258449532055806003 16706679387674298083709005)
      ·
        refine ⟨6265004770377861781390877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16706679387674298083709005 6265004770377861781390877)
        ·
          refine ⟨2349376788891698168021579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6265004770377861781390877 2349376788891698168021579)
          ·
            refine ⟨3524065183337547252032369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2349376788891698168021579 3524065183337547252032369)
            ·
              refine ⟨2643048887503160439024277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3524065183337547252032369 2643048887503160439024277)
              ·
                refine ⟨123892916601710645579263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2643048887503160439024277 123892916601710645579263)
                ·
                  rfl

theorem cell19_407161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 6].length) (baseStart_407161 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407161 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407161 prefixEnd_407161 := by exact prefixLift 407161
  have htrace : WordTrace (prefixWord ++ tailWord_407161) baseStart_407161 baseEnd_407161 := by
    simpa [prefixWord, tailWord_407161, baseEnd_407161] using wordTrace_append hprefix tailTrace_407161
  have hstable : (prefixWord ++ tailWord_407161).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407161).length < 2 ^ (prefixWord ++ tailWord_407161).sum := by decide
  have hdescent : baseEnd_407161 < baseStart_407161 := by decide
  rcases family_descends (prefixWord ++ tailWord_407161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407176 : List Nat := [2, 1, 3, 5, 1, 1, 1, 5]
def baseStart_407176 : Nat := 118140960795 + 407176 * 2 ^ 59
def prefixEnd_407176 : Nat := 4983230072969 + 3 ^ 40 * 407176 * 2
def baseEnd_407176 : Nat := 123897480874195055245889

theorem tailTrace_407176 : CollatzResearch.WordTrace tailWord_407176 prefixEnd_407176 123897480874195055245889 := by
  unfold tailWord_407176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7425464386439183484768691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9900619181918911313024921 7425464386439183484768691)
  ·
    refine ⟨11138196579658775227153037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7425464386439183484768691 11138196579658775227153037)
    ·
      refine ⟨4176823717372040710182389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11138196579658775227153037 4176823717372040710182389)
      ·
        refine ⟨391577223503628816579599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4176823717372040710182389 391577223503628816579599)
        ·
          refine ⟨587365835255443224869399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391577223503628816579599 587365835255443224869399)
          ·
            refine ⟨881048752883164837304099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587365835255443224869399 881048752883164837304099)
            ·
              refine ⟨1321573129324747255956149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881048752883164837304099 1321573129324747255956149)
              ·
                refine ⟨123897480874195055245889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1321573129324747255956149 123897480874195055245889)
                ·
                  rfl

theorem cell19_407176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 1, 5].length) (baseStart_407176 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407176 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407176 prefixEnd_407176 := by exact prefixLift 407176
  have htrace : WordTrace (prefixWord ++ tailWord_407176) baseStart_407176 baseEnd_407176 := by
    simpa [prefixWord, tailWord_407176, baseEnd_407176] using wordTrace_append hprefix tailTrace_407176
  have hstable : (prefixWord ++ tailWord_407176).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407176).length < 2 ^ (prefixWord ++ tailWord_407176).sum := by decide
  have hdescent : baseEnd_407176 < baseStart_407176 := by decide
  rcases family_descends (prefixWord ++ tailWord_407176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407178 : List Nat := [3, 1, 2, 3, 2, 2, 1, 5]
def baseStart_407178 : Nat := 118140960795 + 407178 * 2 ^ 59
def prefixEnd_407178 : Nat := 4983230072969 + 3 ^ 40 * 407178 * 2
def baseEnd_407178 : Nat := 123898089443859643201439

theorem tailTrace_407178 : CollatzResearch.WordTrace tailWord_407178 prefixEnd_407178 123898089443859643201439 := by
  unfold tailWord_407178
  simp only [CollatzResearch.WordTrace]
  refine ⟨3712750429717780327777547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9900667812580747540740125 3712750429717780327777547)
  ·
    refine ⟨5569125644576670491666321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3712750429717780327777547 5569125644576670491666321)
    ·
      refine ⟨4176844233432502868749741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5569125644576670491666321 4176844233432502868749741)
      ·
        refine ⟨1566316587537188575781153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4176844233432502868749741 1566316587537188575781153)
        ·
          refine ⟨1174737440652891431835865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1566316587537188575781153 1174737440652891431835865)
          ·
            refine ⟨881053080489668573876899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1174737440652891431835865 881053080489668573876899)
            ·
              refine ⟨1321579620734502860815349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881053080489668573876899 1321579620734502860815349)
              ·
                refine ⟨123898089443859643201439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1321579620734502860815349 123898089443859643201439)
                ·
                  rfl

theorem cell19_407178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_407178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407178 prefixEnd_407178 := by exact prefixLift 407178
  have htrace : WordTrace (prefixWord ++ tailWord_407178) baseStart_407178 baseEnd_407178 := by
    simpa [prefixWord, tailWord_407178, baseEnd_407178] using wordTrace_append hprefix tailTrace_407178
  have hstable : (prefixWord ++ tailWord_407178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407178).length < 2 ^ (prefixWord ++ tailWord_407178).sum := by decide
  have hdescent : baseEnd_407178 < baseStart_407178 := by decide
  rcases family_descends (prefixWord ++ tailWord_407178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407180 : List Nat := [2, 2, 1, 2, 1, 1, 5, 5]
def baseStart_407180 : Nat := 118140960795 + 407180 * 2 ^ 59
def prefixEnd_407180 : Nat := 4983230072969 + 3 ^ 40 * 407180 * 2
def baseEnd_407180 : Nat := 123898698013524231156989

theorem tailTrace_407180 : CollatzResearch.WordTrace tailWord_407180 prefixEnd_407180 123898698013524231156989 := by
  unfold tailWord_407180
  simp only [CollatzResearch.WordTrace]
  refine ⟨7425537332431937826341497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9900716443242583768455329 7425537332431937826341497)
  ·
    refine ⟨5569152999323953369756123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7425537332431937826341497 5569152999323953369756123)
    ·
      refine ⟨8353729498985930054634185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5569152999323953369756123 8353729498985930054634185)
      ·
        refine ⟨6265297124239447540975639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8353729498985930054634185 6265297124239447540975639)
        ·
          refine ⟨9397945686359171311463459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6265297124239447540975639 9397945686359171311463459)
          ·
            refine ⟨14096918529538756967195189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9397945686359171311463459 14096918529538756967195189)
            ·
              refine ⟨1321586112144258465674549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14096918529538756967195189 1321586112144258465674549)
              ·
                refine ⟨123898698013524231156989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1321586112144258465674549 123898698013524231156989)
                ·
                  rfl

theorem cell19_407180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 5].length) (baseStart_407180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407180 prefixEnd_407180 := by exact prefixLift 407180
  have htrace : WordTrace (prefixWord ++ tailWord_407180) baseStart_407180 baseEnd_407180 := by
    simpa [prefixWord, tailWord_407180, baseEnd_407180] using wordTrace_append hprefix tailTrace_407180
  have hstable : (prefixWord ++ tailWord_407180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407180).length < 2 ^ (prefixWord ++ tailWord_407180).sum := by decide
  have hdescent : baseEnd_407180 < baseStart_407180 := by decide
  rcases family_descends (prefixWord ++ tailWord_407180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407218 : List Nat := [3, 2, 1, 1, 1, 2, 3, 6]
def baseStart_407218 : Nat := 118140960795 + 407218 * 2 ^ 59
def prefixEnd_407218 : Nat := 4983230072969 + 3 ^ 40 * 407218 * 2
def baseEnd_407218 : Nat := 123910260837151402312441

theorem tailTrace_407218 : CollatzResearch.WordTrace tailWord_407218 prefixEnd_407218 123910260837151402312441 := by
  unfold tailWord_407218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3713115159681552035641577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9901640425817472095044205 3713115159681552035641577)
  ·
    refine ⟨2784836369761164026731183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3713115159681552035641577 2784836369761164026731183)
    ·
      refine ⟨4177254554641746040096775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2784836369761164026731183 4177254554641746040096775)
      ·
        refine ⟨6265881831962619060145163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4177254554641746040096775 6265881831962619060145163)
        ·
          refine ⟨9398822747943928590217745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6265881831962619060145163 9398822747943928590217745)
          ·
            refine ⟨7049117060957946442663309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9398822747943928590217745 7049117060957946442663309)
            ·
              refine ⟨2643418897859229915998741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7049117060957946442663309 2643418897859229915998741)
              ·
                refine ⟨123910260837151402312441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2643418897859229915998741 123910260837151402312441)
                ·
                  rfl

theorem cell19_407218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_407218 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407218 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407218 prefixEnd_407218 := by exact prefixLift 407218
  have htrace : WordTrace (prefixWord ++ tailWord_407218) baseStart_407218 baseEnd_407218 := by
    simpa [prefixWord, tailWord_407218, baseEnd_407218] using wordTrace_append hprefix tailTrace_407218
  have hstable : (prefixWord ++ tailWord_407218).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407218).length < 2 ^ (prefixWord ++ tailWord_407218).sum := by decide
  have hdescent : baseEnd_407218 < baseStart_407218 := by decide
  rcases family_descends (prefixWord ++ tailWord_407218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407275 : List Nat := [1, 1, 1, 1, 2, 4, 5, 4]
def baseStart_407275 : Nat := 118140960795 + 407275 * 2 ^ 59
def prefixEnd_407275 : Nat := 4983230072969 + 3 ^ 40 * 407275 * 2
def baseEnd_407275 : Nat := 123927605072592159045619

theorem tailTrace_407275 : CollatzResearch.WordTrace tailWord_407275 prefixEnd_407275 123927605072592159045619 := by
  unfold tailWord_407275
  simp only [CollatzResearch.WordTrace]
  refine ⟨14854539599519706877391279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9903026399679804584927519 14854539599519706877391279)
  ·
    refine ⟨22281809399279560316086919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14854539599519706877391279 22281809399279560316086919)
    ·
      refine ⟨33422714098919340474130379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22281809399279560316086919 33422714098919340474130379)
      ·
        refine ⟨50134071148379010711195569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33422714098919340474130379 50134071148379010711195569)
        ·
          refine ⟨37600553361284258033396677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50134071148379010711195569 37600553361284258033396677)
          ·
            refine ⟨7050103755240798381261877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37600553361284258033396677 7050103755240798381261877)
            ·
              refine ⟨660947227053824848243301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7050103755240798381261877 660947227053824848243301)
              ·
                refine ⟨123927605072592159045619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 660947227053824848243301 123927605072592159045619)
                ·
                  rfl

theorem cell19_407275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 4].length) (baseStart_407275 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407275 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407275 prefixEnd_407275 := by exact prefixLift 407275
  have htrace : WordTrace (prefixWord ++ tailWord_407275) baseStart_407275 baseEnd_407275 := by
    simpa [prefixWord, tailWord_407275, baseEnd_407275] using wordTrace_append hprefix tailTrace_407275
  have hstable : (prefixWord ++ tailWord_407275).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407275).length < 2 ^ (prefixWord ++ tailWord_407275).sum := by decide
  have hdescent : baseEnd_407275 < baseStart_407275 := by decide
  rcases family_descends (prefixWord ++ tailWord_407275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407292 : List Nat := [2, 2, 2, 1, 3, 1, 5, 3]
def baseStart_407292 : Nat := 118140960795 + 407292 * 2 ^ 59
def prefixEnd_407292 : Nat := 4983230072969 + 3 ^ 40 * 407292 * 2
def baseEnd_407292 : Nat := 123932777914741156667795

theorem tailTrace_407292 : CollatzResearch.WordTrace tailWord_407292 prefixEnd_407292 123932777914741156667795 := by
  unfold tailWord_407292
  simp only [CollatzResearch.WordTrace]
  refine ⟨7427579820229059390380065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9903439760305412520506753 7427579820229059390380065)
  ·
    refine ⟨5570684865171794542785049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7427579820229059390380065 5570684865171794542785049)
    ·
      refine ⟨4178013648878845907088787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5570684865171794542785049 4178013648878845907088787)
      ·
        refine ⟨6267020473318268860633181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4178013648878845907088787 6267020473318268860633181)
        ·
          refine ⟨2350132677494350822737443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6267020473318268860633181 2350132677494350822737443)
          ·
            refine ⟨3525199016241526234106165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2350132677494350822737443 3525199016241526234106165)
            ·
              refine ⟨330487407772643084447453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3525199016241526234106165 330487407772643084447453)
              ·
                refine ⟨123932777914741156667795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330487407772643084447453 123932777914741156667795)
                ·
                  rfl

theorem cell19_407292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 3].length) (baseStart_407292 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407292 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407292 prefixEnd_407292 := by exact prefixLift 407292
  have htrace : WordTrace (prefixWord ++ tailWord_407292) baseStart_407292 baseEnd_407292 := by
    simpa [prefixWord, tailWord_407292, baseEnd_407292] using wordTrace_append hprefix tailTrace_407292
  have hstable : (prefixWord ++ tailWord_407292).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407292).length < 2 ^ (prefixWord ++ tailWord_407292).sum := by decide
  have hdescent : baseEnd_407292 < baseStart_407292 := by decide
  rcases family_descends (prefixWord ++ tailWord_407292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407347 : List Nat := [1, 1, 1, 2, 7, 2, 2, 3]
def baseStart_407347 : Nat := 118140960795 + 407347 * 2 ^ 59
def prefixEnd_407347 : Nat := 4983230072969 + 3 ^ 40 * 407347 * 2
def baseEnd_407347 : Nat := 123949513580517325445423

theorem tailTrace_407347 : CollatzResearch.WordTrace tailWord_407347 prefixEnd_407347 123949513580517325445423 := by
  unfold tailWord_407347
  simp only [CollatzResearch.WordTrace]
  refine ⟨14857165655258863174012295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9904777103505908782674863 14857165655258863174012295)
  ·
    refine ⟨22285748482888294761018443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14857165655258863174012295 22285748482888294761018443)
    ·
      refine ⟨33428622724332442141527665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22285748482888294761018443 33428622724332442141527665)
      ·
        refine ⟨25071467043249331606145749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33428622724332442141527665 25071467043249331606145749)
        ·
          refine ⟨587612508826156209519041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 25071467043249331606145749 587612508826156209519041)
          ·
            refine ⟨440709381619617157139281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 587612508826156209519041 440709381619617157139281)
            ·
              refine ⟨330532036214712867854461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 440709381619617157139281 330532036214712867854461)
              ·
                refine ⟨123949513580517325445423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330532036214712867854461 123949513580517325445423)
                ·
                  rfl

theorem cell19_407347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 2, 2, 3].length) (baseStart_407347 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407347 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407347 prefixEnd_407347 := by exact prefixLift 407347
  have htrace : WordTrace (prefixWord ++ tailWord_407347) baseStart_407347 baseEnd_407347 := by
    simpa [prefixWord, tailWord_407347, baseEnd_407347] using wordTrace_append hprefix tailTrace_407347
  have hstable : (prefixWord ++ tailWord_407347).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407347).length < 2 ^ (prefixWord ++ tailWord_407347).sum := by decide
  have hdescent : baseEnd_407347 < baseStart_407347 := by decide
  rcases family_descends (prefixWord ++ tailWord_407347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407349 : List Nat := [1, 3, 3, 1, 4, 1, 1, 5]
def baseStart_407349 : Nat := 118140960795 + 407349 * 2 ^ 59
def prefixEnd_407349 : Nat := 4983230072969 + 3 ^ 40 * 407349 * 2
def baseEnd_407349 : Nat := 123950122150181913400973

theorem tailTrace_407349 : CollatzResearch.WordTrace tailWord_407349 prefixEnd_407349 123950122150181913400973 := by
  unfold tailWord_407349
  simp only [CollatzResearch.WordTrace]
  refine ⟨14857238601251617515585101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9904825734167745010390067 14857238601251617515585101)
  ·
    refine ⟨5571464475469356568344413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14857238601251617515585101 5571464475469356568344413)
    ·
      refine ⟨2089299178301008713129155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5571464475469356568344413 2089299178301008713129155)
      ·
        refine ⟨3133948767451513069693733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2089299178301008713129155 3133948767451513069693733)
        ·
          refine ⟨587615393897158700567575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3133948767451513069693733 587615393897158700567575)
          ·
            refine ⟨881423090845738050851363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587615393897158700567575 881423090845738050851363)
            ·
              refine ⟨1322134636268607076277045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881423090845738050851363 1322134636268607076277045)
              ·
                refine ⟨123950122150181913400973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1322134636268607076277045 123950122150181913400973)
                ·
                  rfl

theorem cell19_407349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 1, 5].length) (baseStart_407349 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407349 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407349 prefixEnd_407349 := by exact prefixLift 407349
  have htrace : WordTrace (prefixWord ++ tailWord_407349) baseStart_407349 baseEnd_407349 := by
    simpa [prefixWord, tailWord_407349, baseEnd_407349] using wordTrace_append hprefix tailTrace_407349
  have hstable : (prefixWord ++ tailWord_407349).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407349).length < 2 ^ (prefixWord ++ tailWord_407349).sum := by decide
  have hdescent : baseEnd_407349 < baseStart_407349 := by decide
  rcases family_descends (prefixWord ++ tailWord_407349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407366 : List Nat := [6, 1, 1, 2, 1, 1, 7]
def baseStart_407366 : Nat := 118140960795 + 407366 * 2 ^ 59
def prefixEnd_407366 : Nat := 4983230072969 + 3 ^ 40 * 407366 * 2
def baseEnd_407366 : Nat := 41318431664110303674383

theorem tailTrace_407366 : CollatzResearch.WordTrace tailWord_407366 prefixEnd_407366 41318431664110303674383 := by
  unfold tailWord_407366
  simp only [CollatzResearch.WordTrace]
  refine ⟨464308082568438419342311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9905239094793352945969301 464308082568438419342311)
  ·
    refine ⟨696462123852657629013467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 464308082568438419342311 696462123852657629013467)
    ·
      refine ⟨1044693185778986443520201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 696462123852657629013467 1044693185778986443520201)
      ·
        refine ⟨783519889334239832640151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1044693185778986443520201 783519889334239832640151)
        ·
          refine ⟨1175279834001359748960227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783519889334239832640151 1175279834001359748960227)
          ·
            refine ⟨1762919751002039623440341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175279834001359748960227 1762919751002039623440341)
            ·
              refine ⟨41318431664110303674383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1762919751002039623440341 41318431664110303674383)
              ·
                rfl

theorem cell19_407366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 7].length) (baseStart_407366 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407366 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407366 prefixEnd_407366 := by exact prefixLift 407366
  have htrace : WordTrace (prefixWord ++ tailWord_407366) baseStart_407366 baseEnd_407366 := by
    simpa [prefixWord, tailWord_407366, baseEnd_407366] using wordTrace_append hprefix tailTrace_407366
  have hstable : (prefixWord ++ tailWord_407366).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407366).length < 2 ^ (prefixWord ++ tailWord_407366).sum := by decide
  have hdescent : baseEnd_407366 < baseStart_407366 := by decide
  rcases family_descends (prefixWord ++ tailWord_407366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407406 : List Nat := [4, 1, 2, 3, 1, 1, 2, 5]
def baseStart_407406 : Nat := 118140960795 + 407406 * 2 ^ 59
def prefixEnd_407406 : Nat := 4983230072969 + 3 ^ 40 * 407406 * 2
def baseEnd_407406 : Nat := 123967466385622670134151

theorem tailTrace_407406 : CollatzResearch.WordTrace tailWord_407406 prefixEnd_407406 123967466385622670134151 := by
  unfold tailWord_407406
  simp only [CollatzResearch.WordTrace]
  refine ⟨1857414695255639531301259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9906211708030077500273381 1857414695255639531301259)
  ·
    refine ⟨2786122042883459296951889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1857414695255639531301259 2786122042883459296951889)
    ·
      refine ⟨2089591532162594472713917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2786122042883459296951889 2089591532162594472713917)
      ·
        refine ⟨783596824560972927267719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2089591532162594472713917 783596824560972927267719)
        ·
          refine ⟨1175395236841459390901579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783596824560972927267719 1175395236841459390901579)
          ·
            refine ⟨1763092855262189086352369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1175395236841459390901579 1763092855262189086352369)
            ·
              refine ⟨1322319641446641814764277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1763092855262189086352369 1322319641446641814764277)
              ·
                refine ⟨123967466385622670134151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1322319641446641814764277 123967466385622670134151)
                ·
                  rfl

theorem cell19_407406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_407406 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407406 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407406 prefixEnd_407406 := by exact prefixLift 407406
  have htrace : WordTrace (prefixWord ++ tailWord_407406) baseStart_407406 baseEnd_407406 := by
    simpa [prefixWord, tailWord_407406, baseEnd_407406] using wordTrace_append hprefix tailTrace_407406
  have hstable : (prefixWord ++ tailWord_407406).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407406).length < 2 ^ (prefixWord ++ tailWord_407406).sum := by decide
  have hdescent : baseEnd_407406 < baseStart_407406 := by decide
  rcases family_descends (prefixWord ++ tailWord_407406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407425 : List Nat := [1, 2, 4, 4, 1, 7]
def baseStart_407425 : Nat := 118140960795 + 407425 * 2 ^ 59
def prefixEnd_407425 : Nat := 4983230072969 + 3 ^ 40 * 407425 * 2
def baseEnd_407425 : Nat := 13774805310826250634653

theorem tailTrace_407425 : CollatzResearch.WordTrace tailWord_407425 prefixEnd_407425 13774805310826250634653 := by
  unfold tailWord_407425
  simp only [CollatzResearch.WordTrace]
  refine ⟨14860010548976282495351729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9906673699317521663567819 14860010548976282495351729)
  ·
    refine ⟨11145007911732211871513797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14860010548976282495351729 11145007911732211871513797)
    ·
      refine ⟨2089688983449789725908837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11145007911732211871513797 2089688983449789725908837)
      ·
        refine ⟨391816684396835573607907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2089688983449789725908837 391816684396835573607907)
        ·
          refine ⟨587725026595253360411861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391816684396835573607907 587725026595253360411861)
          ·
            refine ⟨13774805310826250634653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 587725026595253360411861 13774805310826250634653)
            ·
              rfl

theorem cell19_407425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 7].length) (baseStart_407425 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407425 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407425 prefixEnd_407425 := by exact prefixLift 407425
  have htrace : WordTrace (prefixWord ++ tailWord_407425) baseStart_407425 baseEnd_407425 := by
    simpa [prefixWord, tailWord_407425, baseEnd_407425] using wordTrace_append hprefix tailTrace_407425
  have hstable : (prefixWord ++ tailWord_407425).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407425).length < 2 ^ (prefixWord ++ tailWord_407425).sum := by decide
  have hdescent : baseEnd_407425 < baseStart_407425 := by decide
  rcases family_descends (prefixWord ++ tailWord_407425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407442 : List Nat := [3, 2, 3, 2, 1, 3, 1, 4]
def baseStart_407442 : Nat := 118140960795 + 407442 * 2 ^ 59
def prefixEnd_407442 : Nat := 4983230072969 + 3 ^ 40 * 407442 * 2
def baseEnd_407442 : Nat := 123978420639585253334053

theorem tailTrace_407442 : CollatzResearch.WordTrace tailWord_407442 prefixEnd_407442 123978420639585253334053 := by
  unfold tailWord_407442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3715157647478673599680145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9907087059943129599147053 3715157647478673599680145)
  ·
    refine ⟨2786368235609005199760109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3715157647478673599680145 2786368235609005199760109)
    ·
      refine ⟨1044888088353376949910041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2786368235609005199760109 1044888088353376949910041)
      ·
        refine ⟨783666066265032712432531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1044888088353376949910041 783666066265032712432531)
        ·
          refine ⟨1175499099397549068648797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 783666066265032712432531 1175499099397549068648797)
          ·
            refine ⟨440812162274080900743299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1175499099397549068648797 440812162274080900743299)
            ·
              refine ⟨661218243411121351114949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 440812162274080900743299 661218243411121351114949)
              ·
                refine ⟨123978420639585253334053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 661218243411121351114949 123978420639585253334053)
                ·
                  rfl

theorem cell19_407442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_407442 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407442 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407442 prefixEnd_407442 := by exact prefixLift 407442
  have htrace : WordTrace (prefixWord ++ tailWord_407442) baseStart_407442 baseEnd_407442 := by
    simpa [prefixWord, tailWord_407442, baseEnd_407442] using wordTrace_append hprefix tailTrace_407442
  have hstable : (prefixWord ++ tailWord_407442).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407442).length < 2 ^ (prefixWord ++ tailWord_407442).sum := by decide
  have hdescent : baseEnd_407442 < baseStart_407442 := by decide
  rcases family_descends (prefixWord ++ tailWord_407442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407444 : List Nat := [2, 4, 2, 1, 1, 2, 3, 4]
def baseStart_407444 : Nat := 118140960795 + 407444 * 2 ^ 59
def prefixEnd_407444 : Nat := 4983230072969 + 3 ^ 40 * 407444 * 2
def baseEnd_407444 : Nat := 123979029209249841289603

theorem tailTrace_407444 : CollatzResearch.WordTrace tailWord_407444 prefixEnd_407444 123979029209249841289603 := by
  unfold tailWord_407444
  simp only [CollatzResearch.WordTrace]
  refine ⟨7430351767953724370146693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9907135690604965826862257 7430351767953724370146693)
  ·
    refine ⟨1393190956491323319402505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7430351767953724370146693 1393190956491323319402505)
    ·
      refine ⟨1044893217368492489551879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1393190956491323319402505 1044893217368492489551879)
      ·
        refine ⟨1567339826052738734327819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1044893217368492489551879 1567339826052738734327819)
        ·
          refine ⟨2351009739079108101491729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567339826052738734327819 2351009739079108101491729)
          ·
            refine ⟨1763257304309331076118797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2351009739079108101491729 1763257304309331076118797)
            ·
              refine ⟨661221489115999153544549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1763257304309331076118797 661221489115999153544549)
              ·
                refine ⟨123979029209249841289603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 661221489115999153544549 123979029209249841289603)
                ·
                  rfl

theorem cell19_407444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_407444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407444 prefixEnd_407444 := by exact prefixLift 407444
  have htrace : WordTrace (prefixWord ++ tailWord_407444) baseStart_407444 baseEnd_407444 := by
    simpa [prefixWord, tailWord_407444, baseEnd_407444] using wordTrace_append hprefix tailTrace_407444
  have hstable : (prefixWord ++ tailWord_407444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407444).length < 2 ^ (prefixWord ++ tailWord_407444).sum := by decide
  have hdescent : baseEnd_407444 < baseStart_407444 := by decide
  rcases family_descends (prefixWord ++ tailWord_407444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407516 : List Nat := [2, 2, 6, 1, 1, 1, 1, 5]
def baseStart_407516 : Nat := 118140960795 + 407516 * 2 ^ 59
def prefixEnd_407516 : Nat := 4983230072969 + 3 ^ 40 * 407516 * 2
def baseEnd_407516 : Nat := 124000937717175007689407

theorem tailTrace_407516 : CollatzResearch.WordTrace tailWord_407516 prefixEnd_407516 124000937717175007689407 := by
  unfold tailWord_407516
  simp only [CollatzResearch.WordTrace]
  refine ⟨7431664795823302518457201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9908886394431070024609601 7431664795823302518457201)
  ·
    refine ⟨5573748596867476888842901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7431664795823302518457201 5573748596867476888842901)
    ·
      refine ⟨261269465478162979164511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5573748596867476888842901 261269465478162979164511)
      ·
        refine ⟨391904198217244468746767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261269465478162979164511 391904198217244468746767)
        ·
          refine ⟨587856297325866703120151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391904198217244468746767 587856297325866703120151)
          ·
            refine ⟨881784445988800054680227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587856297325866703120151 881784445988800054680227)
            ·
              refine ⟨1322676668983200082020341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 881784445988800054680227 1322676668983200082020341)
              ·
                refine ⟨124000937717175007689407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1322676668983200082020341 124000937717175007689407)
                ·
                  rfl

theorem cell19_407516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_407516 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407516 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407516 prefixEnd_407516 := by exact prefixLift 407516
  have htrace : WordTrace (prefixWord ++ tailWord_407516) baseStart_407516 baseEnd_407516 := by
    simpa [prefixWord, tailWord_407516, baseEnd_407516] using wordTrace_append hprefix tailTrace_407516
  have hstable : (prefixWord ++ tailWord_407516).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407516).length < 2 ^ (prefixWord ++ tailWord_407516).sum := by decide
  have hdescent : baseEnd_407516 < baseStart_407516 := by decide
  rcases family_descends (prefixWord ++ tailWord_407516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407556 : List Nat := [2, 3, 2, 4, 1, 1, 2, 4]
def baseStart_407556 : Nat := 118140960795 + 407556 * 2 ^ 59
def prefixEnd_407556 : Nat := 4983230072969 + 3 ^ 40 * 407556 * 2
def baseEnd_407556 : Nat := 124013109110466766800409

theorem tailTrace_407556 : CollatzResearch.WordTrace tailWord_407556 prefixEnd_407556 124013109110466766800409 := by
  unfold tailWord_407556
  simp only [CollatzResearch.WordTrace]
  refine ⟨7432394255750845934185261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9909859007667794578913681 7432394255750845934185261)
  ·
    refine ⟨2787147845906567225319473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7432394255750845934185261 2787147845906567225319473)
    ·
      refine ⟨2090360884429925418989605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2787147845906567225319473 2090360884429925418989605)
      ·
        refine ⟨391942665830611016060551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2090360884429925418989605 391942665830611016060551)
        ·
          refine ⟨587913998745916524090827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 391942665830611016060551 587913998745916524090827)
          ·
            refine ⟨881870998118874786136241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 587913998745916524090827 881870998118874786136241)
            ·
              refine ⟨661403248589156089602181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 881870998118874786136241 661403248589156089602181)
              ·
                refine ⟨124013109110466766800409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 661403248589156089602181 124013109110466766800409)
                ·
                  rfl

theorem cell19_407556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 4].length) (baseStart_407556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407556 prefixEnd_407556 := by exact prefixLift 407556
  have htrace : WordTrace (prefixWord ++ tailWord_407556) baseStart_407556 baseEnd_407556 := by
    simpa [prefixWord, tailWord_407556, baseEnd_407556] using wordTrace_append hprefix tailTrace_407556
  have hstable : (prefixWord ++ tailWord_407556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407556).length < 2 ^ (prefixWord ++ tailWord_407556).sum := by decide
  have hdescent : baseEnd_407556 < baseStart_407556 := by decide
  rcases family_descends (prefixWord ++ tailWord_407556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407560 : List Nat := [2, 1, 3, 2, 1, 2, 4, 4]
def baseStart_407560 : Nat := 118140960795 + 407560 * 2 ^ 59
def prefixEnd_407560 : Nat := 4983230072969 + 3 ^ 40 * 407560 * 2
def baseEnd_407560 : Nat := 124014326249795942711509

theorem tailTrace_407560 : CollatzResearch.WordTrace tailWord_407560 prefixEnd_407560 124014326249795942711509 := by
  unfold tailWord_407560
  simp only [CollatzResearch.WordTrace]
  refine ⟨7432467201743600275758067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9909956268991467034344089 7432467201743600275758067)
  ·
    refine ⟨11148700802615400413637101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7432467201743600275758067 11148700802615400413637101)
    ·
      refine ⟨4180762800980775155113913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11148700802615400413637101 4180762800980775155113913)
      ·
        refine ⟨3135572100735581366335435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4180762800980775155113913 3135572100735581366335435)
        ·
          refine ⟨4703358151103372049503153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3135572100735581366335435 4703358151103372049503153)
          ·
            refine ⟨3527518613327529037127365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4703358151103372049503153 3527518613327529037127365)
            ·
              refine ⟨661409739998911694461381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3527518613327529037127365 661409739998911694461381)
              ·
                refine ⟨124014326249795942711509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 661409739998911694461381 124014326249795942711509)
                ·
                  rfl

theorem cell19_407560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_407560 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407560 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407560 prefixEnd_407560 := by exact prefixLift 407560
  have htrace : WordTrace (prefixWord ++ tailWord_407560) baseStart_407560 baseEnd_407560 := by
    simpa [prefixWord, tailWord_407560, baseEnd_407560] using wordTrace_append hprefix tailTrace_407560
  have hstable : (prefixWord ++ tailWord_407560).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407560).length < 2 ^ (prefixWord ++ tailWord_407560).sum := by decide
  have hdescent : baseEnd_407560 < baseStart_407560 := by decide
  rcases family_descends (prefixWord ++ tailWord_407560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407598 : List Nat := [4, 1, 3, 1, 1, 9]
def baseStart_407598 : Nat := 118140960795 + 407598 * 2 ^ 59
def prefixEnd_407598 : Nat := 4983230072969 + 3 ^ 40 * 407598 * 2
def baseEnd_407598 : Nat := 13780654341491457096329

theorem tailTrace_407598 : CollatzResearch.WordTrace tailWord_407598 prefixEnd_407598 13780654341491457096329 := by
  unfold tailWord_407598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1858290047168691630174931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9910880251566355360932965 1858290047168691630174931)
  ·
    refine ⟨2787435070753037445262397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1858290047168691630174931 2787435070753037445262397)
    ·
      refine ⟨1045288151532389041973399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2787435070753037445262397 1045288151532389041973399)
      ·
        refine ⟨1567932227298583562960099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045288151532389041973399 1567932227298583562960099)
        ·
          refine ⟨2351898340947875344440149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1567932227298583562960099 2351898340947875344440149)
          ·
            refine ⟨13780654341491457096329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2351898340947875344440149 13780654341491457096329)
            ·
              rfl

theorem cell19_407598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 9].length) (baseStart_407598 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407598 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407598 prefixEnd_407598 := by exact prefixLift 407598
  have htrace : WordTrace (prefixWord ++ tailWord_407598) baseStart_407598 baseEnd_407598 := by
    simpa [prefixWord, tailWord_407598, baseEnd_407598] using wordTrace_append hprefix tailTrace_407598
  have hstable : (prefixWord ++ tailWord_407598).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407598).length < 2 ^ (prefixWord ++ tailWord_407598).sum := by decide
  have hdescent : baseEnd_407598 < baseStart_407598 := by decide
  rcases family_descends (prefixWord ++ tailWord_407598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407600 : List Nat := [2, 1, 1, 1, 2, 12]
def baseStart_407600 : Nat := 118140960795 + 407600 * 2 ^ 59
def prefixEnd_407600 : Nat := 4983230072969 + 3 ^ 40 * 407600 * 2
def baseEnd_407600 : Nat := 13780721960343077980279

theorem tailTrace_407600 : CollatzResearch.WordTrace tailWord_407600 prefixEnd_407600 13780721960343077980279 := by
  unfold tailWord_407600
  simp only [CollatzResearch.WordTrace]
  refine ⟨7433196661671143691486127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9910928882228191588648169 7433196661671143691486127)
  ·
    refine ⟨11149794992506715537229191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7433196661671143691486127 11149794992506715537229191)
    ·
      refine ⟨16724692488760073305843787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11149794992506715537229191 16724692488760073305843787)
      ·
        refine ⟨25087038733140109958765681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16724692488760073305843787 25087038733140109958765681)
        ·
          refine ⟨18815279049855082469074261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25087038733140109958765681 18815279049855082469074261)
          ·
            refine ⟨13780721960343077980279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 18815279049855082469074261 13780721960343077980279)
            ·
              rfl

theorem cell19_407600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 12].length) (baseStart_407600 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407600 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407600 prefixEnd_407600 := by exact prefixLift 407600
  have htrace : WordTrace (prefixWord ++ tailWord_407600) baseStart_407600 baseEnd_407600 := by
    simpa [prefixWord, tailWord_407600, baseEnd_407600] using wordTrace_append hprefix tailTrace_407600
  have hstable : (prefixWord ++ tailWord_407600).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407600).length < 2 ^ (prefixWord ++ tailWord_407600).sum := by decide
  have hdescent : baseEnd_407600 < baseStart_407600 := by decide
  rcases family_descends (prefixWord ++ tailWord_407600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407619 : List Nat := [1, 1, 1, 3, 1, 2, 2, 8]
def baseStart_407619 : Nat := 118140960795 + 407619 * 2 ^ 59
def prefixEnd_407619 : Nat := 4983230072969 + 3 ^ 40 * 407619 * 2
def baseEnd_407619 : Nat := 124032279054901287400237

theorem tailTrace_407619 : CollatzResearch.WordTrace tailWord_407619 prefixEnd_407619 124032279054901287400237 := by
  unfold tailWord_407619
  simp only [CollatzResearch.WordTrace]
  refine ⟨14867086310273453627913911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9911390873515635751942607 14867086310273453627913911)
  ·
    refine ⟨22300629465410180441870867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14867086310273453627913911 22300629465410180441870867)
    ·
      refine ⟨33450944198115270662806301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22300629465410180441870867 33450944198115270662806301)
      ·
        refine ⟨12544104074293226498552363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33450944198115270662806301 12544104074293226498552363)
        ·
          refine ⟨18816156111439839747828545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12544104074293226498552363 18816156111439839747828545)
          ·
            refine ⟨14112117083579879810871409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18816156111439839747828545 14112117083579879810871409)
            ·
              refine ⟨10584087812684909858153557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14112117083579879810871409 10584087812684909858153557)
              ·
                refine ⟨124032279054901287400237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10584087812684909858153557 124032279054901287400237)
                ·
                  rfl

theorem cell19_407619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_407619 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407619 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407619 prefixEnd_407619 := by exact prefixLift 407619
  have htrace : WordTrace (prefixWord ++ tailWord_407619) baseStart_407619 baseEnd_407619 := by
    simpa [prefixWord, tailWord_407619, baseEnd_407619] using wordTrace_append hprefix tailTrace_407619
  have hstable : (prefixWord ++ tailWord_407619).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407619).length < 2 ^ (prefixWord ++ tailWord_407619).sum := by decide
  have hdescent : baseEnd_407619 < baseStart_407619 := by decide
  rcases family_descends (prefixWord ++ tailWord_407619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407657 : List Nat := [1, 2, 1, 1, 1, 5, 8]
def baseStart_407657 : Nat := 118140960795 + 407657 * 2 ^ 59
def prefixEnd_407657 : Nat := 4983230072969 + 3 ^ 40 * 407657 * 2
def baseEnd_407657 : Nat := 41347947292842819518563

theorem tailTrace_407657 : CollatzResearch.WordTrace tailWord_407657 prefixEnd_407657 41347947292842819518563 := by
  unfold tailWord_407657
  simp only [CollatzResearch.WordTrace]
  refine ⟨14868472284135786117797225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9912314856090524078531483 14868472284135786117797225)
  ·
    refine ⟨11151354213101839588347919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14868472284135786117797225 11151354213101839588347919)
    ·
      refine ⟨16727031319652759382521879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11151354213101839588347919 16727031319652759382521879)
      ·
        refine ⟨25090546979479139073782819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16727031319652759382521879 25090546979479139073782819)
        ·
          refine ⟨37635820469218708610674229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25090546979479139073782819 37635820469218708610674229)
          ·
            refine ⟨3528358168989253932250709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37635820469218708610674229 3528358168989253932250709)
            ·
              refine ⟨41347947292842819518563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3528358168989253932250709 41347947292842819518563)
              ·
                rfl

theorem cell19_407657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 8].length) (baseStart_407657 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407657 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407657 prefixEnd_407657 := by exact prefixLift 407657
  have htrace : WordTrace (prefixWord ++ tailWord_407657) baseStart_407657 baseEnd_407657 := by
    simpa [prefixWord, tailWord_407657, baseEnd_407657] using wordTrace_append hprefix tailTrace_407657
  have hstable : (prefixWord ++ tailWord_407657).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407657).length < 2 ^ (prefixWord ++ tailWord_407657).sum := by decide
  have hdescent : baseEnd_407657 < baseStart_407657 := by decide
  rcases family_descends (prefixWord ++ tailWord_407657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407702 : List Nat := [5, 3, 2, 1, 2, 1, 5]
def baseStart_407702 : Nat := 118140960795 + 407702 * 2 ^ 59
def prefixEnd_407702 : Nat := 4983230072969 + 3 ^ 40 * 407702 * 2
def baseEnd_407702 : Nat := 41352511565327229185189

theorem tailTrace_407702 : CollatzResearch.WordTrace tailWord_407702 prefixEnd_407702 41352511565327229185189 := by
  unfold tailWord_407702
  simp only [CollatzResearch.WordTrace]
  refine ⟨929382098060797425199085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9913409045981839202123573 929382098060797425199085)
  ·
    refine ⟨348518286772799034449657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 929382098060797425199085 348518286772799034449657)
    ·
      refine ⟨261388715079599275837243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 348518286772799034449657 261388715079599275837243)
      ·
        refine ⟨392083072619398913755865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261388715079599275837243 392083072619398913755865)
        ·
          refine ⟨294062304464549185316899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 392083072619398913755865 294062304464549185316899)
          ·
            refine ⟨441093456696823777975349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294062304464549185316899 441093456696823777975349)
            ·
              refine ⟨41352511565327229185189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 441093456696823777975349 41352511565327229185189)
              ·
                rfl

theorem cell19_407702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 5].length) (baseStart_407702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407702 prefixEnd_407702 := by exact prefixLift 407702
  have htrace : WordTrace (prefixWord ++ tailWord_407702) baseStart_407702 baseEnd_407702 := by
    simpa [prefixWord, tailWord_407702, baseEnd_407702] using wordTrace_append hprefix tailTrace_407702
  have hstable : (prefixWord ++ tailWord_407702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407702).length < 2 ^ (prefixWord ++ tailWord_407702).sum := by decide
  have hdescent : baseEnd_407702 < baseStart_407702 := by decide
  rcases family_descends (prefixWord ++ tailWord_407702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407712 : List Nat := [2, 1, 1, 4, 2, 4, 5]
def baseStart_407712 : Nat := 118140960795 + 407712 * 2 ^ 59
def prefixEnd_407712 : Nat := 4983230072969 + 3 ^ 40 * 407712 * 2
def baseEnd_407712 : Nat := 41353525848101542444439

theorem tailTrace_407712 : CollatzResearch.WordTrace tailWord_407712 prefixEnd_407712 41353525848101542444439 := by
  unfold tailWord_407712
  simp only [CollatzResearch.WordTrace]
  refine ⟨7435239149468265255524695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9913652199291020340699593 7435239149468265255524695)
  ·
    refine ⟨11152858724202397883287043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7435239149468265255524695 11152858724202397883287043)
    ·
      refine ⟨16729288086303596824930565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11152858724202397883287043 16729288086303596824930565)
      ·
        refine ⟨3136741516181924404674481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16729288086303596824930565 3136741516181924404674481)
        ·
          refine ⟨2352556137136443303505861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3136741516181924404674481 2352556137136443303505861)
          ·
            refine ⟨441104275713083119407349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2352556137136443303505861 441104275713083119407349)
            ·
              refine ⟨41353525848101542444439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 441104275713083119407349 41353525848101542444439)
              ·
                rfl

theorem cell19_407712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 4, 5].length) (baseStart_407712 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407712 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407712 prefixEnd_407712 := by exact prefixLift 407712
  have htrace : WordTrace (prefixWord ++ tailWord_407712) baseStart_407712 baseEnd_407712 := by
    simpa [prefixWord, tailWord_407712, baseEnd_407712] using wordTrace_append hprefix tailTrace_407712
  have hstable : (prefixWord ++ tailWord_407712).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407712).length < 2 ^ (prefixWord ++ tailWord_407712).sum := by decide
  have hdescent : baseEnd_407712 < baseStart_407712 := by decide
  rcases family_descends (prefixWord ++ tailWord_407712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407729 : List Nat := [1, 2, 2, 5, 2, 1, 2, 4]
def baseStart_407729 : Nat := 118140960795 + 407729 * 2 ^ 59
def prefixEnd_407729 : Nat := 4983230072969 + 3 ^ 40 * 407729 * 2
def baseEnd_407729 : Nat := 124065750386453624955493

theorem tailTrace_407729 : CollatzResearch.WordTrace tailWord_407729 prefixEnd_407729 124065750386453624955493 := by
  unfold tailWord_407729
  simp only [CollatzResearch.WordTrace]
  refine ⟨14871098339874942414418241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9914065559916628276278827 14871098339874942414418241)
  ·
    refine ⟨11153323754906206810813681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14871098339874942414418241 11153323754906206810813681)
    ·
      refine ⟨8364992816179655108110261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11153323754906206810813681 8364992816179655108110261)
      ·
        refine ⟨784218076516842666385337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8364992816179655108110261 784218076516842666385337)
        ·
          refine ⟨588163557387631999789003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784218076516842666385337 588163557387631999789003)
          ·
            refine ⟨882245336081447999683505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588163557387631999789003 882245336081447999683505)
            ·
              refine ⟨661684002061085999762629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 882245336081447999683505 661684002061085999762629)
              ·
                refine ⟨124065750386453624955493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 661684002061085999762629 124065750386453624955493)
                ·
                  rfl

theorem cell19_407729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 2, 4].length) (baseStart_407729 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407729 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407729 prefixEnd_407729 := by exact prefixLift 407729
  have htrace : WordTrace (prefixWord ++ tailWord_407729) baseStart_407729 baseEnd_407729 := by
    simpa [prefixWord, tailWord_407729, baseEnd_407729] using wordTrace_append hprefix tailTrace_407729
  have hstable : (prefixWord ++ tailWord_407729).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407729).length < 2 ^ (prefixWord ++ tailWord_407729).sum := by decide
  have hdescent : baseEnd_407729 < baseStart_407729 := by decide
  rcases family_descends (prefixWord ++ tailWord_407729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407746 : List Nat := [3, 5, 1, 1, 1, 1, 2, 5]
def baseStart_407746 : Nat := 118140960795 + 407746 * 2 ^ 59
def prefixEnd_407746 : Nat := 4983230072969 + 3 ^ 40 * 407746 * 2
def baseEnd_407746 : Nat := 124070923228602622577669

theorem tailTrace_407746 : CollatzResearch.WordTrace tailWord_407746 prefixEnd_407746 124070923228602622577669 := by
  unfold tailWord_407746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3717929595203338579446773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9914478920542236211858061 3717929595203338579446773)
  ·
    refine ⟨348555899550312991823135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3717929595203338579446773 348555899550312991823135)
    ·
      refine ⟨522833849325469487734703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 348555899550312991823135 522833849325469487734703)
      ·
        refine ⟨784250773988204231602055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 522833849325469487734703 784250773988204231602055)
        ·
          refine ⟨1176376160982306347403083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 784250773988204231602055 1176376160982306347403083)
          ·
            refine ⟨1764564241473459521104625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1176376160982306347403083 1764564241473459521104625)
            ·
              refine ⟨1323423181105094640828469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1764564241473459521104625 1323423181105094640828469)
              ·
                refine ⟨124070923228602622577669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1323423181105094640828469 124070923228602622577669)
                ·
                  rfl

theorem cell19_407746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 5].length) (baseStart_407746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407746 prefixEnd_407746 := by exact prefixLift 407746
  have htrace : WordTrace (prefixWord ++ tailWord_407746) baseStart_407746 baseEnd_407746 := by
    simpa [prefixWord, tailWord_407746, baseEnd_407746] using wordTrace_append hprefix tailTrace_407746
  have hstable : (prefixWord ++ tailWord_407746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407746).length < 2 ^ (prefixWord ++ tailWord_407746).sum := by decide
  have hdescent : baseEnd_407746 < baseStart_407746 := by decide
  rcases family_descends (prefixWord ++ tailWord_407746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407807 : List Nat := [1, 1, 2, 2, 1, 4, 5, 3]
def baseStart_407807 : Nat := 118140960795 + 407807 * 2 ^ 59
def prefixEnd_407807 : Nat := 4983230072969 + 3 ^ 40 * 407807 * 2
def baseEnd_407807 : Nat := 124089484603372555221947

theorem tailTrace_407807 : CollatzResearch.WordTrace tailWord_407807 prefixEnd_407807 124089484603372555221947 := by
  unfold tailWord_407807
  simp only [CollatzResearch.WordTrace]
  refine ⟨14873943233592361735757675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9915962155728241157171783 14873943233592361735757675)
  ·
    refine ⟨22310914850388542603636513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14873943233592361735757675 22310914850388542603636513)
    ·
      refine ⟨16733186137791406952727385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22310914850388542603636513 16733186137791406952727385)
      ·
        refine ⟨12549889603343555214545539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16733186137791406952727385 12549889603343555214545539)
        ·
          refine ⟨18824834405015332821818309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12549889603343555214545539 18824834405015332821818309)
          ·
            refine ⟨3529656450940374904090933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18824834405015332821818309 3529656450940374904090933)
            ·
              refine ⟨330905292275660147258525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3529656450940374904090933 330905292275660147258525)
              ·
                refine ⟨124089484603372555221947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330905292275660147258525 124089484603372555221947)
                ·
                  rfl

theorem cell19_407807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 5, 3].length) (baseStart_407807 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407807 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407807 prefixEnd_407807 := by exact prefixLift 407807
  have htrace : WordTrace (prefixWord ++ tailWord_407807) baseStart_407807 baseEnd_407807 := by
    simpa [prefixWord, tailWord_407807, baseEnd_407807] using wordTrace_append hprefix tailTrace_407807
  have hstable : (prefixWord ++ tailWord_407807).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407807).length < 2 ^ (prefixWord ++ tailWord_407807).sum := by decide
  have hdescent : baseEnd_407807 < baseStart_407807 := by decide
  rcases family_descends (prefixWord ++ tailWord_407807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407860 : List Nat := [2, 5, 1, 1, 1, 4, 2, 3]
def baseStart_407860 : Nat := 118140960795 + 407860 * 2 ^ 59
def prefixEnd_407860 : Nat := 4983230072969 + 3 ^ 40 * 407860 * 2
def baseEnd_407860 : Nat := 124105611699484136044025

theorem tailTrace_407860 : CollatzResearch.WordTrace tailWord_407860 prefixEnd_407860 124105611699484136044025 := by
  unfold tailWord_407860
  simp only [CollatzResearch.WordTrace]
  refine ⟨7437938151200175893718517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9917250868266901191624689 7437938151200175893718517)
  ·
    refine ⟨697306701675016490036111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7437938151200175893718517 697306701675016490036111)
    ·
      refine ⟨1045960052512524735054167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 697306701675016490036111 1045960052512524735054167)
      ·
        refine ⟨1568940078768787102581251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1045960052512524735054167 1568940078768787102581251)
        ·
          refine ⟨2353410118153180653871877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1568940078768787102581251 2353410118153180653871877)
          ·
            refine ⟨441264397153721372600977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2353410118153180653871877 441264397153721372600977)
            ·
              refine ⟨330948297865291029450733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441264397153721372600977 330948297865291029450733)
              ·
                refine ⟨124105611699484136044025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330948297865291029450733 124105611699484136044025)
                ·
                  rfl

theorem cell19_407860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 4, 2, 3].length) (baseStart_407860 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407860 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407860 prefixEnd_407860 := by exact prefixLift 407860
  have htrace : WordTrace (prefixWord ++ tailWord_407860) baseStart_407860 baseEnd_407860 := by
    simpa [prefixWord, tailWord_407860, baseEnd_407860] using wordTrace_append hprefix tailTrace_407860
  have hstable : (prefixWord ++ tailWord_407860).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407860).length < 2 ^ (prefixWord ++ tailWord_407860).sum := by decide
  have hdescent : baseEnd_407860 < baseStart_407860 := by decide
  rcases family_descends (prefixWord ++ tailWord_407860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407864 : List Nat := [2, 1, 2, 1, 3, 1, 6, 3]
def baseStart_407864 : Nat := 118140960795 + 407864 * 2 ^ 59
def prefixEnd_407864 : Nat := 4983230072969 + 3 ^ 40 * 407864 * 2
def baseEnd_407864 : Nat := 124106828838813311955125

theorem tailTrace_407864 : CollatzResearch.WordTrace tailWord_407864 prefixEnd_407864 124106828838813311955125 := by
  unfold tailWord_407864
  simp only [CollatzResearch.WordTrace]
  refine ⟨7438011097192930235291323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9917348129590573647055097 7438011097192930235291323)
  ·
    refine ⟨11157016645789395352936985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7438011097192930235291323 11157016645789395352936985)
    ·
      refine ⟨8367762484342046514702739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11157016645789395352936985 8367762484342046514702739)
      ·
        refine ⟨12551643726513069772054109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8367762484342046514702739 12551643726513069772054109)
        ·
          refine ⟨4706866397442401164520291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12551643726513069772054109 4706866397442401164520291)
          ·
            refine ⟨7060299596163601746780437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4706866397442401164520291 7060299596163601746780437)
            ·
              refine ⟨330951543570168831880333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7060299596163601746780437 330951543570168831880333)
              ·
                refine ⟨124106828838813311955125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 330951543570168831880333 124106828838813311955125)
                ·
                  rfl

theorem cell19_407864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 6, 3].length) (baseStart_407864 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407864 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407864 prefixEnd_407864 := by exact prefixLift 407864
  have htrace : WordTrace (prefixWord ++ tailWord_407864) baseStart_407864 baseEnd_407864 := by
    simpa [prefixWord, tailWord_407864, baseEnd_407864] using wordTrace_append hprefix tailTrace_407864
  have hstable : (prefixWord ++ tailWord_407864).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407864).length < 2 ^ (prefixWord ++ tailWord_407864).sum := by decide
  have hdescent : baseEnd_407864 < baseStart_407864 := by decide
  rcases family_descends (prefixWord ++ tailWord_407864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_407938 : List Nat := [3, 4, 2, 1, 2, 7]
def baseStart_407938 : Nat := 118140960795 + 407938 * 2 ^ 59
def prefixEnd_407938 : Nat := 4983230072969 + 3 ^ 40 * 407938 * 2
def baseEnd_407938 : Nat := 13792149546267007367831

theorem tailTrace_407938 : CollatzResearch.WordTrace tailWord_407938 prefixEnd_407938 13792149546267007367831 := by
  unfold tailWord_407938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3719680299029442777194117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9919147464078514072517645 3719680299029442777194117)
  ·
    refine ⟨697440056068020520723897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3719680299029442777194117 697440056068020520723897)
    ·
      refine ⟨523080042051015390542923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 697440056068020520723897 523080042051015390542923)
      ·
        refine ⟨784620063076523085814385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523080042051015390542923 784620063076523085814385)
        ·
          refine ⟨588465047307392314360789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 784620063076523085814385 588465047307392314360789)
          ·
            refine ⟨13792149546267007367831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 588465047307392314360789 13792149546267007367831)
            ·
              rfl

theorem cell19_407938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 7].length) (baseStart_407938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_407938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_407938 prefixEnd_407938 := by exact prefixLift 407938
  have htrace : WordTrace (prefixWord ++ tailWord_407938) baseStart_407938 baseEnd_407938 := by
    simpa [prefixWord, tailWord_407938, baseEnd_407938] using wordTrace_append hprefix tailTrace_407938
  have hstable : (prefixWord ++ tailWord_407938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_407938).length < 2 ^ (prefixWord ++ tailWord_407938).sum := by decide
  have hdescent : baseEnd_407938 < baseStart_407938 := by decide
  rcases family_descends (prefixWord ++ tailWord_407938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408035 : List Nat := [1, 1, 1, 6, 3, 1, 1, 5]
def baseStart_408035 : Nat := 118140960795 + 408035 * 2 ^ 59
def prefixEnd_408035 : Nat := 4983230072969 + 3 ^ 40 * 408035 * 2
def baseEnd_408035 : Nat := 124158861545135582154659

theorem tailTrace_408035 : CollatzResearch.WordTrace tailWord_408035 prefixEnd_408035 124158861545135582154659 := by
  unfold tailWord_408035
  simp only [CollatzResearch.WordTrace]
  refine ⟨14882259076766356675057559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9921506051177571116705039 14882259076766356675057559)
  ·
    refine ⟨22323388615149535012586339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14882259076766356675057559 22323388615149535012586339)
    ·
      refine ⟨33485082922724302518879509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22323388615149535012586339 33485082922724302518879509)
      ·
        refine ⟨1569613262002701680572477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 33485082922724302518879509 1569613262002701680572477)
        ·
          refine ⟨588604973251013130214679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1569613262002701680572477 588604973251013130214679)
          ·
            refine ⟨882907459876519695322019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588604973251013130214679 882907459876519695322019)
            ·
              refine ⟨1324361189814779542983029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 882907459876519695322019 1324361189814779542983029)
              ·
                refine ⟨124158861545135582154659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1324361189814779542983029 124158861545135582154659)
                ·
                  rfl

theorem cell19_408035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_408035 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408035 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408035 prefixEnd_408035 := by exact prefixLift 408035
  have htrace : WordTrace (prefixWord ++ tailWord_408035) baseStart_408035 baseEnd_408035 := by
    simpa [prefixWord, tailWord_408035, baseEnd_408035] using wordTrace_append hprefix tailTrace_408035
  have hstable : (prefixWord ++ tailWord_408035).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408035).length < 2 ^ (prefixWord ++ tailWord_408035).sum := by decide
  have hdescent : baseEnd_408035 < baseStart_408035 := by decide
  rcases family_descends (prefixWord ++ tailWord_408035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408075 : List Nat := [1, 1, 1, 1, 7, 1, 1, 6]
def baseStart_408075 : Nat := 118140960795 + 408075 * 2 ^ 59
def prefixEnd_408075 : Nat := 4983230072969 + 3 ^ 40 * 408075 * 2
def baseEnd_408075 : Nat := 124171032938427341265661

theorem tailTrace_408075 : CollatzResearch.WordTrace tailWord_408075 prefixEnd_408075 124171032938427341265661 := by
  unfold tailWord_408075
  simp only [CollatzResearch.WordTrace]
  refine ⟨14883717996621443506513679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9922478664414295671009119 14883717996621443506513679)
  ·
    refine ⟨22325576994932165259770519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14883717996621443506513679 22325576994932165259770519)
    ·
      refine ⟨33488365492398247889655779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22325576994932165259770519 33488365492398247889655779)
      ·
        refine ⟨50232548238597371834483669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33488365492398247889655779 50232548238597371834483669)
        ·
          refine ⟨1177325349342125902370711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 50232548238597371834483669 1177325349342125902370711)
          ·
            refine ⟨1765988024013188853556067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1177325349342125902370711 1765988024013188853556067)
            ·
              refine ⟨2648982036019783280334101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1765988024013188853556067 2648982036019783280334101)
              ·
                refine ⟨124171032938427341265661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2648982036019783280334101 124171032938427341265661)
                ·
                  rfl

theorem cell19_408075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_408075 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408075 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408075 prefixEnd_408075 := by exact prefixLift 408075
  have htrace : WordTrace (prefixWord ++ tailWord_408075) baseStart_408075 baseEnd_408075 := by
    simpa [prefixWord, tailWord_408075, baseEnd_408075] using wordTrace_append hprefix tailTrace_408075
  have hstable : (prefixWord ++ tailWord_408075).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408075).length < 2 ^ (prefixWord ++ tailWord_408075).sum := by decide
  have hdescent : baseEnd_408075 < baseStart_408075 := by decide
  rcases family_descends (prefixWord ++ tailWord_408075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408109 : List Nat := [1, 5, 4, 1, 8]
def baseStart_408109 : Nat := 118140960795 + 408109 * 2 ^ 59
def prefixEnd_408109 : Nat := 4983230072969 + 3 ^ 40 * 408109 * 2
def baseEnd_408109 : Nat := 4599310319360197648519

theorem tailTrace_408109 : CollatzResearch.WordTrace tailWord_408109 prefixEnd_408109 4599310319360197648519 := by
  unfold tailWord_408109
  simp only [CollatzResearch.WordTrace]
  refine ⟨14884958078498267313251381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9923305385665511542167587 14884958078498267313251381)
  ·
    refine ⟨1395464819859212560617317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14884958078498267313251381 1395464819859212560617317)
    ·
      refine ⟨261649653723602355115747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1395464819859212560617317 261649653723602355115747)
      ·
        refine ⟨392474480585403532673621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 261649653723602355115747 392474480585403532673621)
        ·
          refine ⟨4599310319360197648519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 392474480585403532673621 4599310319360197648519)
          ·
            rfl

theorem cell19_408109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 8].length) (baseStart_408109 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408109 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408109 prefixEnd_408109 := by exact prefixLift 408109
  have htrace : WordTrace (prefixWord ++ tailWord_408109) baseStart_408109 baseEnd_408109 := by
    simpa [prefixWord, tailWord_408109, baseEnd_408109] using wordTrace_append hprefix tailTrace_408109
  have hstable : (prefixWord ++ tailWord_408109).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408109).length < 2 ^ (prefixWord ++ tailWord_408109).sum := by decide
  have hdescent : baseEnd_408109 < baseStart_408109 := by decide
  rcases family_descends (prefixWord ++ tailWord_408109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408126 : List Nat := [4, 2, 1, 4, 1, 2, 1, 4]
def baseStart_408126 : Nat := 118140960795 + 408126 * 2 ^ 59
def prefixEnd_408126 : Nat := 4983230072969 + 3 ^ 40 * 408126 * 2
def baseEnd_408126 : Nat := 124186551464874334132189

theorem tailTrace_408126 : CollatzResearch.WordTrace tailWord_408126 prefixEnd_408126 124186551464874334132189 := by
  unfold tailWord_408126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1860697264929584902077529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9923718746291119477746821 1860697264929584902077529)
  ·
    refine ⟨1395522948697188676558147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1860697264929584902077529 1395522948697188676558147)
    ·
      refine ⟨2093284423045783014837221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1395522948697188676558147 2093284423045783014837221)
      ·
        refine ⟨392490829321084315281979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2093284423045783014837221 392490829321084315281979)
        ·
          refine ⟨588736243981626472922969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392490829321084315281979 588736243981626472922969)
          ·
            refine ⟨441552182986219854692227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588736243981626472922969 441552182986219854692227)
            ·
              refine ⟨662328274479329782038341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 441552182986219854692227 662328274479329782038341)
              ·
                refine ⟨124186551464874334132189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 662328274479329782038341 124186551464874334132189)
                ·
                  rfl

theorem cell19_408126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_408126 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408126 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408126 prefixEnd_408126 := by exact prefixLift 408126
  have htrace : WordTrace (prefixWord ++ tailWord_408126) baseStart_408126 baseEnd_408126 := by
    simpa [prefixWord, tailWord_408126, baseEnd_408126] using wordTrace_append hprefix tailTrace_408126
  have hstable : (prefixWord ++ tailWord_408126).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408126).length < 2 ^ (prefixWord ++ tailWord_408126).sum := by decide
  have hdescent : baseEnd_408126 < baseStart_408126 := by decide
  rcases family_descends (prefixWord ++ tailWord_408126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408168 : List Nat := [2, 1, 4, 3, 2, 1, 6]
def baseStart_408168 : Nat := 118140960795 + 408168 * 2 ^ 59
def prefixEnd_408168 : Nat := 4983230072969 + 3 ^ 40 * 408168 * 2
def baseEnd_408168 : Nat := 41399777142610227066247

theorem tailTrace_408168 : CollatzResearch.WordTrace tailWord_408168 prefixEnd_408168 41399777142610227066247 := by
  unfold tailWord_408168
  simp only [CollatzResearch.WordTrace]
  refine ⟨7443554992642260194824579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9924739990189680259766105 7443554992642260194824579)
  ·
    refine ⟨11165332488963390292236869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7443554992642260194824579 11165332488963390292236869)
    ·
      refine ⟨2093499841680635679794413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11165332488963390292236869 2093499841680635679794413)
      ·
        refine ⟨785062440630238379922905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2093499841680635679794413 785062440630238379922905)
        ·
          refine ⟨588796830472678784942179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 785062440630238379922905 588796830472678784942179)
          ·
            refine ⟨883195245709018177413269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 588796830472678784942179 883195245709018177413269)
            ·
              refine ⟨41399777142610227066247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 883195245709018177413269 41399777142610227066247)
              ·
                rfl

theorem cell19_408168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 6].length) (baseStart_408168 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408168 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408168 prefixEnd_408168 := by exact prefixLift 408168
  have htrace : WordTrace (prefixWord ++ tailWord_408168) baseStart_408168 baseEnd_408168 := by
    simpa [prefixWord, tailWord_408168, baseEnd_408168] using wordTrace_append hprefix tailTrace_408168
  have hstable : (prefixWord ++ tailWord_408168).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408168).length < 2 ^ (prefixWord ++ tailWord_408168).sum := by decide
  have hdescent : baseEnd_408168 < baseStart_408168 := by decide
  rcases family_descends (prefixWord ++ tailWord_408168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408170 : List Nat := [3, 1, 3, 2, 1, 1, 8]
def baseStart_408170 : Nat := 118140960795 + 408170 * 2 ^ 59
def prefixEnd_408170 : Nat := 4983230072969 + 3 ^ 40 * 408170 * 2
def baseEnd_408170 : Nat := 41399979999165089718097

theorem tailTrace_408170 : CollatzResearch.WordTrace tailWord_408170 prefixEnd_408170 41399979999165089718097 := by
  unfold tailWord_408170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3721795732819318682805491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9924788620851516487481309 3721795732819318682805491)
  ·
    refine ⟨5582693599228978024208237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3721795732819318682805491 5582693599228978024208237)
    ·
      refine ⟨2093510099710866759078089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5582693599228978024208237 2093510099710866759078089)
      ·
        refine ⟨1570132574783150069308567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2093510099710866759078089 1570132574783150069308567)
        ·
          refine ⟨2355198862174725103962851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570132574783150069308567 2355198862174725103962851)
          ·
            refine ⟨3532798293262087655944277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355198862174725103962851 3532798293262087655944277)
            ·
              refine ⟨41399979999165089718097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3532798293262087655944277 41399979999165089718097)
              ·
                rfl

theorem cell19_408170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 8].length) (baseStart_408170 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408170 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408170 prefixEnd_408170 := by exact prefixLift 408170
  have htrace : WordTrace (prefixWord ++ tailWord_408170) baseStart_408170 baseEnd_408170 := by
    simpa [prefixWord, tailWord_408170, baseEnd_408170] using wordTrace_append hprefix tailTrace_408170
  have hstable : (prefixWord ++ tailWord_408170).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408170).length < 2 ^ (prefixWord ++ tailWord_408170).sum := by decide
  have hdescent : baseEnd_408170 < baseStart_408170 := by decide
  rcases family_descends (prefixWord ++ tailWord_408170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408202 : List Nat := [3, 1, 2, 3, 4, 1, 2, 3]
def baseStart_408202 : Nat := 118140960795 + 408202 * 2 ^ 59
def prefixEnd_408202 : Nat := 4983230072969 + 3 ^ 40 * 408202 * 2
def baseEnd_408202 : Nat := 124209677112128676443093

theorem tailTrace_408202 : CollatzResearch.WordTrace tailWord_408202 prefixEnd_408202 124209677112128676443093 := by
  unfold tailWord_408202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3722087516790336049096715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9925566711440896130924573 3722087516790336049096715)
  ·
    refine ⟨5583131275185504073645073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3722087516790336049096715 5583131275185504073645073)
    ·
      refine ⟨4187348456389128055233805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5583131275185504073645073 4187348456389128055233805)
      ·
        refine ⟨1570255671145923020712677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4187348456389128055233805 1570255671145923020712677)
        ·
          refine ⟨294422938339860566383627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1570255671145923020712677 294422938339860566383627)
          ·
            refine ⟨441634407509790849575441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294422938339860566383627 441634407509790849575441)
            ·
              refine ⟨331225805632343137181581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 441634407509790849575441 331225805632343137181581)
              ·
                refine ⟨124209677112128676443093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331225805632343137181581 124209677112128676443093)
                ·
                  rfl

theorem cell19_408202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 2, 3].length) (baseStart_408202 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408202 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408202 prefixEnd_408202 := by exact prefixLift 408202
  have htrace : WordTrace (prefixWord ++ tailWord_408202) baseStart_408202 baseEnd_408202 := by
    simpa [prefixWord, tailWord_408202, baseEnd_408202] using wordTrace_append hprefix tailTrace_408202
  have hstable : (prefixWord ++ tailWord_408202).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408202).length < 2 ^ (prefixWord ++ tailWord_408202).sum := by decide
  have hdescent : baseEnd_408202 < baseStart_408202 := by decide
  rcases family_descends (prefixWord ++ tailWord_408202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408225 : List Nat := [1, 2, 3, 3, 3, 2, 5]
def baseStart_408225 : Nat := 118140960795 + 408225 * 2 ^ 59
def prefixEnd_408225 : Nat := 4983230072969 + 3 ^ 40 * 408225 * 2
def baseEnd_408225 : Nat := 41405558554423812643973

theorem tailTrace_408225 : CollatzResearch.WordTrace tailWord_408225 prefixEnd_408225 41405558554423812643973 := by
  unfold tailWord_408225
  simp only [CollatzResearch.WordTrace]
  refine ⟨14889188946078019124474129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9926125964052012749649419 14889188946078019124474129)
  ·
    refine ⟨11166891709558514343355597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14889188946078019124474129 11166891709558514343355597)
    ·
      refine ⟨4187584391084442878758349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11166891709558514343355597 4187584391084442878758349)
      ·
        refine ⟨1570344146656666079534381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4187584391084442878758349 1570344146656666079534381)
        ·
          refine ⟨588879054996249779825393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1570344146656666079534381 588879054996249779825393)
          ·
            refine ⟨441659291247187334869045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 588879054996249779825393 441659291247187334869045)
            ·
              refine ⟨41405558554423812643973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 441659291247187334869045 41405558554423812643973)
              ·
                rfl

theorem cell19_408225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 5].length) (baseStart_408225 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408225 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408225 prefixEnd_408225 := by exact prefixLift 408225
  have htrace : WordTrace (prefixWord ++ tailWord_408225) baseStart_408225 baseEnd_408225 := by
    simpa [prefixWord, tailWord_408225, baseEnd_408225] using wordTrace_append hprefix tailTrace_408225
  have hstable : (prefixWord ++ tailWord_408225).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408225).length < 2 ^ (prefixWord ++ tailWord_408225).sum := by decide
  have hdescent : baseEnd_408225 < baseStart_408225 := by decide
  rcases family_descends (prefixWord ++ tailWord_408225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408303 : List Nat := [1, 1, 2, 1, 5, 2, 3, 4]
def baseStart_408303 : Nat := 118140960795 + 408303 * 2 ^ 59
def prefixEnd_408303 : Nat := 4983230072969 + 3 ^ 40 * 408303 * 2
def baseEnd_408303 : Nat := 124240409880190368198373

theorem tailTrace_408303 : CollatzResearch.WordTrace tailWord_408303 prefixEnd_408303 124240409880190368198373 := by
  unfold tailWord_408303
  simp only [CollatzResearch.WordTrace]
  refine ⟨14892033839795438445813563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9928022559863625630542375 14892033839795438445813563)
  ·
    refine ⟨22338050759693157668720345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14892033839795438445813563 22338050759693157668720345)
    ·
      refine ⟨16753538069769868251540259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22338050759693157668720345 16753538069769868251540259)
      ·
        refine ⟨25130307104654802377310389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16753538069769868251540259 25130307104654802377310389)
        ·
          refine ⟨2355966291061387722872849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25130307104654802377310389 2355966291061387722872849)
          ·
            refine ⟨1766974718296040792154637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2355966291061387722872849 1766974718296040792154637)
            ·
              refine ⟨662615519361015297057989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1766974718296040792154637 662615519361015297057989)
              ·
                refine ⟨124240409880190368198373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 662615519361015297057989 124240409880190368198373)
                ·
                  rfl

theorem cell19_408303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_408303 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408303 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408303 prefixEnd_408303 := by exact prefixLift 408303
  have htrace : WordTrace (prefixWord ++ tailWord_408303) baseStart_408303 baseEnd_408303 := by
    simpa [prefixWord, tailWord_408303, baseEnd_408303] using wordTrace_append hprefix tailTrace_408303
  have hstable : (prefixWord ++ tailWord_408303).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408303).length < 2 ^ (prefixWord ++ tailWord_408303).sum := by decide
  have hdescent : baseEnd_408303 < baseStart_408303 := by decide
  rcases family_descends (prefixWord ++ tailWord_408303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408318 : List Nat := [4, 2, 2, 1, 2, 2, 3, 3]
def baseStart_408318 : Nat := 118140960795 + 408318 * 2 ^ 59
def prefixEnd_408318 : Nat := 4983230072969 + 3 ^ 40 * 408318 * 2
def baseEnd_408318 : Nat := 124244974152674777864999

theorem tailTrace_408318 : CollatzResearch.WordTrace tailWord_408318 prefixEnd_408318 124244974152674777864999 := by
  unfold tailWord_408318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1861572616842637000951201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9928387289827397338406405 1861572616842637000951201)
  ·
    refine ⟨1396179462631977750713401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1861572616842637000951201 1396179462631977750713401)
    ·
      refine ⟨1047134596973983313035051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1396179462631977750713401 1047134596973983313035051)
      ·
        refine ⟨1570701895460974969552577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1047134596973983313035051 1570701895460974969552577)
        ·
          refine ⟨1178026421595731227164433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1570701895460974969552577 1178026421595731227164433)
          ·
            refine ⟨883519816196798420373325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1178026421595731227164433 883519816196798420373325)
            ·
              refine ⟨331319931073799407639997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 883519816196798420373325 331319931073799407639997)
              ·
                refine ⟨124244974152674777864999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331319931073799407639997 124244974152674777864999)
                ·
                  rfl

theorem cell19_408318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_408318 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408318 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408318 prefixEnd_408318 := by exact prefixLift 408318
  have htrace : WordTrace (prefixWord ++ tailWord_408318) baseStart_408318 baseEnd_408318 := by
    simpa [prefixWord, tailWord_408318, baseEnd_408318] using wordTrace_append hprefix tailTrace_408318
  have hstable : (prefixWord ++ tailWord_408318).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408318).length < 2 ^ (prefixWord ++ tailWord_408318).sum := by decide
  have hdescent : baseEnd_408318 < baseStart_408318 := by decide
  rcases family_descends (prefixWord ++ tailWord_408318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408360 : List Nat := [2, 1, 5, 1, 1, 1, 2, 6]
def baseStart_408360 : Nat := 118140960795 + 408360 * 2 ^ 59
def prefixEnd_408360 : Nat := 4983230072969 + 3 ^ 40 * 408360 * 2
def baseEnd_408360 : Nat := 124257754115631124931551

theorem tailTrace_408360 : CollatzResearch.WordTrace tailWord_408360 prefixEnd_408360 124257754115631124931551 := by
  unfold tailWord_408360
  simp only [CollatzResearch.WordTrace]
  refine ⟨7447056400294468590319267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9929408533725958120425689 7447056400294468590319267)
  ·
    refine ⟨11170584600441702885478901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7447056400294468590319267 11170584600441702885478901)
    ·
      refine ⟨1047242306291409645513647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11170584600441702885478901 1047242306291409645513647)
      ·
        refine ⟨1570863459437114468270471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1047242306291409645513647 1570863459437114468270471)
        ·
          refine ⟨2356295189155671702405707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1570863459437114468270471 2356295189155671702405707)
          ·
            refine ⟨3534442783733507553608561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2356295189155671702405707 3534442783733507553608561)
            ·
              refine ⟨2650832087800130665206421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3534442783733507553608561 2650832087800130665206421)
              ·
                refine ⟨124257754115631124931551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2650832087800130665206421 124257754115631124931551)
                ·
                  rfl

theorem cell19_408360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_408360 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408360 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408360 prefixEnd_408360 := by exact prefixLift 408360
  have htrace : WordTrace (prefixWord ++ tailWord_408360) baseStart_408360 baseEnd_408360 := by
    simpa [prefixWord, tailWord_408360, baseEnd_408360] using wordTrace_append hprefix tailTrace_408360
  have hstable : (prefixWord ++ tailWord_408360).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408360).length < 2 ^ (prefixWord ++ tailWord_408360).sum := by decide
  have hdescent : baseEnd_408360 < baseStart_408360 := by decide
  rcases family_descends (prefixWord ++ tailWord_408360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408400 : List Nat := [2, 1, 1, 1, 1, 4, 9]
def baseStart_408400 : Nat := 118140960795 + 408400 * 2 ^ 59
def prefixEnd_408400 : Nat := 4983230072969 + 3 ^ 40 * 408400 * 2
def baseEnd_408400 : Nat := 41423308502974294680851

theorem tailTrace_408400 : CollatzResearch.WordTrace tailWord_408400 prefixEnd_408400 41423308502974294680851 := by
  unfold tailWord_408400
  simp only [CollatzResearch.WordTrace]
  refine ⟨7447785860222012006047327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9930381146962682674729769 7447785860222012006047327)
  ·
    refine ⟨11171678790333018009070991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7447785860222012006047327 11171678790333018009070991)
    ·
      refine ⟨16757518185499527013606487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11171678790333018009070991 16757518185499527013606487)
      ·
        refine ⟨25136277278249290520409731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16757518185499527013606487 25136277278249290520409731)
        ·
          refine ⟨37704415917373935780614597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25136277278249290520409731 37704415917373935780614597)
          ·
            refine ⟨7069577984507612958865237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37704415917373935780614597 7069577984507612958865237)
            ·
              refine ⟨41423308502974294680851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7069577984507612958865237 41423308502974294680851)
              ·
                rfl

theorem cell19_408400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 9].length) (baseStart_408400 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408400 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408400 prefixEnd_408400 := by exact prefixLift 408400
  have htrace : WordTrace (prefixWord ++ tailWord_408400) baseStart_408400 baseEnd_408400 := by
    simpa [prefixWord, tailWord_408400, baseEnd_408400] using wordTrace_append hprefix tailTrace_408400
  have hstable : (prefixWord ++ tailWord_408400).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408400).length < 2 ^ (prefixWord ++ tailWord_408400).sum := by decide
  have hdescent : baseEnd_408400 < baseStart_408400 := by decide
  rcases family_descends (prefixWord ++ tailWord_408400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408457 : List Nat := [1, 2, 1, 1, 5, 9]
def baseStart_408457 : Nat := 118140960795 + 408457 * 2 ^ 59
def prefixEnd_408457 : Nat := 4983230072969 + 3 ^ 40 * 408457 * 2
def baseEnd_408457 : Nat := 13809696638262626752859

theorem tailTrace_408457 : CollatzResearch.WordTrace tailWord_408457 prefixEnd_408457 13809696638262626752859 := by
  unfold tailWord_408457
  simp only [CollatzResearch.WordTrace]
  refine ⟨14897650681237522746919625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9931767120825015164613083 14897650681237522746919625)
  ·
    refine ⟨11173238010928142060189719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14897650681237522746919625 11173238010928142060189719)
    ·
      refine ⟨16759857016392213090284579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11173238010928142060189719 16759857016392213090284579)
      ·
        refine ⟨25139785524588319635426869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16759857016392213090284579 25139785524588319635426869)
        ·
          refine ⟨2356854892930154965821269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25139785524588319635426869 2356854892930154965821269)
          ·
            refine ⟨13809696638262626752859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2356854892930154965821269 13809696638262626752859)
            ·
              rfl

theorem cell19_408457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 9].length) (baseStart_408457 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408457 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408457 prefixEnd_408457 := by exact prefixLift 408457
  have htrace : WordTrace (prefixWord ++ tailWord_408457) baseStart_408457 baseEnd_408457 := by
    simpa [prefixWord, tailWord_408457, baseEnd_408457] using wordTrace_append hprefix tailTrace_408457
  have hstable : (prefixWord ++ tailWord_408457).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408457).length < 2 ^ (prefixWord ++ tailWord_408457).sum := by decide
  have hdescent : baseEnd_408457 < baseStart_408457 := by decide
  rcases family_descends (prefixWord ++ tailWord_408457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408546 : List Nat := [3, 3, 3, 1, 1, 1, 4, 3]
def baseStart_408546 : Nat := 118140960795 + 408546 * 2 ^ 59
def prefixEnd_408546 : Nat := 4983230072969 + 3 ^ 40 * 408546 * 2
def baseEnd_408546 : Nat := 124314351094437804797711

theorem tailTrace_408546 : CollatzResearch.WordTrace tailWord_408546 prefixEnd_408546 124314351094437804797711 := by
  unfold tailWord_408546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3725224194478772736727373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9933931185276727297939661 3725224194478772736727373)
  ·
    refine ⟨1396959072929539776272765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3725224194478772736727373 1396959072929539776272765)
    ·
      refine ⟨523859652348577416102287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1396959072929539776272765 523859652348577416102287)
      ·
        refine ⟨785789478522866124153431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 523859652348577416102287 785789478522866124153431)
        ·
          refine ⟨1178684217784299186230147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 785789478522866124153431 1178684217784299186230147)
          ·
            refine ⟨1768026326676448779345221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1178684217784299186230147 1768026326676448779345221)
            ·
              refine ⟨331504936251834146127229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1768026326676448779345221 331504936251834146127229)
              ·
                refine ⟨124314351094437804797711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331504936251834146127229 124314351094437804797711)
                ·
                  rfl

theorem cell19_408546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_408546 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408546 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408546 prefixEnd_408546 := by exact prefixLift 408546
  have htrace : WordTrace (prefixWord ++ tailWord_408546) baseStart_408546 baseEnd_408546 := by
    simpa [prefixWord, tailWord_408546, baseEnd_408546] using wordTrace_append hprefix tailTrace_408546
  have hstable : (prefixWord ++ tailWord_408546).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408546).length < 2 ^ (prefixWord ++ tailWord_408546).sum := by decide
  have hdescent : baseEnd_408546 < baseStart_408546 := by decide
  rcases family_descends (prefixWord ++ tailWord_408546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408565 : List Nat := [1, 3, 5, 2, 1, 2, 5]
def baseStart_408565 : Nat := 118140960795 + 408565 * 2 ^ 59
def prefixEnd_408565 : Nat := 4983230072969 + 3 ^ 40 * 408565 * 2
def baseEnd_408565 : Nat := 41440044168750463458479

theorem tailTrace_408565 : CollatzResearch.WordTrace tailWord_408565 prefixEnd_408565 41440044168750463458479 := by
  unfold tailWord_408565
  simp only [CollatzResearch.WordTrace]
  refine ⟨14901589764846257191851149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9934393176564171461234099 14901589764846257191851149)
  ·
    refine ⟨5588096161817346446944181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14901589764846257191851149 5588096161817346446944181)
    ·
      refine ⟨523884015170376229401017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5588096161817346446944181 523884015170376229401017)
      ·
        refine ⟨392913011377782172050763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 523884015170376229401017 392913011377782172050763)
        ·
          refine ⟨589369517066673258076145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 392913011377782172050763 589369517066673258076145)
          ·
            refine ⟨442027137800004943557109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589369517066673258076145 442027137800004943557109)
            ·
              refine ⟨41440044168750463458479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 442027137800004943557109 41440044168750463458479)
              ·
                rfl

theorem cell19_408565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 5].length) (baseStart_408565 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408565 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408565 prefixEnd_408565 := by exact prefixLift 408565
  have htrace : WordTrace (prefixWord ++ tailWord_408565) baseStart_408565 baseEnd_408565 := by
    simpa [prefixWord, tailWord_408565, baseEnd_408565] using wordTrace_append hprefix tailTrace_408565
  have hstable : (prefixWord ++ tailWord_408565).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408565).length < 2 ^ (prefixWord ++ tailWord_408565).sum := by decide
  have hdescent : baseEnd_408565 < baseStart_408565 := by decide
  rcases family_descends (prefixWord ++ tailWord_408565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408588 : List Nat := [2, 2, 1, 2, 3, 3, 2, 4]
def baseStart_408588 : Nat := 118140960795 + 408588 * 2 ^ 59
def prefixEnd_408588 : Nat := 4983230072969 + 3 ^ 40 * 408588 * 2
def baseEnd_408588 : Nat := 124327131057394151864263

theorem tailTrace_408588 : CollatzResearch.WordTrace tailWord_408588 prefixEnd_408588 124327131057394151864263 := by
  unfold tailWord_408588
  simp only [CollatzResearch.WordTrace]
  refine ⟨7451214321881466059969209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9934952429175288079958945 7451214321881466059969209)
  ·
    refine ⟨5588410741411099544976907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7451214321881466059969209 5588410741411099544976907)
    ·
      refine ⟨8382616112116649317465361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5588410741411099544976907 8382616112116649317465361)
      ·
        refine ⟨6286962084087486988099021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8382616112116649317465361 6286962084087486988099021)
        ·
          refine ⟨2357610781532807620537133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6286962084087486988099021 2357610781532807620537133)
          ·
            refine ⟨884104043074802857701425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2357610781532807620537133 884104043074802857701425)
            ·
              refine ⟨663078032306102143276069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 884104043074802857701425 663078032306102143276069)
              ·
                refine ⟨124327131057394151864263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 663078032306102143276069 124327131057394151864263)
                ·
                  rfl

theorem cell19_408588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_408588 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408588 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408588 prefixEnd_408588 := by exact prefixLift 408588
  have htrace : WordTrace (prefixWord ++ tailWord_408588) baseStart_408588 baseEnd_408588 := by
    simpa [prefixWord, tailWord_408588, baseEnd_408588] using wordTrace_append hprefix tailTrace_408588
  have hstable : (prefixWord ++ tailWord_408588).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408588).length < 2 ^ (prefixWord ++ tailWord_408588).sum := by decide
  have hdescent : baseEnd_408588 < baseStart_408588 := by decide
  rcases family_descends (prefixWord ++ tailWord_408588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408641 : List Nat := [1, 2, 5, 1, 4, 1, 1, 4]
def baseStart_408641 : Nat := 118140960795 + 408641 * 2 ^ 59
def prefixEnd_408641 : Nat := 4983230072969 + 3 ^ 40 * 408641 * 2
def baseEnd_408641 : Nat := 124343258153505732686341

theorem tailTrace_408641 : CollatzResearch.WordTrace tailWord_408641 prefixEnd_408641 124343258153505732686341 := by
  unfold tailWord_408641
  simp only [CollatzResearch.WordTrace]
  refine ⟨14904361712570922171617777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9936241141713948114411851 14904361712570922171617777)
  ·
    refine ⟨11178271284428191628713333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14904361712570922171617777 11178271284428191628713333)
    ·
      refine ⟨1047962932915142965191875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11178271284428191628713333 1047962932915142965191875)
      ·
        refine ⟨1571944399372714447787813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1047962932915142965191875 1571944399372714447787813)
        ·
          refine ⟨294739574882383958960215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1571944399372714447787813 294739574882383958960215)
          ·
            refine ⟨442109362323575938440323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 294739574882383958960215 442109362323575938440323)
            ·
              refine ⟨663164043485363907660485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 442109362323575938440323 663164043485363907660485)
              ·
                refine ⟨124343258153505732686341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 663164043485363907660485 124343258153505732686341)
                ·
                  rfl

theorem cell19_408641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 4, 1, 1, 4].length) (baseStart_408641 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408641 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408641 prefixEnd_408641 := by exact prefixLift 408641
  have htrace : WordTrace (prefixWord ++ tailWord_408641) baseStart_408641 baseEnd_408641 := by
    simpa [prefixWord, tailWord_408641, baseEnd_408641] using wordTrace_append hprefix tailTrace_408641
  have hstable : (prefixWord ++ tailWord_408641).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408641).length < 2 ^ (prefixWord ++ tailWord_408641).sum := by decide
  have hdescent : baseEnd_408641 < baseStart_408641 := by decide
  rcases family_descends (prefixWord ++ tailWord_408641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408664 : List Nat := [2, 1, 2, 2, 1, 3, 5, 3]
def baseStart_408664 : Nat := 118140960795 + 408664 * 2 ^ 59
def prefixEnd_408664 : Nat := 4983230072969 + 3 ^ 40 * 408664 * 2
def baseEnd_408664 : Nat := 124350256704648494175167

theorem tailTrace_408664 : CollatzResearch.WordTrace tailWord_408664 prefixEnd_408664 124350256704648494175167 := by
  unfold tailWord_408664
  simp only [CollatzResearch.WordTrace]
  refine ⟨7452600295743798549852523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9936800394325064733136697 7452600295743798549852523)
  ·
    refine ⟨11178900443615697824778785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7452600295743798549852523 11178900443615697824778785)
    ·
      refine ⟨8384175332711773368584089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11178900443615697824778785 8384175332711773368584089)
      ·
        refine ⟨6288131499533830026438067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8384175332711773368584089 6288131499533830026438067)
        ·
          refine ⟨9432197249300745039657101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6288131499533830026438067 9432197249300745039657101)
          ·
            refine ⟨3537073968487779389871413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9432197249300745039657101 3537073968487779389871413)
            ·
              refine ⟨331600684545729317800445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3537073968487779389871413 331600684545729317800445)
              ·
                refine ⟨124350256704648494175167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331600684545729317800445 124350256704648494175167)
                ·
                  rfl

theorem cell19_408664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 5, 3].length) (baseStart_408664 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408664 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408664 prefixEnd_408664 := by exact prefixLift 408664
  have htrace : WordTrace (prefixWord ++ tailWord_408664) baseStart_408664 baseEnd_408664 := by
    simpa [prefixWord, tailWord_408664, baseEnd_408664] using wordTrace_append hprefix tailTrace_408664
  have hstable : (prefixWord ++ tailWord_408664).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408664).length < 2 ^ (prefixWord ++ tailWord_408664).sum := by decide
  have hdescent : baseEnd_408664 < baseStart_408664 := by decide
  rcases family_descends (prefixWord ++ tailWord_408664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408738 : List Nat := [3, 3, 1, 3, 2, 2, 5]
def baseStart_408738 : Nat := 118140960795 + 408738 * 2 ^ 59
def prefixEnd_408738 : Nat := 4983230072969 + 3 ^ 40 * 408738 * 2
def baseEnd_408738 : Nat := 41457591260746082843507

theorem tailTrace_408738 : CollatzResearch.WordTrace tailWord_408738 prefixEnd_408738 41457591260746082843507 := by
  unfold tailWord_408738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3726974898304876934474717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9938599728813005158599245 3726974898304876934474717)
  ·
    refine ⟨1397615586864328850428019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3726974898304876934474717 1397615586864328850428019)
    ·
      refine ⟨2096423380296493275642029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1397615586864328850428019 2096423380296493275642029)
      ·
        refine ⟨786158767611184978365761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2096423380296493275642029 786158767611184978365761)
        ·
          refine ⟨589619075708388733774321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786158767611184978365761 589619075708388733774321)
          ·
            refine ⟨442214306781291550330741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589619075708388733774321 442214306781291550330741)
            ·
              refine ⟨41457591260746082843507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 442214306781291550330741 41457591260746082843507)
              ·
                rfl

theorem cell19_408738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 5].length) (baseStart_408738 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408738 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408738 prefixEnd_408738 := by exact prefixLift 408738
  have htrace : WordTrace (prefixWord ++ tailWord_408738) baseStart_408738 baseEnd_408738 := by
    simpa [prefixWord, tailWord_408738, baseEnd_408738] using wordTrace_append hprefix tailTrace_408738
  have hstable : (prefixWord ++ tailWord_408738).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408738).length < 2 ^ (prefixWord ++ tailWord_408738).sum := by decide
  have hdescent : baseEnd_408738 < baseStart_408738 := by decide
  rcases family_descends (prefixWord ++ tailWord_408738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408740 : List Nat := [2, 3, 1, 2, 3, 3, 5]
def baseStart_408740 : Nat := 118140960795 + 408740 * 2 ^ 59
def prefixEnd_408740 : Nat := 4983230072969 + 3 ^ 40 * 408740 * 2
def baseEnd_408740 : Nat := 41457794117300945495357

theorem tailTrace_408740 : CollatzResearch.WordTrace tailWord_408740 prefixEnd_408740 41457794117300945495357 := by
  unfold tailWord_408740
  simp only [CollatzResearch.WordTrace]
  refine ⟨7453986269606131039735837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9938648359474841386314449 7453986269606131039735837)
  ·
    refine ⟨2795244851102299139900939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7453986269606131039735837 2795244851102299139900939)
    ·
      refine ⟨4192867276653448709851409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2795244851102299139900939 4192867276653448709851409)
      ·
        refine ⟨3144650457490086532388557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4192867276653448709851409 3144650457490086532388557)
        ·
          refine ⟨1179243921558782449645709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3144650457490086532388557 1179243921558782449645709)
          ·
            refine ⟨442216470584543418617141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1179243921558782449645709 442216470584543418617141)
            ·
              refine ⟨41457794117300945495357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 442216470584543418617141 41457794117300945495357)
              ·
                rfl

theorem cell19_408740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 5].length) (baseStart_408740 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408740 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408740 prefixEnd_408740 := by exact prefixLift 408740
  have htrace : WordTrace (prefixWord ++ tailWord_408740) baseStart_408740 baseEnd_408740 := by
    simpa [prefixWord, tailWord_408740, baseEnd_408740] using wordTrace_append hprefix tailTrace_408740
  have hstable : (prefixWord ++ tailWord_408740).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408740).length < 2 ^ (prefixWord ++ tailWord_408740).sum := by decide
  have hdescent : baseEnd_408740 < baseStart_408740 := by decide
  rcases family_descends (prefixWord ++ tailWord_408740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408761 : List Nat := [1, 2, 1, 4, 1, 3, 1, 6]
def baseStart_408761 : Nat := 118140960795 + 408761 * 2 ^ 59
def prefixEnd_408761 : Nat := 4983230072969 + 3 ^ 40 * 408761 * 2
def baseEnd_408761 : Nat := 124379772333381010019347

theorem tailTrace_408761 : CollatzResearch.WordTrace tailWord_408761 prefixEnd_408761 124379772333381010019347 := by
  unfold tailWord_408761
  simp only [CollatzResearch.WordTrace]
  refine ⟨14908738472136182665986137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9939158981424121777324091 14908738472136182665986137)
  ·
    refine ⟨11181553854102136999489603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14908738472136182665986137 11181553854102136999489603)
    ·
      refine ⟨16772330781153205499234405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11181553854102136999489603 16772330781153205499234405)
      ·
        refine ⟨3144812021466226031106451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16772330781153205499234405 3144812021466226031106451)
        ·
          refine ⟨4717218032199339046659677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3144812021466226031106451 4717218032199339046659677)
          ·
            refine ⟨1768956762074752142497379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4717218032199339046659677 1768956762074752142497379)
            ·
              refine ⟨2653435143112128213746069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1768956762074752142497379 2653435143112128213746069)
              ·
                refine ⟨124379772333381010019347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2653435143112128213746069 124379772333381010019347)
                ·
                  rfl

theorem cell19_408761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 6].length) (baseStart_408761 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408761 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408761 prefixEnd_408761 := by exact prefixLift 408761
  have htrace : WordTrace (prefixWord ++ tailWord_408761) baseStart_408761 baseEnd_408761 := by
    simpa [prefixWord, tailWord_408761, baseEnd_408761] using wordTrace_append hprefix tailTrace_408761
  have hstable : (prefixWord ++ tailWord_408761).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408761).length < 2 ^ (prefixWord ++ tailWord_408761).sum := by decide
  have hdescent : baseEnd_408761 < baseStart_408761 := by decide
  rcases family_descends (prefixWord ++ tailWord_408761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408797 : List Nat := [1, 4, 3, 2, 2, 7]
def baseStart_408797 : Nat := 118140960795 + 408797 * 2 ^ 59
def prefixEnd_408797 : Nat := 4983230072969 + 3 ^ 40 * 408797 * 2
def baseEnd_408797 : Nat := 13821191843038177024361

theorem tailTrace_408797 : CollatzResearch.WordTrace tailWord_408797 prefixEnd_408797 13821191843038177024361 := by
  unfold tailWord_408797
  simp only [CollatzResearch.WordTrace]
  refine ⟨14910051500005760814296645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9940034333337173876197763 14910051500005760814296645)
  ·
    refine ⟨2795634656251080152680621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14910051500005760814296645 2795634656251080152680621)
    ·
      refine ⟨1048362996094155057255233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2795634656251080152680621 1048362996094155057255233)
      ·
        refine ⟨786272247070616292941425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1048362996094155057255233 786272247070616292941425)
        ·
          refine ⟨589704185302962219706069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 786272247070616292941425 589704185302962219706069)
          ·
            refine ⟨13821191843038177024361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 589704185302962219706069 13821191843038177024361)
            ·
              rfl

theorem cell19_408797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 7].length) (baseStart_408797 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408797 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408797 prefixEnd_408797 := by exact prefixLift 408797
  have htrace : WordTrace (prefixWord ++ tailWord_408797) baseStart_408797 baseEnd_408797 := by
    simpa [prefixWord, tailWord_408797, baseEnd_408797] using wordTrace_append hprefix tailTrace_408797
  have hstable : (prefixWord ++ tailWord_408797).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408797).length < 2 ^ (prefixWord ++ tailWord_408797).sum := by decide
  have hdescent : baseEnd_408797 < baseStart_408797 := by decide
  rcases family_descends (prefixWord ++ tailWord_408797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408835 : List Nat := [1, 1, 1, 3, 2, 5, 3, 3]
def baseStart_408835 : Nat := 118140960795 + 408835 * 2 ^ 59
def prefixEnd_408835 : Nat := 4983230072969 + 3 ^ 40 * 408835 * 2
def baseEnd_408835 : Nat := 124402289410970764374701

theorem tailTrace_408835 : CollatzResearch.WordTrace tailWord_408835 prefixEnd_408835 124402289410970764374701 := by
  unfold tailWord_408835
  simp only [CollatzResearch.WordTrace]
  refine ⟨14911437473868093304179959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9940958315912062202786639 14911437473868093304179959)
  ·
    refine ⟨22367156210802139956269939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14911437473868093304179959 22367156210802139956269939)
    ·
      refine ⟨33550734316203209934404909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22367156210802139956269939 33550734316203209934404909)
      ·
        refine ⟨12581525368576203725401841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33550734316203209934404909 12581525368576203725401841)
        ·
          refine ⟨9436144026432152794051381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12581525368576203725401841 9436144026432152794051381)
          ·
            refine ⟨884638502478014324442317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9436144026432152794051381 884638502478014324442317)
            ·
              refine ⟨331739438429255371665869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 884638502478014324442317 331739438429255371665869)
              ·
                refine ⟨124402289410970764374701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331739438429255371665869 124402289410970764374701)
                ·
                  rfl

theorem cell19_408835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 3, 3].length) (baseStart_408835 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408835 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408835 prefixEnd_408835 := by exact prefixLift 408835
  have htrace : WordTrace (prefixWord ++ tailWord_408835) baseStart_408835 baseEnd_408835 := by
    simpa [prefixWord, tailWord_408835, baseEnd_408835] using wordTrace_append hprefix tailTrace_408835
  have hstable : (prefixWord ++ tailWord_408835).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408835).length < 2 ^ (prefixWord ++ tailWord_408835).sum := by decide
  have hdescent : baseEnd_408835 < baseStart_408835 := by decide
  rcases family_descends (prefixWord ++ tailWord_408835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408856 : List Nat := [2, 1, 2, 3, 1, 4, 6]
def baseStart_408856 : Nat := 118140960795 + 408856 * 2 ^ 59
def prefixEnd_408856 : Nat := 4983230072969 + 3 ^ 40 * 408856 * 2
def baseEnd_408856 : Nat := 41469559797482979302659

theorem tailTrace_408856 : CollatzResearch.WordTrace tailWord_408856 prefixEnd_408856 41469559797482979302659 := by
  unfold tailWord_408856
  simp only [CollatzResearch.WordTrace]
  refine ⟨7456101703396006945347211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9941468937861342593796281 7456101703396006945347211)
  ·
    refine ⟨11184152555094010418020817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7456101703396006945347211 11184152555094010418020817)
    ·
      refine ⟨8388114416320507813515613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11184152555094010418020817 8388114416320507813515613)
      ·
        refine ⟨3145542906120190430068355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8388114416320507813515613 3145542906120190430068355)
        ·
          refine ⟨4718314359180285645102533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145542906120190430068355 4718314359180285645102533)
          ·
            refine ⟨884683942346303558456725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4718314359180285645102533 884683942346303558456725)
            ·
              refine ⟨41469559797482979302659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 884683942346303558456725 41469559797482979302659)
              ·
                rfl

theorem cell19_408856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 6].length) (baseStart_408856 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408856 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408856 prefixEnd_408856 := by exact prefixLift 408856
  have htrace : WordTrace (prefixWord ++ tailWord_408856) baseStart_408856 baseEnd_408856 := by
    simpa [prefixWord, tailWord_408856, baseEnd_408856] using wordTrace_append hprefix tailTrace_408856
  have hstable : (prefixWord ++ tailWord_408856).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408856).length < 2 ^ (prefixWord ++ tailWord_408856).sum := by decide
  have hdescent : baseEnd_408856 < baseStart_408856 := by decide
  rcases family_descends (prefixWord ++ tailWord_408856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408886 : List Nat := [5, 1, 2, 3, 1, 2, 2, 3]
def baseStart_408886 : Nat := 118140960795 + 408886 * 2 ^ 59
def prefixEnd_408886 : Nat := 4983230072969 + 3 ^ 40 * 408886 * 2
def baseEnd_408886 : Nat := 124417807937417757241229

theorem tailTrace_408886 : CollatzResearch.WordTrace tailWord_408886 prefixEnd_408886 124417807937417757241229 := by
  unfold tailWord_408886
  simp only [CollatzResearch.WordTrace]
  refine ⟨932081099792708063392907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9942198397788886009524341 932081099792708063392907)
  ·
    refine ⟨1398121649689062095089361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 932081099792708063392907 1398121649689062095089361)
    ·
      refine ⟨1048591237266796571317021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1398121649689062095089361 1048591237266796571317021)
      ·
        refine ⟨393221713975048714243883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1048591237266796571317021 393221713975048714243883)
        ·
          refine ⟨589832570962573071365825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 393221713975048714243883 589832570962573071365825)
          ·
            refine ⟨442374428221929803524369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 589832570962573071365825 442374428221929803524369)
            ·
              refine ⟨331780821166447352643277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442374428221929803524369 331780821166447352643277)
              ·
                refine ⟨124417807937417757241229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331780821166447352643277 124417807937417757241229)
                ·
                  rfl

theorem cell19_408886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_408886 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408886 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408886 prefixEnd_408886 := by exact prefixLift 408886
  have htrace : WordTrace (prefixWord ++ tailWord_408886) baseStart_408886 baseEnd_408886 := by
    simpa [prefixWord, tailWord_408886, baseEnd_408886] using wordTrace_append hprefix tailTrace_408886
  have hstable : (prefixWord ++ tailWord_408886).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408886).length < 2 ^ (prefixWord ++ tailWord_408886).sum := by decide
  have hdescent : baseEnd_408886 < baseStart_408886 := by decide
  rcases family_descends (prefixWord ++ tailWord_408886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408892 : List Nat := [2, 2, 2, 2, 1, 3, 4, 3]
def baseStart_408892 : Nat := 118140960795 + 408892 * 2 ^ 59
def prefixEnd_408892 : Nat := 4983230072969 + 3 ^ 40 * 408892 * 2
def baseEnd_408892 : Nat := 124419633646411521107879

theorem tailTrace_408892 : CollatzResearch.WordTrace tailWord_408892 prefixEnd_408892 124419633646411521107879 := by
  unfold tailWord_408892
  simp only [CollatzResearch.WordTrace]
  refine ⟨7456758217330796019502465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9942344289774394692669953 7456758217330796019502465)
  ·
    refine ⟨5592568662998097014626849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7456758217330796019502465 5592568662998097014626849)
    ·
      refine ⟨4194426497248572760970137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5592568662998097014626849 4194426497248572760970137)
      ·
        refine ⟨3145819872936429570727603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4194426497248572760970137 3145819872936429570727603)
        ·
          refine ⟨4718729809404644356091405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145819872936429570727603 4718729809404644356091405)
          ·
            refine ⟨1769523678526741633534277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4718729809404644356091405 1769523678526741633534277)
            ·
              refine ⟨331785689723764056287677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1769523678526741633534277 331785689723764056287677)
              ·
                refine ⟨124419633646411521107879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331785689723764056287677 124419633646411521107879)
                ·
                  rfl

theorem cell19_408892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_408892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408892 prefixEnd_408892 := by exact prefixLift 408892
  have htrace : WordTrace (prefixWord ++ tailWord_408892) baseStart_408892 baseEnd_408892 := by
    simpa [prefixWord, tailWord_408892, baseEnd_408892] using wordTrace_append hprefix tailTrace_408892
  have hstable : (prefixWord ++ tailWord_408892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408892).length < 2 ^ (prefixWord ++ tailWord_408892).sum := by decide
  have hdescent : baseEnd_408892 < baseStart_408892 := by decide
  rcases family_descends (prefixWord ++ tailWord_408892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408930 : List Nat := [3, 3, 2, 1, 1, 1, 4, 4]
def baseStart_408930 : Nat := 118140960795 + 408930 * 2 ^ 59
def prefixEnd_408930 : Nat := 4983230072969 + 3 ^ 40 * 408930 * 2
def baseEnd_408930 : Nat := 124431196470038692263331

theorem tailTrace_408930 : CollatzResearch.WordTrace tailWord_408930 prefixEnd_408930 124431196470038692263331 := by
  unfold tailWord_408930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3728725602130981132222061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9943268272349283019258829 3728725602130981132222061)
  ·
    refine ⟨1398272100799117924583273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3728725602130981132222061 1398272100799117924583273)
    ·
      refine ⟨1048704075599338443437455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1398272100799117924583273 1048704075599338443437455)
      ·
        refine ⟨1573056113399007665156183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1048704075599338443437455 1573056113399007665156183)
        ·
          refine ⟨2359584170098511497734275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573056113399007665156183 2359584170098511497734275)
          ·
            refine ⟨3539376255147767246601413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2359584170098511497734275 3539376255147767246601413)
            ·
              refine ⟨663633047840206358737765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3539376255147767246601413 663633047840206358737765)
              ·
                refine ⟨124431196470038692263331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 663633047840206358737765 124431196470038692263331)
                ·
                  rfl

theorem cell19_408930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_408930 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408930 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408930 prefixEnd_408930 := by exact prefixLift 408930
  have htrace : WordTrace (prefixWord ++ tailWord_408930) baseStart_408930 baseEnd_408930 := by
    simpa [prefixWord, tailWord_408930, baseEnd_408930] using wordTrace_append hprefix tailTrace_408930
  have hstable : (prefixWord ++ tailWord_408930).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408930).length < 2 ^ (prefixWord ++ tailWord_408930).sum := by decide
  have hdescent : baseEnd_408930 < baseStart_408930 := by decide
  rcases family_descends (prefixWord ++ tailWord_408930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_408932 : List Nat := [2, 3, 1, 1, 3, 2, 1, 6]
def baseStart_408932 : Nat := 118140960795 + 408932 * 2 ^ 59
def prefixEnd_408932 : Nat := 4983230072969 + 3 ^ 40 * 408932 * 2
def baseEnd_408932 : Nat := 124431805039703280218881

theorem tailTrace_408932 : CollatzResearch.WordTrace tailWord_408932 prefixEnd_408932 124431805039703280218881 := by
  unfold tailWord_408932
  simp only [CollatzResearch.WordTrace]
  refine ⟨7457487677258339435230525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9943316903011119246974033 7457487677258339435230525)
  ·
    refine ⟨2796557878971877288211447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7457487677258339435230525 2796557878971877288211447)
    ·
      refine ⟨4194836818457815932317171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2796557878971877288211447 4194836818457815932317171)
      ·
        refine ⟨6292255227686723898475757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4194836818457815932317171 6292255227686723898475757)
        ·
          refine ⟨2359595710382521461928409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6292255227686723898475757 2359595710382521461928409)
          ·
            refine ⟨1769696782786891096446307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2359595710382521461928409 1769696782786891096446307)
            ·
              refine ⟨2654545174180336644669461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1769696782786891096446307 2654545174180336644669461)
              ·
                refine ⟨124431805039703280218881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2654545174180336644669461 124431805039703280218881)
                ·
                  rfl

theorem cell19_408932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 6].length) (baseStart_408932 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_408932 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_408932 prefixEnd_408932 := by exact prefixLift 408932
  have htrace : WordTrace (prefixWord ++ tailWord_408932) baseStart_408932 baseEnd_408932 := by
    simpa [prefixWord, tailWord_408932, baseEnd_408932] using wordTrace_append hprefix tailTrace_408932
  have hstable : (prefixWord ++ tailWord_408932).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_408932).length < 2 ^ (prefixWord ++ tailWord_408932).sum := by decide
  have hdescent : baseEnd_408932 < baseStart_408932 := by decide
  rcases family_descends (prefixWord ++ tailWord_408932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409061 : List Nat := [1, 3, 1, 5, 1, 3, 2, 3]
def baseStart_409061 : Nat := 118140960795 + 409061 * 2 ^ 59
def prefixEnd_409061 : Nat := 4983230072969 + 3 ^ 40 * 409061 * 2
def baseEnd_409061 : Nat := 124471057783069203351863

theorem tailTrace_409061 : CollatzResearch.WordTrace tailWord_409061 prefixEnd_409061 124471057783069203351863 := by
  unfold tailWord_409061
  simp only [CollatzResearch.WordTrace]
  refine ⟨14919680371049333901907037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9946453580699555934604691 14919680371049333901907037)
  ·
    refine ⟨5594880139143500213215139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14919680371049333901907037 5594880139143500213215139)
    ·
      refine ⟨8392320208715250319822709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5594880139143500213215139 8392320208715250319822709)
      ·
        refine ⟨786780019567054717483379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8392320208715250319822709 786780019567054717483379)
        ·
          refine ⟨1180170029350582076225069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 786780019567054717483379 1180170029350582076225069)
          ·
            refine ⟨442563761006468278584401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1180170029350582076225069 442563761006468278584401)
            ·
              refine ⟨331922820754851208938301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442563761006468278584401 331922820754851208938301)
              ·
                refine ⟨124471057783069203351863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331922820754851208938301 124471057783069203351863)
                ·
                  rfl

theorem cell19_409061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 2, 3].length) (baseStart_409061 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409061 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409061 prefixEnd_409061 := by exact prefixLift 409061
  have htrace : WordTrace (prefixWord ++ tailWord_409061) baseStart_409061 baseEnd_409061 := by
    simpa [prefixWord, tailWord_409061, baseEnd_409061] using wordTrace_append hprefix tailTrace_409061
  have hstable : (prefixWord ++ tailWord_409061).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409061).length < 2 ^ (prefixWord ++ tailWord_409061).sum := by decide
  have hdescent : baseEnd_409061 < baseStart_409061 := by decide
  rcases family_descends (prefixWord ++ tailWord_409061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409063 : List Nat := [1, 1, 5, 2, 1, 2, 4, 3]
def baseStart_409063 : Nat := 118140960795 + 409063 * 2 ^ 59
def prefixEnd_409063 : Nat := 4983230072969 + 3 ^ 40 * 409063 * 2
def baseEnd_409063 : Nat := 124471666352733791307413

theorem tailTrace_409063 : CollatzResearch.WordTrace tailWord_409063 prefixEnd_409063 124471666352733791307413 := by
  unfold tailWord_409063
  simp only [CollatzResearch.WordTrace]
  refine ⟨14919753317042088243479843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9946502211361392162319895 14919753317042088243479843)
  ·
    refine ⟨22379629975563132365219765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14919753317042088243479843 22379629975563132365219765)
    ·
      refine ⟨2098090310209043659239353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22379629975563132365219765 2098090310209043659239353)
      ·
        refine ⟨1573567732656782744429515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2098090310209043659239353 1573567732656782744429515)
        ·
          refine ⟨2360351598985174116644273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1573567732656782744429515 2360351598985174116644273)
          ·
            refine ⟨1770263699238880587483205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2360351598985174116644273 1770263699238880587483205)
            ·
              refine ⟨331924443607290110153101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1770263699238880587483205 331924443607290110153101)
              ·
                refine ⟨124471666352733791307413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 331924443607290110153101 124471666352733791307413)
                ·
                  rfl

theorem cell19_409063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 4, 3].length) (baseStart_409063 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409063 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409063 prefixEnd_409063 := by exact prefixLift 409063
  have htrace : WordTrace (prefixWord ++ tailWord_409063) baseStart_409063 baseEnd_409063 := by
    simpa [prefixWord, tailWord_409063, baseEnd_409063] using wordTrace_append hprefix tailTrace_409063
  have hstable : (prefixWord ++ tailWord_409063).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409063).length < 2 ^ (prefixWord ++ tailWord_409063).sum := by decide
  have hdescent : baseEnd_409063 < baseStart_409063 := by decide
  rcases family_descends (prefixWord ++ tailWord_409063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409122 : List Nat := [3, 3, 1, 1, 1, 1, 4, 5]
def baseStart_409122 : Nat := 118140960795 + 409122 * 2 ^ 59
def prefixEnd_409122 : Nat := 4983230072969 + 3 ^ 40 * 409122 * 2
def baseEnd_409122 : Nat := 124489619157839135996141

theorem tailTrace_409122 : CollatzResearch.WordTrace tailWord_409122 prefixEnd_409122 124489619157839135996141 := by
  unfold tailWord_409122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3730476305957085329969405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9947936815885560879918413 3730476305957085329969405)
  ·
    refine ⟨1398928614733906998738527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3730476305957085329969405 1398928614733906998738527)
    ·
      refine ⟨2098392922100860498107791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1398928614733906998738527 2098392922100860498107791)
      ·
        refine ⟨3147589383151290747161687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2098392922100860498107791 3147589383151290747161687)
        ·
          refine ⟨4721384074726936120742531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3147589383151290747161687 4721384074726936120742531)
          ·
            refine ⟨7082076112090404181113797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4721384074726936120742531 7082076112090404181113797)
            ·
              refine ⟨1327889271016950783958837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7082076112090404181113797 1327889271016950783958837)
              ·
                refine ⟨124489619157839135996141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1327889271016950783958837 124489619157839135996141)
                ·
                  rfl

theorem cell19_409122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_409122 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409122 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409122 prefixEnd_409122 := by exact prefixLift 409122
  have htrace : WordTrace (prefixWord ++ tailWord_409122) baseStart_409122 baseEnd_409122 := by
    simpa [prefixWord, tailWord_409122, baseEnd_409122] using wordTrace_append hprefix tailTrace_409122
  have hstable : (prefixWord ++ tailWord_409122).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409122).length < 2 ^ (prefixWord ++ tailWord_409122).sum := by decide
  have hdescent : baseEnd_409122 < baseStart_409122 := by decide
  rcases family_descends (prefixWord ++ tailWord_409122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409143 : List Nat := [1, 1, 3, 1, 2, 11]
def baseStart_409143 : Nat := 118140960795 + 409143 * 2 ^ 59
def prefixEnd_409143 : Nat := 4983230072969 + 3 ^ 40 * 409143 * 2
def baseEnd_409143 : Nat := 13832889904368589947713

theorem tailTrace_409143 : CollatzResearch.WordTrace tailWord_409143 prefixEnd_409143 13832889904368589947713 := by
  unfold tailWord_409143
  simp only [CollatzResearch.WordTrace]
  refine ⟨14922671156752261906392083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9948447437834841270928055 14922671156752261906392083)
  ·
    refine ⟨22384006735128392859588125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14922671156752261906392083 22384006735128392859588125)
    ·
      refine ⟨8394002525673147322345547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22384006735128392859588125 8394002525673147322345547)
      ·
        refine ⟨12591003788509720983518321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8394002525673147322345547 12591003788509720983518321)
        ·
          refine ⟨9443252841382290737638741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12591003788509720983518321 9443252841382290737638741)
          ·
            refine ⟨13832889904368589947713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9443252841382290737638741 13832889904368589947713)
            ·
              rfl

theorem cell19_409143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 11].length) (baseStart_409143 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409143 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409143 prefixEnd_409143 := by exact prefixLift 409143
  have htrace : WordTrace (prefixWord ++ tailWord_409143) baseStart_409143 baseEnd_409143 := by
    simpa [prefixWord, tailWord_409143, baseEnd_409143] using wordTrace_append hprefix tailTrace_409143
  have hstable : (prefixWord ++ tailWord_409143).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409143).length < 2 ^ (prefixWord ++ tailWord_409143).sum := by decide
  have hdescent : baseEnd_409143 < baseStart_409143 := by decide
  rcases family_descends (prefixWord ++ tailWord_409143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409219 : List Nat := [1, 1, 1, 3, 3, 1, 1, 8]
def baseStart_409219 : Nat := 118140960795 + 409219 * 2 ^ 59
def prefixEnd_409219 : Nat := 4983230072969 + 3 ^ 40 * 409219 * 2
def baseEnd_409219 : Nat := 124519134786571651840321

theorem tailTrace_409219 : CollatzResearch.WordTrace tailWord_409219 prefixEnd_409219 124519134786571651840321 := by
  unfold tailWord_409219
  simp only [CollatzResearch.WordTrace]
  refine ⟨14925443104476926886158711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9950295402984617924105807 14925443104476926886158711)
  ·
    refine ⟨22388164656715390329238067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14925443104476926886158711 22388164656715390329238067)
    ·
      refine ⟨33582246985073085493857101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22388164656715390329238067 33582246985073085493857101)
      ·
        refine ⟨12593342619402407060196413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33582246985073085493857101 12593342619402407060196413)
        ·
          refine ⟨4722503482275902647573655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12593342619402407060196413 4722503482275902647573655)
          ·
            refine ⟨7083755223413853971360483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4722503482275902647573655 7083755223413853971360483)
            ·
              refine ⟨10625632835120780957040725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7083755223413853971360483 10625632835120780957040725)
              ·
                refine ⟨124519134786571651840321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10625632835120780957040725 124519134786571651840321)
                ·
                  rfl

theorem cell19_409219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 8].length) (baseStart_409219 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409219 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409219 prefixEnd_409219 := by exact prefixLift 409219
  have htrace : WordTrace (prefixWord ++ tailWord_409219) baseStart_409219 baseEnd_409219 := by
    simpa [prefixWord, tailWord_409219, baseEnd_409219] using wordTrace_append hprefix tailTrace_409219
  have hstable : (prefixWord ++ tailWord_409219).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409219).length < 2 ^ (prefixWord ++ tailWord_409219).sum := by decide
  have hdescent : baseEnd_409219 < baseStart_409219 := by decide
  rcases family_descends (prefixWord ++ tailWord_409219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409234 : List Nat := [3, 2, 3, 1, 3, 1, 1, 5]
def baseStart_409234 : Nat := 118140960795 + 409234 * 2 ^ 59
def prefixEnd_409234 : Nat := 4983230072969 + 3 ^ 40 * 409234 * 2
def baseEnd_409234 : Nat := 124523699059056061506947

theorem tailTrace_409234 : CollatzResearch.WordTrace tailWord_409234 prefixEnd_409234 124523699059056061506947 := by
  unfold tailWord_409234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3731497549855646111988689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9950660132948389631969837 3731497549855646111988689)
  ·
    refine ⟨2798623162391734583991517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3731497549855646111988689 2798623162391734583991517)
    ·
      refine ⟨1049483685896900468996819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2798623162391734583991517 1049483685896900468996819)
      ·
        refine ⟨1574225528845350703495229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1049483685896900468996819 1574225528845350703495229)
        ·
          refine ⟨590334573317006513810711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1574225528845350703495229 590334573317006513810711)
          ·
            refine ⟨885501859975509770716067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590334573317006513810711 885501859975509770716067)
            ·
              refine ⟨1328252789963264656074101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885501859975509770716067 1328252789963264656074101)
              ·
                refine ⟨124523699059056061506947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1328252789963264656074101 124523699059056061506947)
                ·
                  rfl

theorem cell19_409234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_409234 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409234 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409234 prefixEnd_409234 := by exact prefixLift 409234
  have htrace : WordTrace (prefixWord ++ tailWord_409234) baseStart_409234 baseEnd_409234 := by
    simpa [prefixWord, tailWord_409234, baseEnd_409234] using wordTrace_append hprefix tailTrace_409234
  have hstable : (prefixWord ++ tailWord_409234).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409234).length < 2 ^ (prefixWord ++ tailWord_409234).sum := by decide
  have hdescent : baseEnd_409234 < baseStart_409234 := by decide
  rcases family_descends (prefixWord ++ tailWord_409234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409270 : List Nat := [5, 1, 3, 1, 1, 2, 2, 4]
def baseStart_409270 : Nat := 118140960795 + 409270 * 2 ^ 59
def prefixEnd_409270 : Nat := 4983230072969 + 3 ^ 40 * 409270 * 2
def baseEnd_409270 : Nat := 124534653313018644706849

theorem tailTrace_409270 : CollatzResearch.WordTrace tailWord_409270 prefixEnd_409270 124534653313018644706849 := by
  unfold tailWord_409270
  simp only [CollatzResearch.WordTrace]
  refine ⟨932956451705760162266579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9951535484861441730843509 932956451705760162266579)
  ·
    refine ⟨1399434677558640243399869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 932956451705760162266579 1399434677558640243399869)
    ·
      refine ⟨524788004084490091274951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1399434677558640243399869 524788004084490091274951)
      ·
        refine ⟨787182006126735136912427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 524788004084490091274951 787182006126735136912427)
        ·
          refine ⟨1180773009190102705368641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787182006126735136912427 1180773009190102705368641)
          ·
            refine ⟨885579756892577029026481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1180773009190102705368641 885579756892577029026481)
            ·
              refine ⟨664184817669432771769861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885579756892577029026481 664184817669432771769861)
              ·
                refine ⟨124534653313018644706849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 664184817669432771769861 124534653313018644706849)
                ·
                  rfl

theorem cell19_409270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_409270 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409270 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409270 prefixEnd_409270 := by exact prefixLift 409270
  have htrace : WordTrace (prefixWord ++ tailWord_409270) baseStart_409270 baseEnd_409270 := by
    simpa [prefixWord, tailWord_409270, baseEnd_409270] using wordTrace_append hprefix tailTrace_409270
  have hstable : (prefixWord ++ tailWord_409270).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409270).length < 2 ^ (prefixWord ++ tailWord_409270).sum := by decide
  have hdescent : baseEnd_409270 < baseStart_409270 := by decide
  rcases family_descends (prefixWord ++ tailWord_409270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409274 : List Nat := [3, 1, 1, 1, 2, 5, 2, 4]
def baseStart_409274 : Nat := 118140960795 + 409274 * 2 ^ 59
def prefixEnd_409274 : Nat := 4983230072969 + 3 ^ 40 * 409274 * 2
def baseEnd_409274 : Nat := 124535870452347820617949

theorem tailTrace_409274 : CollatzResearch.WordTrace tailWord_409274 prefixEnd_409274 124535870452347820617949 := by
  unfold tailWord_409274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3731862279819417819852719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9951632746185114186273917 3731862279819417819852719)
  ·
    refine ⟨5597793419729126729779079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3731862279819417819852719 5597793419729126729779079)
    ·
      refine ⟨8396690129593690094668619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5597793419729126729779079 8396690129593690094668619)
      ·
        refine ⟨12595035194390535142002929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8396690129593690094668619 12595035194390535142002929)
        ·
          refine ⟨9446276395792901356502197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12595035194390535142002929 9446276395792901356502197)
          ·
            refine ⟨885588412105584502172081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9446276395792901356502197 885588412105584502172081)
            ·
              refine ⟨664191309079188376629061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 885588412105584502172081 664191309079188376629061)
              ·
                refine ⟨124535870452347820617949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 664191309079188376629061 124535870452347820617949)
                ·
                  rfl

theorem cell19_409274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_409274 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409274 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409274 prefixEnd_409274 := by exact prefixLift 409274
  have htrace : WordTrace (prefixWord ++ tailWord_409274) baseStart_409274 baseEnd_409274 := by
    simpa [prefixWord, tailWord_409274, baseEnd_409274] using wordTrace_append hprefix tailTrace_409274
  have hstable : (prefixWord ++ tailWord_409274).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409274).length < 2 ^ (prefixWord ++ tailWord_409274).sum := by decide
  have hdescent : baseEnd_409274 < baseStart_409274 := by decide
  rcases family_descends (prefixWord ++ tailWord_409274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409314 : List Nat := [3, 3, 13]
def baseStart_409314 : Nat := 118140960795 + 409314 * 2 ^ 59
def prefixEnd_409314 : Nat := 4983230072969 + 3 ^ 40 * 409314 * 2
def baseEnd_409314 : Nat := 512543382080821315757

theorem tailTrace_409314 : CollatzResearch.WordTrace tailWord_409314 prefixEnd_409314 512543382080821315757 := by
  unfold tailWord_409314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3732227009783189527716749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9952605359421838740577997 3732227009783189527716749)
  ·
    refine ⟨1399585128668696072893781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3732227009783189527716749 1399585128668696072893781)
    ·
      refine ⟨512543382080821315757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 13 1399585128668696072893781 512543382080821315757)
      ·
        rfl

theorem cell19_409314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 13].length) (baseStart_409314 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409314 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409314 prefixEnd_409314 := by exact prefixLift 409314
  have htrace : WordTrace (prefixWord ++ tailWord_409314) baseStart_409314 baseEnd_409314 := by
    simpa [prefixWord, tailWord_409314, baseEnd_409314] using wordTrace_append hprefix tailTrace_409314
  have hstable : (prefixWord ++ tailWord_409314).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409314).length < 2 ^ (prefixWord ++ tailWord_409314).sum := by decide
  have hdescent : baseEnd_409314 < baseStart_409314 := by decide
  rcases family_descends (prefixWord ++ tailWord_409314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409348 : List Nat := [2, 3, 2, 2, 1, 3, 3, 3]
def baseStart_409348 : Nat := 118140960795 + 409348 * 2 ^ 59
def prefixEnd_409348 : Nat := 4983230072969 + 3 ^ 40 * 409348 * 2
def baseEnd_409348 : Nat := 124558387529937574973303

theorem tailTrace_409348 : CollatzResearch.WordTrace tailWord_409348 prefixEnd_409348 124558387529937574973303 := by
  unfold tailWord_409348
  simp only [CollatzResearch.WordTrace]
  refine ⟨7465074060504790958802349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9953432080673054611736465 7465074060504790958802349)
  ·
    refine ⟨2799402772689296609550881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7465074060504790958802349 2799402772689296609550881)
    ·
      refine ⟨2099552079516972457163161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2799402772689296609550881 2099552079516972457163161)
      ·
        refine ⟨1574664059637729342872371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2099552079516972457163161 1574664059637729342872371)
        ·
          refine ⟨2361996089456594014308557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1574664059637729342872371 2361996089456594014308557)
          ·
            refine ⟨885748533546222755365709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2361996089456594014308557 885748533546222755365709)
            ·
              refine ⟨332155700079833533262141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 885748533546222755365709 332155700079833533262141)
              ·
                refine ⟨124558387529937574973303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332155700079833533262141 124558387529937574973303)
                ·
                  rfl

theorem cell19_409348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_409348 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409348 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409348 prefixEnd_409348 := by exact prefixLift 409348
  have htrace : WordTrace (prefixWord ++ tailWord_409348) baseStart_409348 baseEnd_409348 := by
    simpa [prefixWord, tailWord_409348, baseEnd_409348] using wordTrace_append hprefix tailTrace_409348
  have hstable : (prefixWord ++ tailWord_409348).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409348).length < 2 ^ (prefixWord ++ tailWord_409348).sum := by decide
  have hdescent : baseEnd_409348 < baseStart_409348 := by decide
  rcases family_descends (prefixWord ++ tailWord_409348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409401 : List Nat := [1, 2, 1, 7, 2, 1, 2, 3]
def baseStart_409401 : Nat := 118140960795 + 409401 * 2 ^ 59
def prefixEnd_409401 : Nat := 4983230072969 + 3 ^ 40 * 409401 * 2
def baseEnd_409401 : Nat := 124574514626049155795381

theorem tailTrace_409401 : CollatzResearch.WordTrace tailWord_409401 prefixEnd_409401 124574514626049155795381 := by
  unfold tailWord_409401
  simp only [CollatzResearch.WordTrace]
  refine ⟨14932081189817571969284057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9954720793211714646189371 14932081189817571969284057)
  ·
    refine ⟨11199060892363178976963043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14932081189817571969284057 11199060892363178976963043)
    ·
      refine ⟨16798591338544768465444565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11199060892363178976963043 16798591338544768465444565)
      ·
        refine ⟨393716984497143010908857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 16798591338544768465444565 393716984497143010908857)
        ·
          refine ⟨295287738372857258181643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 393716984497143010908857 295287738372857258181643)
          ·
            refine ⟨442931607559285887272465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295287738372857258181643 442931607559285887272465)
            ·
              refine ⟨332198705669464415454349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 442931607559285887272465 332198705669464415454349)
              ·
                refine ⟨124574514626049155795381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332198705669464415454349 124574514626049155795381)
                ·
                  rfl

theorem cell19_409401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 2, 3].length) (baseStart_409401 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409401 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409401 prefixEnd_409401 := by exact prefixLift 409401
  have htrace : WordTrace (prefixWord ++ tailWord_409401) baseStart_409401 baseEnd_409401 := by
    simpa [prefixWord, tailWord_409401, baseEnd_409401] using wordTrace_append hprefix tailTrace_409401
  have hstable : (prefixWord ++ tailWord_409401).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409401).length < 2 ^ (prefixWord ++ tailWord_409401).sum := by decide
  have hdescent : baseEnd_409401 < baseStart_409401 := by decide
  rcases family_descends (prefixWord ++ tailWord_409401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409405 : List Nat := [1, 4, 1, 4, 1, 1, 4, 3]
def baseStart_409405 : Nat := 118140960795 + 409405 * 2 ^ 59
def prefixEnd_409405 : Nat := 4983230072969 + 3 ^ 40 * 409405 * 2
def baseEnd_409405 : Nat := 124575731765378331706481

theorem tailTrace_409405 : CollatzResearch.WordTrace tailWord_409405 prefixEnd_409405 124575731765378331706481 := by
  unfold tailWord_409405
  simp only [CollatzResearch.WordTrace]
  refine ⟨14932227081803080652429669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9954818054535387101619779 14932227081803080652429669)
  ·
    refine ⟨2799792577838077622330563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14932227081803080652429669 2799792577838077622330563)
    ·
      refine ⟨4199688866757116433495845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2799792577838077622330563 4199688866757116433495845)
      ·
        refine ⟨787441662516959331280471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4199688866757116433495845 787441662516959331280471)
        ·
          refine ⟨1181162493775438996920707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787441662516959331280471 1181162493775438996920707)
          ·
            refine ⟨1771743740663158495381061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1181162493775438996920707 1771743740663158495381061)
            ·
              refine ⟨332201951374342217883949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1771743740663158495381061 332201951374342217883949)
              ·
                refine ⟨124575731765378331706481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332201951374342217883949 124575731765378331706481)
                ·
                  rfl

theorem cell19_409405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 3].length) (baseStart_409405 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409405 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409405 prefixEnd_409405 := by exact prefixLift 409405
  have htrace : WordTrace (prefixWord ++ tailWord_409405) baseStart_409405 baseEnd_409405 := by
    simpa [prefixWord, tailWord_409405, baseEnd_409405] using wordTrace_append hprefix tailTrace_409405
  have hstable : (prefixWord ++ tailWord_409405).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409405).length < 2 ^ (prefixWord ++ tailWord_409405).sum := by decide
  have hdescent : baseEnd_409405 < baseStart_409405 := by decide
  rcases family_descends (prefixWord ++ tailWord_409405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409407 : List Nat := [1, 1, 2, 2, 6, 1, 1, 5]
def baseStart_409407 : Nat := 118140960795 + 409407 * 2 ^ 59
def prefixEnd_409407 : Nat := 4983230072969 + 3 ^ 40 * 409407 * 2
def baseEnd_409407 : Nat := 124576340335042919662031

theorem tailTrace_409407 : CollatzResearch.WordTrace tailWord_409407 prefixEnd_409407 124576340335042919662031 := by
  unfold tailWord_409407
  simp only [CollatzResearch.WordTrace]
  refine ⟨14932300027795834994002475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9954866685197223329334983 14932300027795834994002475)
  ·
    refine ⟨22398450041693752491003713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14932300027795834994002475 22398450041693752491003713)
    ·
      refine ⟨16798837531270314368252785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22398450041693752491003713 16798837531270314368252785)
      ·
        refine ⟨12599128148452735776189589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16798837531270314368252785 12599128148452735776189589)
        ·
          refine ⟨590584131958721989508887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12599128148452735776189589 590584131958721989508887)
          ·
            refine ⟨885876197938082984263331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 590584131958721989508887 885876197938082984263331)
            ·
              refine ⟨1328814296907124476394997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 885876197938082984263331 1328814296907124476394997)
              ·
                refine ⟨124576340335042919662031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1328814296907124476394997 124576340335042919662031)
                ·
                  rfl

theorem cell19_409407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 1, 5].length) (baseStart_409407 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409407 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409407 prefixEnd_409407 := by exact prefixLift 409407
  have htrace : WordTrace (prefixWord ++ tailWord_409407) baseStart_409407 baseEnd_409407 := by
    simpa [prefixWord, tailWord_409407, baseEnd_409407] using wordTrace_append hprefix tailTrace_409407
  have hstable : (prefixWord ++ tailWord_409407).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409407).length < 2 ^ (prefixWord ++ tailWord_409407).sum := by decide
  have hdescent : baseEnd_409407 < baseStart_409407 := by decide
  rcases family_descends (prefixWord ++ tailWord_409407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409426 : List Nat := [3, 2, 2, 1, 1, 5, 5]
def baseStart_409426 : Nat := 118140960795 + 409426 * 2 ^ 59
def prefixEnd_409426 : Nat := 4983230072969 + 3 ^ 40 * 409426 * 2
def baseEnd_409426 : Nat := 41527373915618835079919

theorem tailTrace_409426 : CollatzResearch.WordTrace tailWord_409426 prefixEnd_409426 41527373915618835079919 := by
  unfold tailWord_409426
  simp only [CollatzResearch.WordTrace]
  refine ⟨3733248253681750309736033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9955328676484667492629421 3733248253681750309736033)
  ·
    refine ⟨2799936190261312732302025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3733248253681750309736033 2799936190261312732302025)
    ·
      refine ⟨2099952142695984549226519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2799936190261312732302025 2099952142695984549226519)
      ·
        refine ⟨3149928214043976823839779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2099952142695984549226519 3149928214043976823839779)
        ·
          refine ⟨4724892321065965235759669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3149928214043976823839779 4724892321065965235759669)
          ·
            refine ⟨442958655099934240852469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4724892321065965235759669 442958655099934240852469)
            ·
              refine ⟨41527373915618835079919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 442958655099934240852469 41527373915618835079919)
              ·
                rfl

theorem cell19_409426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 5].length) (baseStart_409426 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409426 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409426 prefixEnd_409426 := by exact prefixLift 409426
  have htrace : WordTrace (prefixWord ++ tailWord_409426) baseStart_409426 baseEnd_409426 := by
    simpa [prefixWord, tailWord_409426, baseEnd_409426] using wordTrace_append hprefix tailTrace_409426
  have hstable : (prefixWord ++ tailWord_409426).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409426).length < 2 ^ (prefixWord ++ tailWord_409426).sum := by decide
  have hdescent : baseEnd_409426 < baseStart_409426 := by decide
  rcases family_descends (prefixWord ++ tailWord_409426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409466 : List Nat := [3, 1, 1, 1, 1, 1, 6, 5]
def baseStart_409466 : Nat := 118140960795 + 409466 * 2 ^ 59
def prefixEnd_409466 : Nat := 4983230072969 + 3 ^ 40 * 409466 * 2
def baseEnd_409466 : Nat := 124594293140148264350759

theorem tailTrace_409466 : CollatzResearch.WordTrace tailWord_409466 prefixEnd_409466 124594293140148264350759 := by
  unfold tailWord_409466
  simp only [CollatzResearch.WordTrace]
  refine ⟨3733612983645522017600063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9956301289721392046933501 3733612983645522017600063)
  ·
    refine ⟨5600419475468283026400095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3733612983645522017600063 5600419475468283026400095)
    ·
      refine ⟨8400629213202424539600143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5600419475468283026400095 8400629213202424539600143)
      ·
        refine ⟨12600943819803636809400215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8400629213202424539600143 12600943819803636809400215)
        ·
          refine ⟨18901415729705455214100323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12600943819803636809400215 18901415729705455214100323)
          ·
            refine ⟨28352123594558182821150485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18901415729705455214100323 28352123594558182821150485)
            ·
              refine ⟨1329005793494914819741429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28352123594558182821150485 1329005793494914819741429)
              ·
                refine ⟨124594293140148264350759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1329005793494914819741429 124594293140148264350759)
                ·
                  rfl

theorem cell19_409466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_409466 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409466 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409466 prefixEnd_409466 := by exact prefixLift 409466
  have htrace : WordTrace (prefixWord ++ tailWord_409466) baseStart_409466 baseEnd_409466 := by
    simpa [prefixWord, tailWord_409466, baseEnd_409466] using wordTrace_append hprefix tailTrace_409466
  have hstable : (prefixWord ++ tailWord_409466).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409466).length < 2 ^ (prefixWord ++ tailWord_409466).sum := by decide
  have hdescent : baseEnd_409466 < baseStart_409466 := by decide
  rcases family_descends (prefixWord ++ tailWord_409466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409494 : List Nat := [5, 3, 1, 1, 3, 1, 1, 4]
def baseStart_409494 : Nat := 118140960795 + 409494 * 2 ^ 59
def prefixEnd_409494 : Nat := 4983230072969 + 3 ^ 40 * 409494 * 2
def baseEnd_409494 : Nat := 124602813115452495728461

theorem tailTrace_409494 : CollatzResearch.WordTrace tailWord_409494 prefixEnd_409494 124602813115452495728461 := by
  unfold tailWord_409494
  simp only [CollatzResearch.WordTrace]
  refine ⟨933467073655040553276221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9956982118987099234946357 933467073655040553276221)
  ·
    refine ⟨350050152620640207478583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 933467073655040553276221 350050152620640207478583)
    ·
      refine ⟨525075228930960311217875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 350050152620640207478583 525075228930960311217875)
      ·
        refine ⟨787612843396440466826813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 525075228930960311217875 787612843396440466826813)
        ·
          refine ⟨295354816273665175060055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 787612843396440466826813 295354816273665175060055)
          ·
            refine ⟨443032224410497762590083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295354816273665175060055 443032224410497762590083)
            ·
              refine ⟨664548336615746643885125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443032224410497762590083 664548336615746643885125)
              ·
                refine ⟨124602813115452495728461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 664548336615746643885125 124602813115452495728461)
                ·
                  rfl

theorem cell19_409494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_409494 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409494 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409494 prefixEnd_409494 := by exact prefixLift 409494
  have htrace : WordTrace (prefixWord ++ tailWord_409494) baseStart_409494 baseEnd_409494 := by
    simpa [prefixWord, tailWord_409494, baseEnd_409494] using wordTrace_append hprefix tailTrace_409494
  have hstable : (prefixWord ++ tailWord_409494).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409494).length < 2 ^ (prefixWord ++ tailWord_409494).sum := by decide
  have hdescent : baseEnd_409494 < baseStart_409494 := by decide
  rcases family_descends (prefixWord ++ tailWord_409494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409500 : List Nat := [2, 2, 3, 3, 1, 3, 1, 4]
def baseStart_409500 : Nat := 118140960795 + 409500 * 2 ^ 59
def prefixEnd_409500 : Nat := 4983230072969 + 3 ^ 40 * 409500 * 2
def baseEnd_409500 : Nat := 124604638824446259595111

theorem tailTrace_409500 : CollatzResearch.WordTrace tailWord_409500 prefixEnd_409500 124604638824446259595111 := by
  unfold tailWord_409500
  simp only [CollatzResearch.WordTrace]
  refine ⟨7467846008229455938568977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9957128010972607918091969 7467846008229455938568977)
  ·
    refine ⟨5600884506172091953926733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7467846008229455938568977 5600884506172091953926733)
    ·
      refine ⟨2100331689814534482722525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5600884506172091953926733 2100331689814534482722525)
      ·
        refine ⟨787624383680450431020947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2100331689814534482722525 787624383680450431020947)
        ·
          refine ⟨1181436575520675646531421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 787624383680450431020947 1181436575520675646531421)
          ·
            refine ⟨443038715820253367449283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1181436575520675646531421 443038715820253367449283)
            ·
              refine ⟨664558073730380051173925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443038715820253367449283 664558073730380051173925)
              ·
                refine ⟨124604638824446259595111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 664558073730380051173925 124604638824446259595111)
                ·
                  rfl

theorem cell19_409500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 3, 1, 4].length) (baseStart_409500 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409500 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409500 prefixEnd_409500 := by exact prefixLift 409500
  have htrace : WordTrace (prefixWord ++ tailWord_409500) baseStart_409500 baseEnd_409500 := by
    simpa [prefixWord, tailWord_409500, baseEnd_409500] using wordTrace_append hprefix tailTrace_409500
  have hstable : (prefixWord ++ tailWord_409500).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409500).length < 2 ^ (prefixWord ++ tailWord_409500).sum := by decide
  have hdescent : baseEnd_409500 < baseStart_409500 := by decide
  rcases family_descends (prefixWord ++ tailWord_409500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409637 : List Nat := [1, 3, 1, 2, 2, 3, 2, 5]
def baseStart_409637 : Nat := 118140960795 + 409637 * 2 ^ 59
def prefixEnd_409637 : Nat := 4983230072969 + 3 ^ 40 * 409637 * 2
def baseEnd_409637 : Nat := 124646325846470534550293

theorem tailTrace_409637 : CollatzResearch.WordTrace tailWord_409637 prefixEnd_409637 124646325846470534550293 := by
  unfold tailWord_409637
  simp only [CollatzResearch.WordTrace]
  refine ⟨14940688816962584274875165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9960459211308389516583443 14940688816962584274875165)
  ·
    refine ⟨5602758306360969103078187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14940688816962584274875165 5602758306360969103078187)
    ·
      refine ⟨8404137459541453654617281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5602758306360969103078187 8404137459541453654617281)
      ·
        refine ⟨6303103094656090240962961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8404137459541453654617281 6303103094656090240962961)
        ·
          refine ⟨4727327320992067680722221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6303103094656090240962961 4727327320992067680722221)
          ·
            refine ⟨1772747745372025380270833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4727327320992067680722221 1772747745372025380270833)
            ·
              refine ⟨1329560809029019035203125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1772747745372025380270833 1329560809029019035203125)
              ·
                refine ⟨124646325846470534550293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1329560809029019035203125 124646325846470534550293)
                ·
                  rfl

theorem cell19_409637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 5].length) (baseStart_409637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409637 prefixEnd_409637 := by exact prefixLift 409637
  have htrace : WordTrace (prefixWord ++ tailWord_409637) baseStart_409637 baseEnd_409637 := by
    simpa [prefixWord, tailWord_409637, baseEnd_409637] using wordTrace_append hprefix tailTrace_409637
  have hstable : (prefixWord ++ tailWord_409637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409637).length < 2 ^ (prefixWord ++ tailWord_409637).sum := by decide
  have hdescent : baseEnd_409637 < baseStart_409637 := by decide
  rcases family_descends (prefixWord ++ tailWord_409637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409652 : List Nat := [2, 5, 1, 2, 3, 6]
def baseStart_409652 : Nat := 118140960795 + 409652 * 2 ^ 59
def prefixEnd_409652 : Nat := 4983230072969 + 3 ^ 40 * 409652 * 2
def baseEnd_409652 : Nat := 13850098902106104912991

theorem tailTrace_409652 : CollatzResearch.WordTrace tailWord_409652 prefixEnd_409652 13850098902106104912991 := by
  unfold tailWord_409652
  simp only [CollatzResearch.WordTrace]
  refine ⟨7470617955954120918335605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9960823941272161224447473 7470617955954120918335605)
  ·
    refine ⟨700370433370698836093963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7470617955954120918335605 700370433370698836093963)
    ·
      refine ⟨1050555650056048254140945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 700370433370698836093963 1050555650056048254140945)
      ·
        refine ⟨787916737542036190605709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1050555650056048254140945 787916737542036190605709)
        ·
          refine ⟨295468776578263571477141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 787916737542036190605709 295468776578263571477141)
          ·
            refine ⟨13850098902106104912991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 295468776578263571477141 13850098902106104912991)
            ·
              rfl

theorem cell19_409652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 6].length) (baseStart_409652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409652 prefixEnd_409652 := by exact prefixLift 409652
  have htrace : WordTrace (prefixWord ++ tailWord_409652) baseStart_409652 baseEnd_409652 := by
    simpa [prefixWord, tailWord_409652, baseEnd_409652] using wordTrace_append hprefix tailTrace_409652
  have hstable : (prefixWord ++ tailWord_409652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409652).length < 2 ^ (prefixWord ++ tailWord_409652).sum := by decide
  have hdescent : baseEnd_409652 < baseStart_409652 := by decide
  rcases family_descends (prefixWord ++ tailWord_409652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409656 : List Nat := [2, 1, 2, 1, 6, 7]
def baseStart_409656 : Nat := 118140960795 + 409656 * 2 ^ 59
def prefixEnd_409656 : Nat := 4983230072969 + 3 ^ 40 * 409656 * 2
def baseEnd_409656 : Nat := 13850234139809346680891

theorem tailTrace_409656 : CollatzResearch.WordTrace tailWord_409656 prefixEnd_409656 13850234139809346680891 := by
  unfold tailWord_409656
  simp only [CollatzResearch.WordTrace]
  refine ⟨7470690901946875259908411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9960921202595833679877881 7470690901946875259908411)
  ·
    refine ⟨11206036352920312889862617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7470690901946875259908411 11206036352920312889862617)
    ·
      refine ⟨8404527264690234667396963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11206036352920312889862617 8404527264690234667396963)
      ·
        refine ⟨12606790897035352001095445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8404527264690234667396963 12606790897035352001095445)
        ·
          refine ⟨590943323298532125051349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12606790897035352001095445 590943323298532125051349)
          ·
            refine ⟨13850234139809346680891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 590943323298532125051349 13850234139809346680891)
            ·
              rfl

theorem cell19_409656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 7].length) (baseStart_409656 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409656 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409656 prefixEnd_409656 := by exact prefixLift 409656
  have htrace : WordTrace (prefixWord ++ tailWord_409656) baseStart_409656 baseEnd_409656 := by
    simpa [prefixWord, tailWord_409656, baseEnd_409656] using wordTrace_append hprefix tailTrace_409656
  have hstable : (prefixWord ++ tailWord_409656).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409656).length < 2 ^ (prefixWord ++ tailWord_409656).sum := by decide
  have hdescent : baseEnd_409656 < baseStart_409656 := by decide
  rcases family_descends (prefixWord ++ tailWord_409656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409732 : List Nat := [2, 3, 2, 1, 2, 1, 2, 6]
def baseStart_409732 : Nat := 118140960795 + 409732 * 2 ^ 59
def prefixEnd_409732 : Nat := 4983230072969 + 3 ^ 40 * 409732 * 2
def baseEnd_409732 : Nat := 124675232905538462438923

theorem tailTrace_409732 : CollatzResearch.WordTrace tailWord_409732 prefixEnd_409732 124675232905538462438923 := by
  unfold tailWord_409732
  simp only [CollatzResearch.WordTrace]
  refine ⟨7472076875809207749791725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9962769167745610333055633 7472076875809207749791725)
  ·
    refine ⟨2802028828428452906171897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7472076875809207749791725 2802028828428452906171897)
    ·
      refine ⟨2101521621321339679628923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2802028828428452906171897 2101521621321339679628923)
      ·
        refine ⟨3152282431982009519443385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2101521621321339679628923 3152282431982009519443385)
        ·
          refine ⟨2364211823986507139582539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3152282431982009519443385 2364211823986507139582539)
          ·
            refine ⟨3546317735979760709373809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2364211823986507139582539 3546317735979760709373809)
            ·
              refine ⟨2659738301984820532030357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3546317735979760709373809 2659738301984820532030357)
              ·
                refine ⟨124675232905538462438923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2659738301984820532030357 124675232905538462438923)
                ·
                  rfl

theorem cell19_409732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 6].length) (baseStart_409732 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409732 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409732 prefixEnd_409732 := by exact prefixLift 409732
  have htrace : WordTrace (prefixWord ++ tailWord_409732) baseStart_409732 baseEnd_409732 := by
    simpa [prefixWord, tailWord_409732, baseEnd_409732] using wordTrace_append hprefix tailTrace_409732
  have hstable : (prefixWord ++ tailWord_409732).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409732).length < 2 ^ (prefixWord ++ tailWord_409732).sum := by decide
  have hdescent : baseEnd_409732 < baseStart_409732 := by decide
  rcases family_descends (prefixWord ++ tailWord_409732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409827 : List Nat := [1, 1, 1, 8, 8]
def baseStart_409827 : Nat := 118140960795 + 409827 * 2 ^ 59
def prefixEnd_409827 : Nat := 4983230072969 + 3 ^ 40 * 409827 * 2
def baseEnd_409827 : Nat := 4618671850540977419539

theorem tailTrace_409827 : CollatzResearch.WordTrace tailWord_409827 prefixEnd_409827 4618671850540977419539 := by
  unfold tailWord_409827
  simp only [CollatzResearch.WordTrace]
  refine ⟨14947618686274246724291735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9965079124182831149527823 14947618686274246724291735)
  ·
    refine ⟨22421428029411370086437603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14947618686274246724291735 22421428029411370086437603)
    ·
      refine ⟨33632142044117055129656405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22421428029411370086437603 33632142044117055129656405)
      ·
        refine ⟨394126664579496739800661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 33632142044117055129656405 394126664579496739800661)
        ·
          refine ⟨4618671850540977419539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 394126664579496739800661 4618671850540977419539)
          ·
            rfl

theorem cell19_409827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 8].length) (baseStart_409827 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409827 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409827 prefixEnd_409827 := by exact prefixLift 409827
  have htrace : WordTrace (prefixWord ++ tailWord_409827) baseStart_409827 baseEnd_409827 := by
    simpa [prefixWord, tailWord_409827, baseEnd_409827] using wordTrace_append hprefix tailTrace_409827
  have hstable : (prefixWord ++ tailWord_409827).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409827).length < 2 ^ (prefixWord ++ tailWord_409827).sum := by decide
  have hdescent : baseEnd_409827 < baseStart_409827 := by decide
  rcases family_descends (prefixWord ++ tailWord_409827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409918 : List Nat := [4, 2, 1, 2, 1, 4, 2, 3]
def baseStart_409918 : Nat := 118140960795 + 409918 * 2 ^ 59
def prefixEnd_409918 : Nat := 4983230072969 + 3 ^ 40 * 409918 * 2
def baseEnd_409918 : Nat := 124731829884345142305083

theorem tailTrace_409918 : CollatzResearch.WordTrace tailWord_409918 prefixEnd_409918 124731829884345142305083 := by
  unfold tailWord_409918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1868867216118071158231801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9967291819296379510569605 1868867216118071158231801)
  ·
    refine ⟨1401650412088553368673851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1868867216118071158231801 1401650412088553368673851)
    ·
      refine ⟨2102475618132830053010777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1401650412088553368673851 2102475618132830053010777)
      ·
        refine ⟨1576856713599622539758083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2102475618132830053010777 1576856713599622539758083)
        ·
          refine ⟨2365285070399433809637125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1576856713599622539758083 2365285070399433809637125)
          ·
            refine ⟨443490950699893839306961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2365285070399433809637125 443490950699893839306961)
            ·
              refine ⟨332618213024920379480221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443490950699893839306961 332618213024920379480221)
              ·
                refine ⟨124731829884345142305083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332618213024920379480221 124731829884345142305083)
                ·
                  rfl

theorem cell19_409918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_409918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409918 prefixEnd_409918 := by exact prefixLift 409918
  have htrace : WordTrace (prefixWord ++ tailWord_409918) baseStart_409918 baseEnd_409918 := by
    simpa [prefixWord, tailWord_409918, baseEnd_409918] using wordTrace_append hprefix tailTrace_409918
  have hstable : (prefixWord ++ tailWord_409918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409918).length < 2 ^ (prefixWord ++ tailWord_409918).sum := by decide
  have hdescent : baseEnd_409918 < baseStart_409918 := by decide
  rcases family_descends (prefixWord ++ tailWord_409918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409960 : List Nat := [2, 1, 4, 2, 2, 1, 1, 6]
def baseStart_409960 : Nat := 118140960795 + 409960 * 2 ^ 59
def prefixEnd_409960 : Nat := 4983230072969 + 3 ^ 40 * 409960 * 2
def baseEnd_409960 : Nat := 124744609847301489371635

theorem tailTrace_409960 : CollatzResearch.WordTrace tailWord_409960 prefixEnd_409960 124744609847301489371635 := by
  unfold tailWord_409960
  simp only [CollatzResearch.WordTrace]
  refine ⟨7476234797396205219441667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9968313063194940292588889 7476234797396205219441667)
  ·
    refine ⟨11214352196094307829162501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7476234797396205219441667 11214352196094307829162501)
    ·
      refine ⟨2102691036767682717967969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11214352196094307829162501 2102691036767682717967969)
      ·
        refine ⟨1577018277575762038475977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2102691036767682717967969 1577018277575762038475977)
        ·
          refine ⟨1182763708181821528856983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1577018277575762038475977 1182763708181821528856983)
          ·
            refine ⟨1774145562272732293285475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1182763708181821528856983 1774145562272732293285475)
            ·
              refine ⟨2661218343409098439928213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1774145562272732293285475 2661218343409098439928213)
              ·
                refine ⟨124744609847301489371635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2661218343409098439928213 124744609847301489371635)
                ·
                  rfl

theorem cell19_409960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_409960 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409960 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409960 prefixEnd_409960 := by exact prefixLift 409960
  have htrace : WordTrace (prefixWord ++ tailWord_409960) baseStart_409960 baseEnd_409960 := by
    simpa [prefixWord, tailWord_409960, baseEnd_409960] using wordTrace_append hprefix tailTrace_409960
  have hstable : (prefixWord ++ tailWord_409960).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409960).length < 2 ^ (prefixWord ++ tailWord_409960).sum := by decide
  have hdescent : baseEnd_409960 < baseStart_409960 := by decide
  rcases family_descends (prefixWord ++ tailWord_409960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_409998 : List Nat := [4, 1, 1, 4, 1, 8]
def baseStart_409998 : Nat := 118140960795 + 409998 * 2 ^ 59
def prefixEnd_409998 : Nat := 4983230072969 + 3 ^ 40 * 409998 * 2
def baseEnd_409998 : Nat := 13861796963436517836343

theorem tailTrace_409998 : CollatzResearch.WordTrace tailWord_409998 prefixEnd_409998 13861796963436517836343 := by
  unfold tailWord_409998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1869231946081842866095831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9969237045769828619177765 1869231946081842866095831)
  ·
    refine ⟨2803847919122764299143747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1869231946081842866095831 2803847919122764299143747)
    ·
      refine ⟨4205771878684146448715621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2803847919122764299143747 4205771878684146448715621)
      ·
        refine ⟨788582227253277459134179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4205771878684146448715621 788582227253277459134179)
        ·
          refine ⟨1182873340879916188701269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 788582227253277459134179 1182873340879916188701269)
          ·
            refine ⟨13861796963436517836343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1182873340879916188701269 13861796963436517836343)
            ·
              rfl

theorem cell19_409998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 8].length) (baseStart_409998 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_409998 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_409998 prefixEnd_409998 := by exact prefixLift 409998
  have htrace : WordTrace (prefixWord ++ tailWord_409998) baseStart_409998 baseEnd_409998 := by
    simpa [prefixWord, tailWord_409998, baseEnd_409998] using wordTrace_append hprefix tailTrace_409998
  have hstable : (prefixWord ++ tailWord_409998).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_409998).length < 2 ^ (prefixWord ++ tailWord_409998).sum := by decide
  have hdescent : baseEnd_409998 < baseStart_409998 := by decide
  rcases family_descends (prefixWord ++ tailWord_409998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410013 : List Nat := [1, 4, 2, 1, 5, 1, 1, 4]
def baseStart_410013 : Nat := 118140960795 + 410013 * 2 ^ 59
def prefixEnd_410013 : Nat := 4983230072969 + 3 ^ 40 * 410013 * 2
def baseEnd_410013 : Nat := 124760736943413070193713

theorem tailTrace_410013 : CollatzResearch.WordTrace tailWord_410013 prefixEnd_410013 124760736943413070193713 := by
  unfold tailWord_410013
  simp only [CollatzResearch.WordTrace]
  refine ⟨14954402663600400490562693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9969601775733600327041795 14954402663600400490562693)
  ·
    refine ⟨2803950499425075091980505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14954402663600400490562693 2803950499425075091980505)
    ·
      refine ⟨2102962874568806318985379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2803950499425075091980505 2102962874568806318985379)
      ·
        refine ⟨3154444311853209478478069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2102962874568806318985379 3154444311853209478478069)
        ·
          refine ⟨295729154236238388607319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3154444311853209478478069 295729154236238388607319)
          ·
            refine ⟨443593731354357582910979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295729154236238388607319 443593731354357582910979)
            ·
              refine ⟨665390597031536374366469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443593731354357582910979 665390597031536374366469)
              ·
                refine ⟨124760736943413070193713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 665390597031536374366469 124760736943413070193713)
                ·
                  rfl

theorem cell19_410013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 4].length) (baseStart_410013 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410013 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410013 prefixEnd_410013 := by exact prefixLift 410013
  have htrace : WordTrace (prefixWord ++ tailWord_410013) baseStart_410013 baseEnd_410013 := by
    simpa [prefixWord, tailWord_410013, baseEnd_410013] using wordTrace_append hprefix tailTrace_410013
  have hstable : (prefixWord ++ tailWord_410013).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410013).length < 2 ^ (prefixWord ++ tailWord_410013).sum := by decide
  have hdescent : baseEnd_410013 < baseStart_410013 := by decide
  rcases family_descends (prefixWord ++ tailWord_410013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410180 : List Nat := [2, 3, 5, 1, 2, 1, 1, 4]
def baseStart_410180 : Nat := 118140960795 + 410180 * 2 ^ 59
def prefixEnd_410180 : Nat := 4983230072969 + 3 ^ 40 * 410180 * 2
def baseEnd_410180 : Nat := 124811552510406164482147

theorem tailTrace_410180 : CollatzResearch.WordTrace tailWord_410180 prefixEnd_410180 124811552510406164482147 := by
  unfold tailWord_410180
  simp only [CollatzResearch.WordTrace]
  refine ⟨7480246826997694005945997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9973662435996925341261329 7480246826997694005945997)
  ·
    refine ⟨2805092560124135252229749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7480246826997694005945997 2805092560124135252229749)
    ·
      refine ⟨262977427511637679896539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2805092560124135252229749 262977427511637679896539)
      ·
        refine ⟨394466141267456519844809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 262977427511637679896539 394466141267456519844809)
        ·
          refine ⟨295849605950592389883607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394466141267456519844809 295849605950592389883607)
          ·
            refine ⟨443774408925888584825411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295849605950592389883607 443774408925888584825411)
            ·
              refine ⟨665661613388832877238117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443774408925888584825411 665661613388832877238117)
              ·
                refine ⟨124811552510406164482147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 665661613388832877238117 124811552510406164482147)
                ·
                  rfl

theorem cell19_410180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 4].length) (baseStart_410180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410180 prefixEnd_410180 := by exact prefixLift 410180
  have htrace : WordTrace (prefixWord ++ tailWord_410180) baseStart_410180 baseEnd_410180 := by
    simpa [prefixWord, tailWord_410180, baseEnd_410180] using wordTrace_append hprefix tailTrace_410180
  have hstable : (prefixWord ++ tailWord_410180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410180).length < 2 ^ (prefixWord ++ tailWord_410180).sum := by decide
  have hdescent : baseEnd_410180 < baseStart_410180 := by decide
  rcases family_descends (prefixWord ++ tailWord_410180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410226 : List Nat := [3, 2, 1, 2, 4, 1, 6]
def baseStart_410226 : Nat := 118140960795 + 410226 * 2 ^ 59
def prefixEnd_410226 : Nat := 4983230072969 + 3 ^ 40 * 410226 * 2
def baseEnd_410226 : Nat := 41608516537563895819933

theorem tailTrace_410226 : CollatzResearch.WordTrace tailWord_410226 prefixEnd_410226 41608516537563895819933 := by
  unfold tailWord_410226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3740542852957184467016633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9974780941219158578711021 3740542852957184467016633)
  ·
    refine ⟨2805407139717888350262475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3740542852957184467016633 2805407139717888350262475)
    ·
      refine ⟨4208110709576832525393713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2805407139717888350262475 4208110709576832525393713)
      ·
        refine ⟨3156083032182624394045285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4208110709576832525393713 3156083032182624394045285)
        ·
          refine ⟨591765568534242073883491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3156083032182624394045285 591765568534242073883491)
          ·
            refine ⟨887648352801363110825237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 591765568534242073883491 887648352801363110825237)
            ·
              refine ⟨41608516537563895819933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 887648352801363110825237 41608516537563895819933)
              ·
                rfl

theorem cell19_410226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 6].length) (baseStart_410226 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410226 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410226 prefixEnd_410226 := by exact prefixLift 410226
  have htrace : WordTrace (prefixWord ++ tailWord_410226) baseStart_410226 baseEnd_410226 := by
    simpa [prefixWord, tailWord_410226, baseEnd_410226] using wordTrace_append hprefix tailTrace_410226
  have hstable : (prefixWord ++ tailWord_410226).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410226).length < 2 ^ (prefixWord ++ tailWord_410226).sum := by decide
  have hdescent : baseEnd_410226 < baseStart_410226 := by decide
  rcases family_descends (prefixWord ++ tailWord_410226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410247 : List Nat := [1, 1, 4, 2, 1, 2, 2, 6]
def baseStart_410247 : Nat := 118140960795 + 410247 * 2 ^ 59
def prefixEnd_410247 : Nat := 4983230072969 + 3 ^ 40 * 410247 * 2
def baseEnd_410247 : Nat := 124831939594169860993075

theorem tailTrace_410247 : CollatzResearch.WordTrace tailWord_410247 prefixEnd_410247 124831939594169860993075 := by
  unfold tailWord_410247
  simp only [CollatzResearch.WordTrace]
  refine ⟨14962937344752658454580995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9975291563168438969720663 14962937344752658454580995)
  ·
    refine ⟨22444406017128987681871493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14962937344752658454580995 22444406017128987681871493)
    ·
      refine ⟨4208326128211685190350905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22444406017128987681871493 4208326128211685190350905)
      ·
        refine ⟨3156244596158763892763179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4208326128211685190350905 3156244596158763892763179)
        ·
          refine ⟨4734366894238145839144769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3156244596158763892763179 4734366894238145839144769)
          ·
            refine ⟨3550775170678609379358577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4734366894238145839144769 3550775170678609379358577)
            ·
              refine ⟨2663081378008957034518933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3550775170678609379358577 2663081378008957034518933)
              ·
                refine ⟨124831939594169860993075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2663081378008957034518933 124831939594169860993075)
                ·
                  rfl

theorem cell19_410247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_410247 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410247 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410247 prefixEnd_410247 := by exact prefixLift 410247
  have htrace : WordTrace (prefixWord ++ tailWord_410247) baseStart_410247 baseEnd_410247 := by
    simpa [prefixWord, tailWord_410247, baseEnd_410247] using wordTrace_append hprefix tailTrace_410247
  have hstable : (prefixWord ++ tailWord_410247).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410247).length < 2 ^ (prefixWord ++ tailWord_410247).sum := by decide
  have hdescent : baseEnd_410247 < baseStart_410247 := by decide
  rcases family_descends (prefixWord ++ tailWord_410247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410260 : List Nat := [2, 4, 2, 2, 1, 3, 2, 3]
def baseStart_410260 : Nat := 118140960795 + 410260 * 2 ^ 59
def prefixEnd_410260 : Nat := 4983230072969 + 3 ^ 40 * 410260 * 2
def baseEnd_410260 : Nat := 124835895296989682704151

theorem tailTrace_410260 : CollatzResearch.WordTrace tailWord_410260 prefixEnd_410260 124835895296989682704151 := by
  unfold tailWord_410260
  simp only [CollatzResearch.WordTrace]
  refine ⟨7481705746852780837402117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9975607662470374449869489 7481705746852780837402117)
  ·
    refine ⟨1402819827534896407012897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7481705746852780837402117 1402819827534896407012897)
    ·
      refine ⟨1052114870651172305259673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1402819827534896407012897 1052114870651172305259673)
      ·
        refine ⟨789086152988379228944755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1052114870651172305259673 789086152988379228944755)
        ·
          refine ⟨1183629229482568843417133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789086152988379228944755 1183629229482568843417133)
          ·
            refine ⟨443860961055963316281425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1183629229482568843417133 443860961055963316281425)
            ·
              refine ⟨332895720791972487211069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 443860961055963316281425 332895720791972487211069)
              ·
                refine ⟨124835895296989682704151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332895720791972487211069 124835895296989682704151)
                ·
                  rfl

theorem cell19_410260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_410260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410260 prefixEnd_410260 := by exact prefixLift 410260
  have htrace : WordTrace (prefixWord ++ tailWord_410260) baseStart_410260 baseEnd_410260 := by
    simpa [prefixWord, tailWord_410260, baseEnd_410260] using wordTrace_append hprefix tailTrace_410260
  have hstable : (prefixWord ++ tailWord_410260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410260).length < 2 ^ (prefixWord ++ tailWord_410260).sum := by decide
  have hdescent : baseEnd_410260 < baseStart_410260 := by decide
  rcases family_descends (prefixWord ++ tailWord_410260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410279 : List Nat := [1, 1, 6, 3, 2, 1, 5]
def baseStart_410279 : Nat := 118140960795 + 410279 * 2 ^ 59
def prefixEnd_410279 : Nat := 4983230072969 + 3 ^ 40 * 410279 * 2
def baseEnd_410279 : Nat := 41613892236267756093959

theorem tailTrace_410279 : CollatzResearch.WordTrace tailWord_410279 prefixEnd_410279 41613892236267756093959 := by
  unfold tailWord_410279
  simp only [CollatzResearch.WordTrace]
  refine ⟨14964104480636727919745891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9976069653757818613163927 14964104480636727919745891)
  ·
    refine ⟨22446156720955091879618837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14964104480636727919745891 22446156720955091879618837)
    ·
      refine ⟨1052163596294769931857133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22446156720955091879618837 1052163596294769931857133)
      ·
        refine ⟨394561348610538724446425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1052163596294769931857133 394561348610538724446425)
        ·
          refine ⟨295921011457904043334819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394561348610538724446425 295921011457904043334819)
          ·
            refine ⟨443881517186856065002229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295921011457904043334819 443881517186856065002229)
            ·
              refine ⟨41613892236267756093959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 443881517186856065002229 41613892236267756093959)
              ·
                rfl

theorem cell19_410279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 5].length) (baseStart_410279 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410279 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410279 prefixEnd_410279 := by exact prefixLift 410279
  have htrace : WordTrace (prefixWord ++ tailWord_410279) baseStart_410279 baseEnd_410279 := by
    simpa [prefixWord, tailWord_410279, baseEnd_410279] using wordTrace_append hprefix tailTrace_410279
  have hstable : (prefixWord ++ tailWord_410279).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410279).length < 2 ^ (prefixWord ++ tailWord_410279).sum := by decide
  have hdescent : baseEnd_410279 < baseStart_410279 := by decide
  rcases family_descends (prefixWord ++ tailWord_410279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410302 : List Nat := [4, 2, 1, 1, 2, 1, 4, 4]
def baseStart_410302 : Nat := 118140960795 + 410302 * 2 ^ 59
def prefixEnd_410302 : Nat := 4983230072969 + 3 ^ 40 * 410302 * 2
def baseEnd_410302 : Nat := 124848675259946029770703

theorem tailTrace_410302 : CollatzResearch.WordTrace tailWord_410302 prefixEnd_410302 124848675259946029770703 := by
  unfold tailWord_410302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1870617919944175355979145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9976628906368935231888773 1870617919944175355979145)
  ·
    refine ⟨1402963439958131516984359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1870617919944175355979145 1402963439958131516984359)
    ·
      refine ⟨2104445159937197275476539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1402963439958131516984359 2104445159937197275476539)
      ·
        refine ⟨3156667739905795913214809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2104445159937197275476539 3156667739905795913214809)
        ·
          refine ⟨2367500804929346934911107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3156667739905795913214809 2367500804929346934911107)
          ·
            refine ⟨3551251207394020402366661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2367500804929346934911107 3551251207394020402366661)
            ·
              refine ⟨665859601386378825443749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3551251207394020402366661 665859601386378825443749)
              ·
                refine ⟨124848675259946029770703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 665859601386378825443749 124848675259946029770703)
                ·
                  rfl

theorem cell19_410302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_410302 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410302 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410302 prefixEnd_410302 := by exact prefixLift 410302
  have htrace : WordTrace (prefixWord ++ tailWord_410302) baseStart_410302 baseEnd_410302 := by
    simpa [prefixWord, tailWord_410302, baseEnd_410302] using wordTrace_append hprefix tailTrace_410302
  have hstable : (prefixWord ++ tailWord_410302).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410302).length < 2 ^ (prefixWord ++ tailWord_410302).sum := by decide
  have hdescent : baseEnd_410302 < baseStart_410302 := by decide
  rcases family_descends (prefixWord ++ tailWord_410302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410304 : List Nat := [2, 1, 1, 2, 4, 2, 1, 6]
def baseStart_410304 : Nat := 118140960795 + 410304 * 2 ^ 59
def prefixEnd_410304 : Nat := 4983230072969 + 3 ^ 40 * 410304 * 2
def baseEnd_410304 : Nat := 124849283829610617726253

theorem tailTrace_410304 : CollatzResearch.WordTrace tailWord_410304 prefixEnd_410304 124849283829610617726253 := by
  unfold tailWord_410304
  simp only [CollatzResearch.WordTrace]
  refine ⟨7482508152773078594702983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9976677537030771459603977 7482508152773078594702983)
  ·
    refine ⟨11223762229159617892054475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7482508152773078594702983 11223762229159617892054475)
    ·
      refine ⟨16835643343739426838081713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11223762229159617892054475 16835643343739426838081713)
      ·
        refine ⟨12626732507804570128561285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16835643343739426838081713 12626732507804570128561285)
        ·
          refine ⟨2367512345213356899105241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12626732507804570128561285 2367512345213356899105241)
          ·
            refine ⟨1775634258910017674328931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2367512345213356899105241 1775634258910017674328931)
            ·
              refine ⟨2663451388365026511493397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1775634258910017674328931 2663451388365026511493397)
              ·
                refine ⟨124849283829610617726253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2663451388365026511493397 124849283829610617726253)
                ·
                  rfl

theorem cell19_410304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 6].length) (baseStart_410304 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410304 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410304 prefixEnd_410304 := by exact prefixLift 410304
  have htrace : WordTrace (prefixWord ++ tailWord_410304) baseStart_410304 baseEnd_410304 := by
    simpa [prefixWord, tailWord_410304, baseEnd_410304] using wordTrace_append hprefix tailTrace_410304
  have hstable : (prefixWord ++ tailWord_410304).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410304).length < 2 ^ (prefixWord ++ tailWord_410304).sum := by decide
  have hdescent : baseEnd_410304 < baseStart_410304 := by decide
  rcases family_descends (prefixWord ++ tailWord_410304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410378 : List Nat := [3, 1, 2, 2, 1, 2, 5, 3]
def baseStart_410378 : Nat := 118140960795 + 410378 * 2 ^ 59
def prefixEnd_410378 : Nat := 4983230072969 + 3 ^ 40 * 410378 * 2
def baseEnd_410378 : Nat := 124871800907200372081607

theorem tailTrace_410378 : CollatzResearch.WordTrace tailWord_410378 prefixEnd_410378 124871800907200372081607 := by
  unfold tailWord_410378
  simp only [CollatzResearch.WordTrace]
  refine ⟨3741928826819516956899947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9978476871518711885066525 3741928826819516956899947)
  ·
    refine ⟨5612893240229275435349921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3741928826819516956899947 5612893240229275435349921)
    ·
      refine ⟨4209669930171956576512441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5612893240229275435349921 4209669930171956576512441)
      ·
        refine ⟨3157252447628967432384331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4209669930171956576512441 3157252447628967432384331)
        ·
          refine ⟨4735878671443451148576497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3157252447628967432384331 4735878671443451148576497)
          ·
            refine ⟨3551909003582588361432373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4735878671443451148576497 3551909003582588361432373)
            ·
              refine ⟨332991469085867658884285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3551909003582588361432373 332991469085867658884285)
              ·
                refine ⟨124871800907200372081607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332991469085867658884285 124871800907200372081607)
                ·
                  rfl

theorem cell19_410378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_410378 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410378 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410378 prefixEnd_410378 := by exact prefixLift 410378
  have htrace : WordTrace (prefixWord ++ tailWord_410378) baseStart_410378 baseEnd_410378 := by
    simpa [prefixWord, tailWord_410378, baseEnd_410378] using wordTrace_append hprefix tailTrace_410378
  have hstable : (prefixWord ++ tailWord_410378).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410378).length < 2 ^ (prefixWord ++ tailWord_410378).sum := by decide
  have hdescent : baseEnd_410378 < baseStart_410378 := by decide
  rcases family_descends (prefixWord ++ tailWord_410378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410399 : List Nat := [1, 1, 2, 4, 2, 3, 6]
def baseStart_410399 : Nat := 118140960795 + 410399 * 2 ^ 59
def prefixEnd_410399 : Nat := 4983230072969 + 3 ^ 40 * 410399 * 2
def baseEnd_410399 : Nat := 41626063629559515204961

theorem tailTrace_410399 : CollatzResearch.WordTrace tailWord_410399 prefixEnd_410399 41626063629559515204961 := by
  unfold tailWord_410399
  simp only [CollatzResearch.WordTrace]
  refine ⟨14968481240201988414114251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9978987493467992276076167 14968481240201988414114251)
  ·
    refine ⟨22452721860302982621171377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14968481240201988414114251 22452721860302982621171377)
    ·
      refine ⟨16839541395227236965878533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22452721860302982621171377 16839541395227236965878533)
      ·
        refine ⟨3157414011605106931102225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16839541395227236965878533 3157414011605106931102225)
        ·
          refine ⟨2368060508703830198326669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3157414011605106931102225 2368060508703830198326669)
          ·
            refine ⟨888022690763936324372501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2368060508703830198326669 888022690763936324372501)
            ·
              refine ⟨41626063629559515204961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 888022690763936324372501 41626063629559515204961)
              ·
                rfl

theorem cell19_410399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 6].length) (baseStart_410399 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410399 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410399 prefixEnd_410399 := by exact prefixLift 410399
  have htrace : WordTrace (prefixWord ++ tailWord_410399) baseStart_410399 baseEnd_410399 := by
    simpa [prefixWord, tailWord_410399, baseEnd_410399] using wordTrace_append hprefix tailTrace_410399
  have hstable : (prefixWord ++ tailWord_410399).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410399).length < 2 ^ (prefixWord ++ tailWord_410399).sum := by decide
  have hdescent : baseEnd_410399 < baseStart_410399 := by decide
  rcases family_descends (prefixWord ++ tailWord_410399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410418 : List Nat := [3, 2, 1, 1, 3, 1, 2, 6]
def baseStart_410418 : Nat := 118140960795 + 410418 * 2 ^ 59
def prefixEnd_410418 : Nat := 4983230072969 + 3 ^ 40 * 410418 * 2
def baseEnd_410418 : Nat := 124883972300492131192609

theorem tailTrace_410418 : CollatzResearch.WordTrace tailWord_410418 prefixEnd_410418 124883972300492131192609 := by
  unfold tailWord_410418
  simp only [CollatzResearch.WordTrace]
  refine ⟨3742293556783288664763977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9979449484755436439370605 3742293556783288664763977)
  ·
    refine ⟨2806720167587466498572983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3742293556783288664763977 2806720167587466498572983)
    ·
      refine ⟨4210080251381199747859475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2806720167587466498572983 4210080251381199747859475)
      ·
        refine ⟨6315120377071799621789213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4210080251381199747859475 6315120377071799621789213)
        ·
          refine ⟨2368170141401924858170955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6315120377071799621789213 2368170141401924858170955)
          ·
            refine ⟨3552255212102887287256433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2368170141401924858170955 3552255212102887287256433)
            ·
              refine ⟨2664191409077165465442325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3552255212102887287256433 2664191409077165465442325)
              ·
                refine ⟨124883972300492131192609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2664191409077165465442325 124883972300492131192609)
                ·
                  rfl

theorem cell19_410418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 6].length) (baseStart_410418 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410418 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410418 prefixEnd_410418 := by exact prefixLift 410418
  have htrace : WordTrace (prefixWord ++ tailWord_410418) baseStart_410418 baseEnd_410418 := by
    simpa [prefixWord, tailWord_410418, baseEnd_410418] using wordTrace_append hprefix tailTrace_410418
  have hstable : (prefixWord ++ tailWord_410418).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410418).length < 2 ^ (prefixWord ++ tailWord_410418).sum := by decide
  have hdescent : baseEnd_410418 < baseStart_410418 := by decide
  rcases family_descends (prefixWord ++ tailWord_410418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410433 : List Nat := [1, 2, 5, 3, 1, 1, 1, 5]
def baseStart_410433 : Nat := 118140960795 + 410433 * 2 ^ 59
def prefixEnd_410433 : Nat := 4983230072969 + 3 ^ 40 * 410433 * 2
def baseEnd_410433 : Nat := 124888536572976540859235

theorem tailTrace_410433 : CollatzResearch.WordTrace tailWord_410433 prefixEnd_410433 124888536572976540859235 := by
  unfold tailWord_410433
  simp only [CollatzResearch.WordTrace]
  refine ⟨14969721322078812220851953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9979814214719208147234635 14969721322078812220851953)
  ·
    refine ⟨11227290991559109165638965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14969721322078812220851953 11227290991559109165638965)
    ·
      refine ⟨1052558530458666484278653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11227290991559109165638965 1052558530458666484278653)
      ·
        refine ⟨394709448921999931604495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1052558530458666484278653 394709448921999931604495)
        ·
          refine ⟨592064173382999897406743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394709448921999931604495 592064173382999897406743)
          ·
            refine ⟨888096260074499846110115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592064173382999897406743 888096260074499846110115)
            ·
              refine ⟨1332144390111749769165173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888096260074499846110115 1332144390111749769165173)
              ·
                refine ⟨124888536572976540859235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1332144390111749769165173 124888536572976540859235)
                ·
                  rfl

theorem cell19_410433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 5].length) (baseStart_410433 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410433 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410433 prefixEnd_410433 := by exact prefixLift 410433
  have htrace : WordTrace (prefixWord ++ tailWord_410433) baseStart_410433 baseEnd_410433 := by
    simpa [prefixWord, tailWord_410433, baseEnd_410433] using wordTrace_append hprefix tailTrace_410433
  have hstable : (prefixWord ++ tailWord_410433).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410433).length < 2 ^ (prefixWord ++ tailWord_410433).sum := by decide
  have hdescent : baseEnd_410433 < baseStart_410433 := by decide
  rcases family_descends (prefixWord ++ tailWord_410433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410452 : List Nat := [2, 4, 1, 1, 5, 1, 5]
def baseStart_410452 : Nat := 118140960795 + 410452 * 2 ^ 59
def prefixEnd_410452 : Nat := 4983230072969 + 3 ^ 40 * 410452 * 2
def baseEnd_410452 : Nat := 41631439328263375478987

theorem tailTrace_410452 : CollatzResearch.WordTrace tailWord_410452 prefixEnd_410452 41631439328263375478987 := by
  unfold tailWord_410452
  simp only [CollatzResearch.WordTrace]
  refine ⟨7485207154504989232896805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9980276206006652310529073 7485207154504989232896805)
  ·
    refine ⟨1403476341469685481168151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7485207154504989232896805 1403476341469685481168151)
    ·
      refine ⟨2105214512204528221752227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1403476341469685481168151 2105214512204528221752227)
      ·
        refine ⟨3157821768306792332628341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2105214512204528221752227 3157821768306792332628341)
        ·
          refine ⟨296045790778761781183907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3157821768306792332628341 296045790778761781183907)
          ·
            refine ⟨444068686168142671775861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296045790778761781183907 444068686168142671775861)
            ·
              refine ⟨41631439328263375478987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 444068686168142671775861 41631439328263375478987)
              ·
                rfl

theorem cell19_410452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 5].length) (baseStart_410452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410452 prefixEnd_410452 := by exact prefixLift 410452
  have htrace : WordTrace (prefixWord ++ tailWord_410452) baseStart_410452 baseEnd_410452 := by
    simpa [prefixWord, tailWord_410452, baseEnd_410452] using wordTrace_append hprefix tailTrace_410452
  have hstable : (prefixWord ++ tailWord_410452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410452).length < 2 ^ (prefixWord ++ tailWord_410452).sum := by decide
  have hdescent : baseEnd_410452 < baseStart_410452 := by decide
  rcases family_descends (prefixWord ++ tailWord_410452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410530 : List Nat := [3, 3, 1, 2, 2, 1, 3, 4]
def baseStart_410530 : Nat := 118140960795 + 410530 * 2 ^ 59
def prefixEnd_410530 : Nat := 4983230072969 + 3 ^ 40 * 410530 * 2
def baseEnd_410530 : Nat := 124918052201709056703415

theorem tailTrace_410530 : CollatzResearch.WordTrace tailWord_410530 prefixEnd_410530 124918052201709056703415 := by
  unfold tailWord_410530
  simp only [CollatzResearch.WordTrace]
  refine ⟨3743314800681849446783261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9982172801818265191422029 3743314800681849446783261)
  ·
    refine ⟨1403743050255693542543723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3743314800681849446783261 1403743050255693542543723)
    ·
      refine ⟨2105614575383540313815585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1403743050255693542543723 2105614575383540313815585)
      ·
        refine ⟨1579210931537655235361689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2105614575383540313815585 1579210931537655235361689)
        ·
          refine ⟨1184408198653241426521267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1579210931537655235361689 1184408198653241426521267)
          ·
            refine ⟨1776612297979862139781901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184408198653241426521267 1776612297979862139781901)
            ·
              refine ⟨666229611742448302418213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1776612297979862139781901 666229611742448302418213)
              ·
                refine ⟨124918052201709056703415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 666229611742448302418213 124918052201709056703415)
                ·
                  rfl

theorem cell19_410530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_410530 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410530 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410530 prefixEnd_410530 := by exact prefixLift 410530
  have htrace : WordTrace (prefixWord ++ tailWord_410530) baseStart_410530 baseEnd_410530 := by
    simpa [prefixWord, tailWord_410530, baseEnd_410530] using wordTrace_append hprefix tailTrace_410530
  have hstable : (prefixWord ++ tailWord_410530).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410530).length < 2 ^ (prefixWord ++ tailWord_410530).sum := by decide
  have hdescent : baseEnd_410530 < baseStart_410530 := by decide
  rcases family_descends (prefixWord ++ tailWord_410530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410549 : List Nat := [1, 3, 3, 2, 1, 1, 5, 3]
def baseStart_410549 : Nat := 118140960795 + 410549 * 2 ^ 59
def prefixEnd_410549 : Nat := 4983230072969 + 3 ^ 40 * 410549 * 2
def baseEnd_410549 : Nat := 124923833613522642281141

theorem tailTrace_410549 : CollatzResearch.WordTrace tailWord_410549 prefixEnd_410549 124923833613522642281141 := by
  unfold tailWord_410549
  simp only [CollatzResearch.WordTrace]
  refine ⟨14973952189658564032074701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9982634793105709354716467 14973952189658564032074701)
  ·
    refine ⟨5615232071121961512028013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14973952189658564032074701 5615232071121961512028013)
    ·
      refine ⟨2105712026670735567010505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5615232071121961512028013 2105712026670735567010505)
      ·
        refine ⟨1579284020003051675257879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2105712026670735567010505 1579284020003051675257879)
        ·
          refine ⟨2368926030004577512886819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1579284020003051675257879 2368926030004577512886819)
          ·
            refine ⟨3553389045006866269330229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2368926030004577512886819 3553389045006866269330229)
            ·
              refine ⟨333130222969393712749709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3553389045006866269330229 333130222969393712749709)
              ·
                refine ⟨124923833613522642281141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333130222969393712749709 124923833613522642281141)
                ·
                  rfl

theorem cell19_410549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 5, 3].length) (baseStart_410549 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410549 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410549 prefixEnd_410549 := by exact prefixLift 410549
  have htrace : WordTrace (prefixWord ++ tailWord_410549) baseStart_410549 baseEnd_410549 := by
    simpa [prefixWord, tailWord_410549, baseEnd_410549] using wordTrace_append hprefix tailTrace_410549
  have hstable : (prefixWord ++ tailWord_410549).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410549).length < 2 ^ (prefixWord ++ tailWord_410549).sum := by decide
  have hdescent : baseEnd_410549 < baseStart_410549 := by decide
  rcases family_descends (prefixWord ++ tailWord_410549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410606 : List Nat := [4, 1, 2, 1, 4, 1, 1, 5]
def baseStart_410606 : Nat := 118140960795 + 410606 * 2 ^ 59
def prefixEnd_410606 : Nat := 4983230072969 + 3 ^ 40 * 410606 * 2
def baseEnd_410606 : Nat := 124941177848963399014319

theorem tailTrace_410606 : CollatzResearch.WordTrace tailWord_410606 prefixEnd_410606 124941177848963399014319 := by
  unfold tailWord_410606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1872003893806507845862459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9984020766968041844599781 1872003893806507845862459)
  ·
    refine ⟨2808005840709761768793689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1872003893806507845862459 2808005840709761768793689)
    ·
      refine ⟨2106004380532321326595267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2808005840709761768793689 2106004380532321326595267)
      ·
        refine ⟨3159006570798481989892901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2106004380532321326595267 3159006570798481989892901)
        ·
          refine ⟨592313732024715373104919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3159006570798481989892901 592313732024715373104919)
          ·
            refine ⟨888470598037073059657379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592313732024715373104919 888470598037073059657379)
            ·
              refine ⟨1332705897055609589486069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888470598037073059657379 1332705897055609589486069)
              ·
                refine ⟨124941177848963399014319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1332705897055609589486069 124941177848963399014319)
                ·
                  rfl

theorem cell19_410606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_410606 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410606 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410606 prefixEnd_410606 := by exact prefixLift 410606
  have htrace : WordTrace (prefixWord ++ tailWord_410606) baseStart_410606 baseEnd_410606 := by
    simpa [prefixWord, tailWord_410606, baseEnd_410606] using wordTrace_append hprefix tailTrace_410606
  have hstable : (prefixWord ++ tailWord_410606).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410606).length < 2 ^ (prefixWord ++ tailWord_410606).sum := by decide
  have hdescent : baseEnd_410606 < baseStart_410606 := by decide
  rcases family_descends (prefixWord ++ tailWord_410606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410663 : List Nat := [1, 1, 7, 1, 1, 1, 2, 5]
def baseStart_410663 : Nat := 118140960795 + 410663 * 2 ^ 59
def prefixEnd_410663 : Nat := 4983230072969 + 3 ^ 40 * 410663 * 2
def baseEnd_410663 : Nat := 124958522084404155747497

theorem tailTrace_410663 : CollatzResearch.WordTrace tailWord_410663 prefixEnd_410663 124958522084404155747497 := by
  unfold tailWord_410663
  simp only [CollatzResearch.WordTrace]
  refine ⟨14978110111245561501724643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9985406740830374334483095 14978110111245561501724643)
  ·
    refine ⟨22467165166868342252586965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14978110111245561501724643 22467165166868342252586965)
    ·
      refine ⟨526574183598476771545007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 22467165166868342252586965 526574183598476771545007)
      ·
        refine ⟨789861275397715157317511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526574183598476771545007 789861275397715157317511)
        ·
          refine ⟨1184791913096572735976267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 789861275397715157317511 1184791913096572735976267)
          ·
            refine ⟨1777187869644859103964401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1184791913096572735976267 1777187869644859103964401)
            ·
              refine ⟨1332890902233644327973301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1777187869644859103964401 1332890902233644327973301)
              ·
                refine ⟨124958522084404155747497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1332890902233644327973301 124958522084404155747497)
                ·
                  rfl

theorem cell19_410663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 5].length) (baseStart_410663 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410663 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410663 prefixEnd_410663 := by exact prefixLift 410663
  have htrace : WordTrace (prefixWord ++ tailWord_410663) baseStart_410663 baseEnd_410663 := by
    simpa [prefixWord, tailWord_410663, baseEnd_410663] using wordTrace_append hprefix tailTrace_410663
  have hstable : (prefixWord ++ tailWord_410663).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410663).length < 2 ^ (prefixWord ++ tailWord_410663).sum := by decide
  have hdescent : baseEnd_410663 < baseStart_410663 := by decide
  rcases family_descends (prefixWord ++ tailWord_410663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410667 : List Nat := [1, 1, 1, 1, 2, 1, 5, 7]
def baseStart_410667 : Nat := 118140960795 + 410667 * 2 ^ 59
def prefixEnd_410667 : Nat := 4983230072969 + 3 ^ 40 * 410667 * 2
def baseEnd_410667 : Nat := 124959739223733331658597

theorem tailTrace_410667 : CollatzResearch.WordTrace tailWord_410667 prefixEnd_410667 124959739223733331658597 := by
  unfold tailWord_410667
  simp only [CollatzResearch.WordTrace]
  refine ⟨14978256003231070184870255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9985504002154046789913503 14978256003231070184870255)
  ·
    refine ⟨22467384004846605277305383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14978256003231070184870255 22467384004846605277305383)
    ·
      refine ⟨33701076007269907915958075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22467384004846605277305383 33701076007269907915958075)
      ·
        refine ⟨50551614010904861873937113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33701076007269907915958075 50551614010904861873937113)
        ·
          refine ⟨37913710508178646405452835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50551614010904861873937113 37913710508178646405452835)
          ·
            refine ⟨56870565762267969608179253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37913710508178646405452835 56870565762267969608179253)
            ·
              refine ⟨5331615540212622150766805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56870565762267969608179253 5331615540212622150766805)
              ·
                refine ⟨124959739223733331658597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5331615540212622150766805 124959739223733331658597)
                ·
                  rfl

theorem cell19_410667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 7].length) (baseStart_410667 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410667 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410667 prefixEnd_410667 := by exact prefixLift 410667
  have htrace : WordTrace (prefixWord ++ tailWord_410667) baseStart_410667 baseEnd_410667 := by
    simpa [prefixWord, tailWord_410667, baseEnd_410667] using wordTrace_append hprefix tailTrace_410667
  have hstable : (prefixWord ++ tailWord_410667).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410667).length < 2 ^ (prefixWord ++ tailWord_410667).sum := by decide
  have hdescent : baseEnd_410667 < baseStart_410667 := by decide
  rcases family_descends (prefixWord ++ tailWord_410667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410701 : List Nat := [1, 6, 1, 1, 1, 2, 3, 4]
def baseStart_410701 : Nat := 118140960795 + 410701 * 2 ^ 59
def prefixEnd_410701 : Nat := 4983230072969 + 3 ^ 40 * 410701 * 2
def baseEnd_410701 : Nat := 124970084908031326902949

theorem tailTrace_410701 : CollatzResearch.WordTrace tailWord_410701 prefixEnd_410701 124970084908031326902949 := by
  unfold tailWord_410701
  simp only [CollatzResearch.WordTrace]
  refine ⟨14979496085107893991607957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9986330723405262661071971 14979496085107893991607957)
  ·
    refine ⟨702163878989432530856623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14979496085107893991607957 702163878989432530856623)
    ·
      refine ⟨1053245818484148796284935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 702163878989432530856623 1053245818484148796284935)
      ·
        refine ⟨1579868727726223194427403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1053245818484148796284935 1579868727726223194427403)
        ·
          refine ⟨2369803091589334791641105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1579868727726223194427403 2369803091589334791641105)
          ·
            refine ⟨1777352318692001093730829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2369803091589334791641105 1777352318692001093730829)
            ·
              refine ⟨666507119509500410149061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1777352318692001093730829 666507119509500410149061)
              ·
                refine ⟨124970084908031326902949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 666507119509500410149061 124970084908031326902949)
                ·
                  rfl

theorem cell19_410701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 4].length) (baseStart_410701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410701 prefixEnd_410701 := by exact prefixLift 410701
  have htrace : WordTrace (prefixWord ++ tailWord_410701) baseStart_410701 baseEnd_410701 := by
    simpa [prefixWord, tailWord_410701, baseEnd_410701] using wordTrace_append hprefix tailTrace_410701
  have hstable : (prefixWord ++ tailWord_410701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410701).length < 2 ^ (prefixWord ++ tailWord_410701).sum := by decide
  have hdescent : baseEnd_410701 < baseStart_410701 := by decide
  rcases family_descends (prefixWord ++ tailWord_410701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410743 : List Nat := [1, 1, 3, 1, 1, 4, 8]
def baseStart_410743 : Nat := 118140960795 + 410743 * 2 ^ 59
def prefixEnd_410743 : Nat := 4983230072969 + 3 ^ 40 * 410743 * 2
def baseEnd_410743 : Nat := 41660954956995891323167

theorem tailTrace_410743 : CollatzResearch.WordTrace tailWord_410743 prefixEnd_410743 41660954956995891323167 := by
  unfold tailWord_410743
  simp only [CollatzResearch.WordTrace]
  refine ⟨14981027950955735164636883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9987351967303823443091255 14981027950955735164636883)
  ·
    refine ⟨22471541926433602746955325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14981027950955735164636883 22471541926433602746955325)
    ·
      refine ⟨8426828222412601030108247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22471541926433602746955325 8426828222412601030108247)
      ·
        refine ⟨12640242333618901545162371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8426828222412601030108247 12640242333618901545162371)
        ·
          refine ⟨18960363500428352317743557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12640242333618901545162371 18960363500428352317743557)
          ·
            refine ⟨3555068156330316059576917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18960363500428352317743557 3555068156330316059576917)
            ·
              refine ⟨41660954956995891323167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3555068156330316059576917 41660954956995891323167)
              ·
                rfl

theorem cell19_410743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_410743 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410743 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410743 prefixEnd_410743 := by exact prefixLift 410743
  have htrace : WordTrace (prefixWord ++ tailWord_410743) baseStart_410743 baseEnd_410743 := by
    simpa [prefixWord, tailWord_410743, baseEnd_410743] using wordTrace_append hprefix tailTrace_410743
  have hstable : (prefixWord ++ tailWord_410743).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410743).length < 2 ^ (prefixWord ++ tailWord_410743).sum := by decide
  have hdescent : baseEnd_410743 < baseStart_410743 := by decide
  rcases family_descends (prefixWord ++ tailWord_410743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410855 : List Nat := [1, 1, 5, 3, 2, 7]
def baseStart_410855 : Nat := 118140960795 + 410855 * 2 ^ 59
def prefixEnd_410855 : Nat := 4983230072969 + 3 ^ 40 * 410855 * 2
def baseEnd_410855 : Nat := 13890771641356066608923

theorem tailTrace_410855 : CollatzResearch.WordTrace tailWord_410855 prefixEnd_410855 13890771641356066608923 := by
  unfold tailWord_410855
  simp only [CollatzResearch.WordTrace]
  refine ⟨14985112926549978292714019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9990075284366652195142679 14985112926549978292714019)
  ·
    refine ⟨22477669389824967439071029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14985112926549978292714019 22477669389824967439071029)
    ·
      refine ⟨2107281505296090697412909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22477669389824967439071029 2107281505296090697412909)
      ·
        refine ⟨790230564486034011529841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2107281505296090697412909 790230564486034011529841)
        ·
          refine ⟨592672923364525508647381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790230564486034011529841 592672923364525508647381)
          ·
            refine ⟨13890771641356066608923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 592672923364525508647381 13890771641356066608923)
            ·
              rfl

theorem cell19_410855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 7].length) (baseStart_410855 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410855 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410855 prefixEnd_410855 := by exact prefixLift 410855
  have htrace : WordTrace (prefixWord ++ tailWord_410855) baseStart_410855 baseEnd_410855 := by
    simpa [prefixWord, tailWord_410855, baseEnd_410855] using wordTrace_append hprefix tailTrace_410855
  have hstable : (prefixWord ++ tailWord_410855).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410855).length < 2 ^ (prefixWord ++ tailWord_410855).sum := by decide
  have hdescent : baseEnd_410855 < baseStart_410855 := by decide
  rcases family_descends (prefixWord ++ tailWord_410855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410912 : List Nat := [2, 1, 1, 5, 3, 1, 6]
def baseStart_410912 : Nat := 118140960795 + 410912 * 2 ^ 59
def prefixEnd_410912 : Nat := 4983230072969 + 3 ^ 40 * 410912 * 2
def baseEnd_410912 : Nat := 41678096335881785404495

theorem tailTrace_410912 : CollatzResearch.WordTrace tailWord_410912 prefixEnd_410912 41678096335881785404495 := by
  unfold tailWord_410912
  simp only [CollatzResearch.WordTrace]
  refine ⟨7493595943671738513769495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9991461258228984685025993 7493595943671738513769495)
  ·
    refine ⟨11240393915507607770654243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7493595943671738513769495 11240393915507607770654243)
    ·
      refine ⟨16860590873261411655981365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11240393915507607770654243 16860590873261411655981365)
      ·
        refine ⟨1580680394368257342748253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16860590873261411655981365 1580680394368257342748253)
        ·
          refine ⟨592755147888096503530595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1580680394368257342748253 592755147888096503530595)
          ·
            refine ⟨889132721832144755295893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592755147888096503530595 889132721832144755295893)
            ·
              refine ⟨41678096335881785404495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 889132721832144755295893 41678096335881785404495)
              ·
                rfl

theorem cell19_410912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 6].length) (baseStart_410912 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410912 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410912 prefixEnd_410912 := by exact prefixLift 410912
  have htrace : WordTrace (prefixWord ++ tailWord_410912) baseStart_410912 baseEnd_410912 := by
    simpa [prefixWord, tailWord_410912, baseEnd_410912] using wordTrace_append hprefix tailTrace_410912
  have hstable : (prefixWord ++ tailWord_410912).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410912).length < 2 ^ (prefixWord ++ tailWord_410912).sum := by decide
  have hdescent : baseEnd_410912 < baseStart_410912 := by decide
  rcases family_descends (prefixWord ++ tailWord_410912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410948 : List Nat := [2, 3, 4, 1, 1, 2, 1, 5]
def baseStart_410948 : Nat := 118140960795 + 410948 * 2 ^ 59
def prefixEnd_410948 : Nat := 4983230072969 + 3 ^ 40 * 410948 * 2
def baseEnd_410948 : Nat := 125045243261607939413387

theorem tailTrace_410948 : CollatzResearch.WordTrace tailWord_410948 prefixEnd_410948 125045243261607939413387 := by
  unfold tailWord_410948
  simp only [CollatzResearch.WordTrace]
  refine ⟨7494252457606527587924749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9992336610142036783899665 7494252457606527587924749)
  ·
    refine ⟨2810344671602447845471781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7494252457606527587924749 2810344671602447845471781)
    ·
      refine ⟨526939625925458971025959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2810344671602447845471781 526939625925458971025959)
      ·
        refine ⟨790409438888188456538939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 526939625925458971025959 790409438888188456538939)
        ·
          refine ⟨1185614158332282684808409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790409438888188456538939 1185614158332282684808409)
          ·
            refine ⟨889210618749212013606307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1185614158332282684808409 889210618749212013606307)
            ·
              refine ⟨1333815928123818020409461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889210618749212013606307 1333815928123818020409461)
              ·
                refine ⟨125045243261607939413387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1333815928123818020409461 125045243261607939413387)
                ·
                  rfl

theorem cell19_410948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 5].length) (baseStart_410948 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410948 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410948 prefixEnd_410948 := by exact prefixLift 410948
  have htrace : WordTrace (prefixWord ++ tailWord_410948) baseStart_410948 baseEnd_410948 := by
    simpa [prefixWord, tailWord_410948, baseEnd_410948] using wordTrace_append hprefix tailTrace_410948
  have hstable : (prefixWord ++ tailWord_410948).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410948).length < 2 ^ (prefixWord ++ tailWord_410948).sum := by decide
  have hdescent : baseEnd_410948 < baseStart_410948 := by decide
  rcases family_descends (prefixWord ++ tailWord_410948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410986 : List Nat := [3, 1, 3, 3, 2, 1, 2, 4]
def baseStart_410986 : Nat := 118140960795 + 410986 * 2 ^ 59
def prefixEnd_410986 : Nat := 4983230072969 + 3 ^ 40 * 410986 * 2
def baseEnd_410986 : Nat := 125056806085235110568839

theorem tailTrace_410986 : CollatzResearch.WordTrace tailWord_410986 prefixEnd_410986 125056806085235110568839 := by
  unfold tailWord_410986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3747472722268846916433203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9993260592716925110488541 3747472722268846916433203)
  ·
    refine ⟨5621209083403270374649805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3747472722268846916433203 5621209083403270374649805)
    ·
      refine ⟨2107953406276226390493677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5621209083403270374649805 2107953406276226390493677)
      ·
        refine ⟨790482527353584896435129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2107953406276226390493677 790482527353584896435129)
        ·
          refine ⟨592861895515188672326347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790482527353584896435129 592861895515188672326347)
          ·
            refine ⟨889292843272783008489521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592861895515188672326347 889292843272783008489521)
            ·
              refine ⟨666969632454587256367141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 889292843272783008489521 666969632454587256367141)
              ·
                refine ⟨125056806085235110568839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 666969632454587256367141 125056806085235110568839)
                ·
                  rfl

theorem cell19_410986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_410986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410986 prefixEnd_410986 := by exact prefixLift 410986
  have htrace : WordTrace (prefixWord ++ tailWord_410986) baseStart_410986 baseEnd_410986 := by
    simpa [prefixWord, tailWord_410986, baseEnd_410986] using wordTrace_append hprefix tailTrace_410986
  have hstable : (prefixWord ++ tailWord_410986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410986).length < 2 ^ (prefixWord ++ tailWord_410986).sum := by decide
  have hdescent : baseEnd_410986 < baseStart_410986 := by decide
  rcases family_descends (prefixWord ++ tailWord_410986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_410988 : List Nat := [2, 2, 1, 1, 5, 2, 2, 4]
def baseStart_410988 : Nat := 118140960795 + 410988 * 2 ^ 59
def prefixEnd_410988 : Nat := 4983230072969 + 3 ^ 40 * 410988 * 2
def baseEnd_410988 : Nat := 125057414654899698524389

theorem tailTrace_410988 : CollatzResearch.WordTrace tailWord_410988 prefixEnd_410988 125057414654899698524389 := by
  unfold tailWord_410988
  simp only [CollatzResearch.WordTrace]
  refine ⟨7494981917534071003652809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9993309223378761338203745 7494981917534071003652809)
  ·
    refine ⟨5621236438150553252739607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7494981917534071003652809 5621236438150553252739607)
    ·
      refine ⟨8431854657225829879109411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5621236438150553252739607 8431854657225829879109411)
      ·
        refine ⟨12647781985838744818664117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8431854657225829879109411 12647781985838744818664117)
        ·
          refine ⟨1185729561172382326749761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12647781985838744818664117 1185729561172382326749761)
          ·
            refine ⟨889297170879286745062321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1185729561172382326749761 889297170879286745062321)
            ·
              refine ⟨666972878159465058796741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 889297170879286745062321 666972878159465058796741)
              ·
                refine ⟨125057414654899698524389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 666972878159465058796741 125057414654899698524389)
                ·
                  rfl

theorem cell19_410988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_410988 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_410988 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_410988 prefixEnd_410988 := by exact prefixLift 410988
  have htrace : WordTrace (prefixWord ++ tailWord_410988) baseStart_410988 baseEnd_410988 := by
    simpa [prefixWord, tailWord_410988, baseEnd_410988] using wordTrace_append hprefix tailTrace_410988
  have hstable : (prefixWord ++ tailWord_410988).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_410988).length < 2 ^ (prefixWord ++ tailWord_410988).sum := by decide
  have hdescent : baseEnd_410988 < baseStart_410988 := by decide
  rcases family_descends (prefixWord ++ tailWord_410988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411026 : List Nat := [3, 2, 3, 3, 8]
def baseStart_411026 : Nat := 118140960795 + 411026 * 2 ^ 59
def prefixEnd_411026 : Nat := 4983230072969 + 3 ^ 40 * 411026 * 2
def baseEnd_411026 : Nat := 4632184351056550728883

theorem tailTrace_411026 : CollatzResearch.WordTrace tailWord_411026 prefixEnd_411026 4632184351056550728883 := by
  unfold tailWord_411026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3747837452232618624297233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9994233205953649664792621 3747837452232618624297233)
  ·
    refine ⟨2810878089174463968222925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3747837452232618624297233 2810878089174463968222925)
    ·
      refine ⟨1054079283440423988083597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2810878089174463968222925 1054079283440423988083597)
      ·
        refine ⟨395279731290158995531349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1054079283440423988083597 395279731290158995531349)
        ·
          refine ⟨4632184351056550728883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 395279731290158995531349 4632184351056550728883)
          ·
            rfl

theorem cell19_411026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 8].length) (baseStart_411026 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411026 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411026 prefixEnd_411026 := by exact prefixLift 411026
  have htrace : WordTrace (prefixWord ++ tailWord_411026) baseStart_411026 baseEnd_411026 := by
    simpa [prefixWord, tailWord_411026, baseEnd_411026] using wordTrace_append hprefix tailTrace_411026
  have hstable : (prefixWord ++ tailWord_411026).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411026).length < 2 ^ (prefixWord ++ tailWord_411026).sum := by decide
  have hdescent : baseEnd_411026 < baseStart_411026 := by decide
  rcases family_descends (prefixWord ++ tailWord_411026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411117 : List Nat := [1, 5, 1, 3, 2, 2, 2, 3]
def baseStart_411117 : Nat := 118140960795 + 411117 * 2 ^ 59
def prefixEnd_411117 : Nat := 4983230072969 + 3 ^ 40 * 411117 * 2
def baseEnd_411117 : Nat := 125096667398265621657371

theorem tailTrace_411117 : CollatzResearch.WordTrace tailWord_411117 prefixEnd_411117 125096667398265621657371 := by
  unfold tailWord_411117
  simp only [CollatzResearch.WordTrace]
  refine ⟨14994668851600797038751605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9996445901067198025834403 14994668851600797038751605)
  ·
    refine ⟨1405750204837574722382963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14994668851600797038751605 1405750204837574722382963)
    ·
      refine ⟨2108625307256362083574445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1405750204837574722382963 2108625307256362083574445)
      ·
        refine ⟨790734490221135781340417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2108625307256362083574445 790734490221135781340417)
        ·
          refine ⟨593050867665851836005313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 790734490221135781340417 593050867665851836005313)
          ·
            refine ⟨444788150749388877003985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 593050867665851836005313 444788150749388877003985)
            ·
              refine ⟨333591113062041657752989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444788150749388877003985 333591113062041657752989)
              ·
                refine ⟨125096667398265621657371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333591113062041657752989 125096667398265621657371)
                ·
                  rfl

theorem cell19_411117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 2, 3].length) (baseStart_411117 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411117 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411117 prefixEnd_411117 := by exact prefixLift 411117
  have htrace : WordTrace (prefixWord ++ tailWord_411117) baseStart_411117 baseEnd_411117 := by
    simpa [prefixWord, tailWord_411117, baseEnd_411117] using wordTrace_append hprefix tailTrace_411117
  have hstable : (prefixWord ++ tailWord_411117).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411117).length < 2 ^ (prefixWord ++ tailWord_411117).sum := by decide
  have hdescent : baseEnd_411117 < baseStart_411117 := by decide
  rcases family_descends (prefixWord ++ tailWord_411117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411121 : List Nat := [1, 2, 2, 2, 3, 2, 4, 3]
def baseStart_411121 : Nat := 118140960795 + 411121 * 2 ^ 59
def prefixEnd_411121 : Nat := 4983230072969 + 3 ^ 40 * 411121 * 2
def baseEnd_411121 : Nat := 125097884537594797568471

theorem tailTrace_411121 : CollatzResearch.WordTrace tailWord_411121 prefixEnd_411121 125097884537594797568471 := by
  unfold tailWord_411121
  simp only [CollatzResearch.WordTrace]
  refine ⟨14994814743586305721897217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9996543162390870481264811 14994814743586305721897217)
  ·
    refine ⟨11246111057689729291422913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14994814743586305721897217 11246111057689729291422913)
    ·
      refine ⟨8434583293267296968567185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11246111057689729291422913 8434583293267296968567185)
      ·
        refine ⟨6325937469950472726425389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8434583293267296968567185 6325937469950472726425389)
        ·
          refine ⟨2372226551231427272409521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6325937469950472726425389 2372226551231427272409521)
          ·
            refine ⟨1779169913423570454307141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2372226551231427272409521 1779169913423570454307141)
            ·
              refine ⟨333594358766919460182589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1779169913423570454307141 333594358766919460182589)
              ·
                refine ⟨125097884537594797568471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333594358766919460182589 125097884537594797568471)
                ·
                  rfl

theorem cell19_411121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 4, 3].length) (baseStart_411121 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411121 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411121 prefixEnd_411121 := by exact prefixLift 411121
  have htrace : WordTrace (prefixWord ++ tailWord_411121) baseStart_411121 baseEnd_411121 := by
    simpa [prefixWord, tailWord_411121, baseEnd_411121] using wordTrace_append hprefix tailTrace_411121
  have hstable : (prefixWord ++ tailWord_411121).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411121).length < 2 ^ (prefixWord ++ tailWord_411121).sum := by decide
  have hdescent : baseEnd_411121 < baseStart_411121 := by decide
  rcases family_descends (prefixWord ++ tailWord_411121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411138 : List Nat := [3, 4, 1, 2, 1, 3, 5]
def baseStart_411138 : Nat := 118140960795 + 411138 * 2 ^ 59
def prefixEnd_411138 : Nat := 4983230072969 + 3 ^ 40 * 411138 * 2
def baseEnd_411138 : Nat := 41701019126581265063549

theorem tailTrace_411138 : CollatzResearch.WordTrace tailWord_411138 prefixEnd_411138 41701019126581265063549 := by
  unfold tailWord_411138
  simp only [CollatzResearch.WordTrace]
  refine ⟨3748858696131179406316517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9996956523016478416844045 3748858696131179406316517)
  ·
    refine ⟨702911005524596138684347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3748858696131179406316517 702911005524596138684347)
    ·
      refine ⟨1054366508286894208026521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 702911005524596138684347 1054366508286894208026521)
      ·
        refine ⟨790774881215170656019891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1054366508286894208026521 790774881215170656019891)
        ·
          refine ⟨1186162321822755984029837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 790774881215170656019891 1186162321822755984029837)
          ·
            refine ⟨444810870683533494011189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1186162321822755984029837 444810870683533494011189)
            ·
              refine ⟨41701019126581265063549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 444810870683533494011189 41701019126581265063549)
              ·
                rfl

theorem cell19_411138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 5].length) (baseStart_411138 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411138 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411138 prefixEnd_411138 := by exact prefixLift 411138
  have htrace : WordTrace (prefixWord ++ tailWord_411138) baseStart_411138 baseEnd_411138 := by
    simpa [prefixWord, tailWord_411138, baseEnd_411138] using wordTrace_append hprefix tailTrace_411138
  have hstable : (prefixWord ++ tailWord_411138).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411138).length < 2 ^ (prefixWord ++ tailWord_411138).sum := by decide
  have hdescent : baseEnd_411138 < baseStart_411138 := by decide
  rcases family_descends (prefixWord ++ tailWord_411138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411197 : List Nat := [1, 4, 1, 3, 4, 6]
def baseStart_411197 : Nat := 118140960795 + 411197 * 2 ^ 59
def prefixEnd_411197 : Nat := 4983230072969 + 3 ^ 40 * 411197 * 2
def baseEnd_411197 : Nat := 13902334464983237764375

theorem tailTrace_411197 : CollatzResearch.WordTrace tailWord_411197 prefixEnd_411197 13902334464983237764375 := by
  unfold tailWord_411197
  simp only [CollatzResearch.WordTrace]
  refine ⟨14997586691310970701663845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9998391127540647134442563 14997586691310970701663845)
  ·
    refine ⟨2812047504620807006561971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14997586691310970701663845 2812047504620807006561971)
    ·
      refine ⟨4218071256931210509842957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2812047504620807006561971 4218071256931210509842957)
      ·
        refine ⟨1581776721349203941191109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4218071256931210509842957 1581776721349203941191109)
        ·
          refine ⟨296583135252975738973333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1581776721349203941191109 296583135252975738973333)
          ·
            refine ⟨13902334464983237764375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 296583135252975738973333 13902334464983237764375)
            ·
              rfl

theorem cell19_411197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 6].length) (baseStart_411197 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411197 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411197 prefixEnd_411197 := by exact prefixLift 411197
  have htrace : WordTrace (prefixWord ++ tailWord_411197) baseStart_411197 baseEnd_411197 := by
    simpa [prefixWord, tailWord_411197, baseEnd_411197] using wordTrace_append hprefix tailTrace_411197
  have hstable : (prefixWord ++ tailWord_411197).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411197).length < 2 ^ (prefixWord ++ tailWord_411197).sum := by decide
  have hdescent : baseEnd_411197 < baseStart_411197 := by decide
  rcases family_descends (prefixWord ++ tailWord_411197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411235 : List Nat := [1, 1, 1, 5, 1, 4, 3, 3]
def baseStart_411235 : Nat := 118140960795 + 411235 * 2 ^ 59
def prefixEnd_411235 : Nat := 4983230072969 + 3 ^ 40 * 411235 * 2
def baseEnd_411235 : Nat := 125132573008476311034827

theorem tailTrace_411235 : CollatzResearch.WordTrace tailWord_411235 prefixEnd_411235 125132573008476311034827 := by
  unfold tailWord_411235
  simp only [CollatzResearch.WordTrace]
  refine ⟨14998972665173303191547159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9999315110115535461031439 14998972665173303191547159)
  ·
    refine ⟨22498458997759954787320739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14998972665173303191547159 22498458997759954787320739)
    ·
      refine ⟨33747688496639932180981109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22498458997759954787320739 33747688496639932180981109)
      ·
        refine ⟨3163845796559993641966979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33747688496639932180981109 3163845796559993641966979)
        ·
          refine ⟨4745768694839990462950469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3163845796559993641966979 4745768694839990462950469)
          ·
            refine ⟨889831630282498211803213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4745768694839990462950469 889831630282498211803213)
            ·
              refine ⟨333686861355936829426205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 889831630282498211803213 333686861355936829426205)
              ·
                refine ⟨125132573008476311034827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333686861355936829426205 125132573008476311034827)
                ·
                  rfl

theorem cell19_411235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 3].length) (baseStart_411235 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411235 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411235 prefixEnd_411235 := by exact prefixLift 411235
  have htrace : WordTrace (prefixWord ++ tailWord_411235) baseStart_411235 baseEnd_411235 := by
    simpa [prefixWord, tailWord_411235, baseEnd_411235] using wordTrace_append hprefix tailTrace_411235
  have hstable : (prefixWord ++ tailWord_411235).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411235).length < 2 ^ (prefixWord ++ tailWord_411235).sum := by decide
  have hdescent : baseEnd_411235 < baseStart_411235 := by decide
  rcases family_descends (prefixWord ++ tailWord_411235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411254 : List Nat := [5, 1, 1, 2, 2, 2, 6]
def baseStart_411254 : Nat := 118140960795 + 411254 * 2 ^ 59
def prefixEnd_411254 : Nat := 4983230072969 + 3 ^ 40 * 411254 * 2
def baseEnd_411254 : Nat := 41712784806763298870851

theorem tailTrace_411254 : CollatzResearch.WordTrace tailWord_411254 prefixEnd_411254 41712784806763298870851 := by
  unfold tailWord_411254
  simp only [CollatzResearch.WordTrace]
  refine ⟨937479103256529339780551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9999777101402979624325877 937479103256529339780551)
  ·
    refine ⟨1406218654884794009670827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 937479103256529339780551 1406218654884794009670827)
    ·
      refine ⟨2109327982327191014506241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1406218654884794009670827 2109327982327191014506241)
      ·
        refine ⟨1581995986745393260879681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2109327982327191014506241 1581995986745393260879681)
        ·
          refine ⟨1186496990059044945659761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1581995986745393260879681 1186496990059044945659761)
          ·
            refine ⟨889872742544283709244821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1186496990059044945659761 889872742544283709244821)
            ·
              refine ⟨41712784806763298870851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 889872742544283709244821 41712784806763298870851)
              ·
                rfl

theorem cell19_411254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 6].length) (baseStart_411254 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411254 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411254 prefixEnd_411254 := by exact prefixLift 411254
  have htrace : WordTrace (prefixWord ++ tailWord_411254) baseStart_411254 baseEnd_411254 := by
    simpa [prefixWord, tailWord_411254, baseEnd_411254] using wordTrace_append hprefix tailTrace_411254
  have hstable : (prefixWord ++ tailWord_411254).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411254).length < 2 ^ (prefixWord ++ tailWord_411254).sum := by decide
  have hdescent : baseEnd_411254 < baseStart_411254 := by decide
  rcases family_descends (prefixWord ++ tailWord_411254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_411292 : List Nat := [2, 2, 3, 2, 3, 1, 1, 5]
def baseStart_411292 : Nat := 118140960795 + 411292 * 2 ^ 59
def prefixEnd_411292 : Nat := 4983230072969 + 3 ^ 40 * 411292 * 2
def baseEnd_411292 : Nat := 125149917243917067768005

theorem tailTrace_411292 : CollatzResearch.WordTrace tailWord_411292 prefixEnd_411292 125149917243917067768005 := by
  unfold tailWord_411292
  simp only [CollatzResearch.WordTrace]
  refine ⟨7500525812983400963186065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10000701083977867950914753 7500525812983400963186065)
  ·
    refine ⟨5625394359737550722389549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7500525812983400963186065 5625394359737550722389549)
    ·
      refine ⟨2109522884901581520896081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5625394359737550722389549 2109522884901581520896081)
      ·
        refine ⟨1582142163676186140672061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2109522884901581520896081 1582142163676186140672061)
        ·
          refine ⟨593303311378569802752023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1582142163676186140672061 593303311378569802752023)
          ·
            refine ⟨889954967067854704128035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 593303311378569802752023 889954967067854704128035)
            ·
              refine ⟨1334932450601782056192053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 889954967067854704128035 1334932450601782056192053)
              ·
                refine ⟨125149917243917067768005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1334932450601782056192053 125149917243917067768005)
                ·
                  rfl

theorem cell19_411292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_411292 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_411292 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_411292 prefixEnd_411292 := by exact prefixLift 411292
  have htrace : WordTrace (prefixWord ++ tailWord_411292) baseStart_411292 baseEnd_411292 := by
    simpa [prefixWord, tailWord_411292, baseEnd_411292] using wordTrace_append hprefix tailTrace_411292
  have hstable : (prefixWord ++ tailWord_411292).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_411292).length < 2 ^ (prefixWord ++ tailWord_411292).sum := by decide
  have hdescent : baseEnd_411292 < baseStart_411292 := by decide
  rcases family_descends (prefixWord ++ tailWord_411292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
