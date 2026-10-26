import V185TrunkScan23Chunk0921

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5457089 : List Nat := [1, 2, 6, 1, 1, 3, 2, 2, 5]
def baseStart_5457089 : Nat := 118140960795 + 5457089 * 2 ^ 59
def prefixEnd_5457089 : Nat := 4983230072969 + 3 ^ 40 * 5457089 * 2
def baseEnd_5457089 : Nat := 311345514595944983098979

theorem tailTrace_5457089 : CollatzResearch.WordTrace tailWord_5457089 prefixEnd_5457089 311345514595944983098979 := by
  unfold tailWord_5457089
  simp only [CollatzResearch.WordTrace]
  refine ⟨199036387326906024446270321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132690924884604016297513547 199036387326906024446270321)
  ·
    refine ⟨149277290495179518334702741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199036387326906024446270321 149277290495179518334702741)
    ·
      refine ⟨6997372991961539921939191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 149277290495179518334702741 6997372991961539921939191)
      ·
        refine ⟨10496059487942309882908787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6997372991961539921939191 10496059487942309882908787)
        ·
          refine ⟨15744089231913464824363181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10496059487942309882908787 15744089231913464824363181)
          ·
            refine ⟨5904033461967549309136193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15744089231913464824363181 5904033461967549309136193)
            ·
              refine ⟨4428025096475661981852145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5904033461967549309136193 4428025096475661981852145)
              ·
                refine ⟨3321018822356746486389109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4428025096475661981852145 3321018822356746486389109)
                ·
                  refine ⟨311345514595944983098979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3321018822356746486389109 311345514595944983098979)
                  ·
                    rfl

theorem cell23_5457089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 2, 5].length) (baseStart_5457089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457089 prefixEnd_5457089 := by exact prefixLift 5457089
  have htrace : WordTrace (prefixWord ++ tailWord_5457089) baseStart_5457089 baseEnd_5457089 := by
    simpa [prefixWord, tailWord_5457089, baseEnd_5457089] using wordTrace_append hprefix tailTrace_5457089
  have hstable : (prefixWord ++ tailWord_5457089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457089).length < 2 ^ (prefixWord ++ tailWord_5457089).sum := by decide
  have hdescent : baseEnd_5457089 < baseStart_5457089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457125 : List Nat := [1, 3, 1, 4, 3, 1, 1, 1, 1, 4, 3]
def baseStart_5457125 : Nat := 118140960795 + 5457125 * 2 ^ 59
def prefixEnd_5457125 : Nat := 4983230072969 + 3 ^ 40 * 5457125 * 2
def baseEnd_5457125 : Nat := 2802128116667066707040645

theorem tailTrace_5457125 : CollatzResearch.WordTrace tailWord_5457125 prefixEnd_5457125 2802128116667066707040645 := by
  unfold tailWord_5457125
  simp only [CollatzResearch.WordTrace]
  refine ⟨199037700354775602594580829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132691800236517068396387219 199037700354775602594580829)
  ·
    refine ⟨74639137633040850972967811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199037700354775602594580829 74639137633040850972967811)
    ·
      refine ⟨111958706449561276459451717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74639137633040850972967811 111958706449561276459451717)
      ·
        refine ⟨20992257459292739336147197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111958706449561276459451717 20992257459292739336147197)
        ·
          refine ⟨7872096547234777251055199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20992257459292739336147197 7872096547234777251055199)
          ·
            refine ⟨11808144820852165876582799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7872096547234777251055199 11808144820852165876582799)
            ·
              refine ⟨17712217231278248814874199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11808144820852165876582799 17712217231278248814874199)
              ·
                refine ⟨26568325846917373222311299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17712217231278248814874199 26568325846917373222311299)
                ·
                  refine ⟨39852488770376059833466949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26568325846917373222311299 39852488770376059833466949)
                  ·
                    refine ⟨7472341644445511218775053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39852488770376059833466949 7472341644445511218775053)
                    ·
                      refine ⟨2802128116667066707040645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7472341644445511218775053 2802128116667066707040645)
                      ·
                        rfl

theorem cell23_5457125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_5457125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457125 prefixEnd_5457125 := by exact prefixLift 5457125
  have htrace : WordTrace (prefixWord ++ tailWord_5457125) baseStart_5457125 baseEnd_5457125 := by
    simpa [prefixWord, tailWord_5457125, baseEnd_5457125] using wordTrace_append hprefix tailTrace_5457125
  have hstable : (prefixWord ++ tailWord_5457125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457125).length < 2 ^ (prefixWord ++ tailWord_5457125).sum := by decide
  have hdescent : baseEnd_5457125 < baseStart_5457125 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457132 : List Nat := [2, 2, 1, 1, 2, 5, 2, 3, 1, 4]
def baseStart_5457132 : Nat := 118140960795 + 5457132 * 2 ^ 59
def prefixEnd_5457132 : Nat := 4983230072969 + 3 ^ 40 * 5457132 * 2
def baseEnd_5457132 : Nat := 934043903677216059884371

theorem tailTrace_5457132 : CollatzResearch.WordTrace tailWord_5457132 prefixEnd_5457132 934043903677216059884371 := by
  unfold tailWord_5457132
  simp only [CollatzResearch.WordTrace]
  refine ⟨99518977832875121395042825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132691970443833495193390433 99518977832875121395042825)
  ·
    refine ⟨74639233374656341046282119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99518977832875121395042825 74639233374656341046282119)
    ·
      refine ⟨111958850061984511569423179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74639233374656341046282119 111958850061984511569423179)
      ·
        refine ⟨167938275092976767354134769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111958850061984511569423179 167938275092976767354134769)
        ·
          refine ⟨125953706319732575515601077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167938275092976767354134769 125953706319732575515601077)
          ·
            refine ⟨11808159967474928954587601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125953706319732575515601077 11808159967474928954587601)
            ·
              refine ⟨8856119975606196715940701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11808159967474928954587601 8856119975606196715940701)
              ·
                refine ⟨3321044990852323768477763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8856119975606196715940701 3321044990852323768477763)
                ·
                  refine ⟨4981567486278485652716645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321044990852323768477763 4981567486278485652716645)
                  ·
                    refine ⟨934043903677216059884371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4981567486278485652716645 934043903677216059884371)
                    ·
                      rfl

theorem cell23_5457132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 3, 1, 4].length) (baseStart_5457132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457132 prefixEnd_5457132 := by exact prefixLift 5457132
  have htrace : WordTrace (prefixWord ++ tailWord_5457132) baseStart_5457132 baseEnd_5457132 := by
    simpa [prefixWord, tailWord_5457132, baseEnd_5457132] using wordTrace_append hprefix tailTrace_5457132
  have hstable : (prefixWord ++ tailWord_5457132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457132).length < 2 ^ (prefixWord ++ tailWord_5457132).sum := by decide
  have hdescent : baseEnd_5457132 < baseStart_5457132 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457155 : List Nat := [1, 1, 1, 3, 2, 4, 1, 3, 3, 1, 3]
def baseStart_5457155 : Nat := 118140960795 + 5457155 * 2 ^ 59
def prefixEnd_5457155 : Nat := 4983230072969 + 3 ^ 40 * 5457155 * 2
def baseEnd_5457155 : Nat := 2802143521086701589665507

theorem tailTrace_5457155 : CollatzResearch.WordTrace tailWord_5457155 prefixEnd_5457155 2802143521086701589665507 := by
  unfold tailWord_5457155
  simp only [CollatzResearch.WordTrace]
  refine ⟨199038794544666917718172919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132692529696444611812115279 199038794544666917718172919)
  ·
    refine ⟨298558191817000376577259379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199038794544666917718172919 298558191817000376577259379)
    ·
      refine ⟨447837287725500564865889069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298558191817000376577259379 447837287725500564865889069)
      ·
        refine ⟨167938982897062711824708401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 447837287725500564865889069 167938982897062711824708401)
        ·
          refine ⟨125954237172797033868531301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167938982897062711824708401 125954237172797033868531301)
          ·
            refine ⟨23616419469899443850349619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125954237172797033868531301 23616419469899443850349619)
            ·
              refine ⟨35424629204849165775524429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23616419469899443850349619 35424629204849165775524429)
              ·
                refine ⟨13284235951818437165821661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35424629204849165775524429 13284235951818437165821661)
                ·
                  refine ⟨4981588481931913937183123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13284235951818437165821661 4981588481931913937183123)
                  ·
                    refine ⟨7472382722897870905774685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4981588481931913937183123 7472382722897870905774685)
                    ·
                      refine ⟨2802143521086701589665507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7472382722897870905774685 2802143521086701589665507)
                      ·
                        rfl

theorem cell23_5457155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 3, 3, 1, 3].length) (baseStart_5457155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457155 prefixEnd_5457155 := by exact prefixLift 5457155
  have htrace : WordTrace (prefixWord ++ tailWord_5457155) baseStart_5457155 baseEnd_5457155 := by
    simpa [prefixWord, tailWord_5457155, baseEnd_5457155] using wordTrace_append hprefix tailTrace_5457155
  have hstable : (prefixWord ++ tailWord_5457155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457155).length < 2 ^ (prefixWord ++ tailWord_5457155).sum := by decide
  have hdescent : baseEnd_5457155 < baseStart_5457155 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457175 : List Nat := [1, 1, 3, 4, 1, 1, 4, 2, 1, 5]
def baseStart_5457175 : Nat := 118140960795 + 5457175 * 2 ^ 59
def prefixEnd_5457175 : Nat := 4983230072969 + 3 ^ 40 * 5457175 * 2
def baseEnd_5457175 : Nat := 934051263566597170471805

theorem tailTrace_5457175 : CollatzResearch.WordTrace tailWord_5457175 prefixEnd_5457175 934051263566597170471805 := by
  unfold tailWord_5457175
  simp only [CollatzResearch.WordTrace]
  refine ⟨199039524004594461133900979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132693016003062974089267319 199039524004594461133900979)
  ·
    refine ⟨298559286006891691700851469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199039524004594461133900979 298559286006891691700851469)
    ·
      refine ⟨111959732252584384387819301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298559286006891691700851469 111959732252584384387819301)
      ·
        refine ⟨20992449797359572072716119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111959732252584384387819301 20992449797359572072716119)
        ·
          refine ⟨31488674696039358109074179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20992449797359572072716119 31488674696039358109074179)
          ·
            refine ⟨47233012044059037163611269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31488674696039358109074179 47233012044059037163611269)
            ·
              refine ⟨8856189758261069468177113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47233012044059037163611269 8856189758261069468177113)
              ·
                refine ⟨6642142318695802101132835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8856189758261069468177113 6642142318695802101132835)
                ·
                  refine ⟨9963213478043703151699253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6642142318695802101132835 9963213478043703151699253)
                  ·
                    refine ⟨934051263566597170471805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9963213478043703151699253 934051263566597170471805)
                    ·
                      rfl

theorem cell23_5457175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 5].length) (baseStart_5457175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457175 prefixEnd_5457175 := by exact prefixLift 5457175
  have htrace : WordTrace (prefixWord ++ tailWord_5457175) baseStart_5457175 baseEnd_5457175 := by
    simpa [prefixWord, tailWord_5457175, baseEnd_5457175] using wordTrace_append hprefix tailTrace_5457175
  have hstable : (prefixWord ++ tailWord_5457175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457175).length < 2 ^ (prefixWord ++ tailWord_5457175).sum := by decide
  have hdescent : baseEnd_5457175 < baseStart_5457175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457188 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 3, 6]
def baseStart_5457188 : Nat := 118140960795 + 5457188 * 2 ^ 59
def prefixEnd_5457188 : Nat := 4983230072969 + 3 ^ 40 * 5457188 * 2
def baseEnd_5457188 : Nat := 934053488649433320184285

theorem tailTrace_5457188 : CollatzResearch.WordTrace tailWord_5457188 prefixEnd_5457188 934053488649433320184285 := by
  unfold tailWord_5457188
  simp only [CollatzResearch.WordTrace]
  refine ⟨99519999076773682177062109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132693332102364909569416145 99519999076773682177062109)
  ·
    refine ⟨37319999653790130816398291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99519999076773682177062109 37319999653790130816398291)
    ·
      refine ⟨55979999480685196224597437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37319999653790130816398291 55979999480685196224597437)
      ·
        refine ⟨20992499805256948584224039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55979999480685196224597437 20992499805256948584224039)
        ·
          refine ⟨31488749707885422876336059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20992499805256948584224039 31488749707885422876336059)
          ·
            refine ⟨47233124561828134314504089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31488749707885422876336059 47233124561828134314504089)
            ·
              refine ⟨35424843421371100735878067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47233124561828134314504089 35424843421371100735878067)
              ·
                refine ⟨53137265132056651103817101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35424843421371100735878067 53137265132056651103817101)
                ·
                  refine ⟨19926474424521244163931413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53137265132056651103817101 19926474424521244163931413)
                  ·
                    refine ⟨934053488649433320184285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19926474424521244163931413 934053488649433320184285)
                    ·
                      rfl

theorem cell23_5457188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_5457188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457188 prefixEnd_5457188 := by exact prefixLift 5457188
  have htrace : WordTrace (prefixWord ++ tailWord_5457188) baseStart_5457188 baseEnd_5457188 := by
    simpa [prefixWord, tailWord_5457188, baseEnd_5457188] using wordTrace_append hprefix tailTrace_5457188
  have hstable : (prefixWord ++ tailWord_5457188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457188).length < 2 ^ (prefixWord ++ tailWord_5457188).sum := by decide
  have hdescent : baseEnd_5457188 < baseStart_5457188 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457189 : List Nat := [1, 3, 1, 2, 4, 1, 3, 3, 1, 1, 3]
def baseStart_5457189 : Nat := 118140960795 + 5457189 * 2 ^ 59
def prefixEnd_5457189 : Nat := 4983230072969 + 3 ^ 40 * 5457189 * 2
def baseEnd_5457189 : Nat := 2802160979428954456640351

theorem tailTrace_5457189 : CollatzResearch.WordTrace tailWord_5457189 prefixEnd_5457189 2802160979428954456640351 := by
  unfold tailWord_5457189
  simp only [CollatzResearch.WordTrace]
  refine ⟨199040034626543741524910621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132693356417695827683273747 199040034626543741524910621)
  ·
    refine ⟨74640012984953903071841483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199040034626543741524910621 74640012984953903071841483)
    ·
      refine ⟨111960019477430854607762225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74640012984953903071841483 111960019477430854607762225)
      ·
        refine ⟨83970014608073140955821669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111960019477430854607762225 83970014608073140955821669)
        ·
          refine ⟨15744377739013713929216563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83970014608073140955821669 15744377739013713929216563)
          ·
            refine ⟨23616566608520570893824845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15744377739013713929216563 23616566608520570893824845)
            ·
              refine ⟨8856212478195214085184317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23616566608520570893824845 8856212478195214085184317)
              ·
                refine ⟨3321079679323205281944119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8856212478195214085184317 3321079679323205281944119)
                ·
                  refine ⟨4981619518984807922916179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321079679323205281944119 4981619518984807922916179)
                  ·
                    refine ⟨7472429278477211884374269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4981619518984807922916179 7472429278477211884374269)
                    ·
                      refine ⟨2802160979428954456640351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7472429278477211884374269 2802160979428954456640351)
                      ·
                        rfl

theorem cell23_5457189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 3, 3, 1, 1, 3].length) (baseStart_5457189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457189 prefixEnd_5457189 := by exact prefixLift 5457189
  have htrace : WordTrace (prefixWord ++ tailWord_5457189) baseStart_5457189 baseEnd_5457189 := by
    simpa [prefixWord, tailWord_5457189, baseEnd_5457189] using wordTrace_append hprefix tailTrace_5457189
  have hstable : (prefixWord ++ tailWord_5457189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457189).length < 2 ^ (prefixWord ++ tailWord_5457189).sum := by decide
  have hdescent : baseEnd_5457189 < baseStart_5457189 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457205 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 4, 4]
def baseStart_5457205 : Nat := 118140960795 + 5457205 * 2 ^ 59
def prefixEnd_5457205 : Nat := 4983230072969 + 3 ^ 40 * 5457205 * 2
def baseEnd_5457205 : Nat := 934056398373142131346759

theorem tailTrace_5457205 : CollatzResearch.WordTrace tailWord_5457205 prefixEnd_5457205 934056398373142131346759 := by
  unfold tailWord_5457205
  simp only [CollatzResearch.WordTrace]
  refine ⟨199040618194485776257493069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132693745462990517504995379 199040618194485776257493069)
  ·
    refine ⟨74640231822932166096559901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199040618194485776257493069 74640231822932166096559901)
    ·
      refine ⟨27990086933599562286209963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74640231822932166096559901 27990086933599562286209963)
      ·
        refine ⟨41985130400399343429314945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27990086933599562286209963 41985130400399343429314945)
        ·
          refine ⟨31488847800299507571986209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41985130400399343429314945 31488847800299507571986209)
          ·
            refine ⟨23616635850224630678989657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31488847800299507571986209 23616635850224630678989657)
            ·
              refine ⟨17712476887668473009242243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23616635850224630678989657 17712476887668473009242243)
              ·
                refine ⟨26568715331502709513863365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17712476887668473009242243 26568715331502709513863365)
                ·
                  refine ⟨4981634124656758033849381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26568715331502709513863365 4981634124656758033849381)
                  ·
                    refine ⟨934056398373142131346759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4981634124656758033849381 934056398373142131346759)
                    ·
                      rfl

theorem cell23_5457205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_5457205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457205 prefixEnd_5457205 := by exact prefixLift 5457205
  have htrace : WordTrace (prefixWord ++ tailWord_5457205) baseStart_5457205 baseEnd_5457205 := by
    simpa [prefixWord, tailWord_5457205, baseEnd_5457205] using wordTrace_append hprefix tailTrace_5457205
  have hstable : (prefixWord ++ tailWord_5457205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457205).length < 2 ^ (prefixWord ++ tailWord_5457205).sum := by decide
  have hdescent : baseEnd_5457205 < baseStart_5457205 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457229 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_5457229 : Nat := 118140960795 + 5457229 * 2 ^ 59
def prefixEnd_5457229 : Nat := 4983230072969 + 3 ^ 40 * 5457229 * 2
def baseEnd_5457229 : Nat := 2802181518655134300140167

theorem tailTrace_5457229 : CollatzResearch.WordTrace tailWord_5457229 prefixEnd_5457229 2802181518655134300140167 := by
  unfold tailWord_5457229
  simp only [CollatzResearch.WordTrace]
  refine ⟨199041493546398828356366741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132694329030932552237577827 199041493546398828356366741)
  ·
    refine ⟨9330070009987445079204691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 199041493546398828356366741 9330070009987445079204691)
    ·
      refine ⟨13995105014981167618807037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9330070009987445079204691 13995105014981167618807037)
      ·
        refine ⟨5248164380617937857052639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13995105014981167618807037 5248164380617937857052639)
        ·
          refine ⟨7872246570926906785578959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5248164380617937857052639 7872246570926906785578959)
          ·
            refine ⟨11808369856390360178368439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7872246570926906785578959 11808369856390360178368439)
            ·
              refine ⟨17712554784585540267552659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11808369856390360178368439 17712554784585540267552659)
              ·
                refine ⟨26568832176878310401328989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17712554784585540267552659 26568832176878310401328989)
                ·
                  refine ⟨9963312066329366400498371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26568832176878310401328989 9963312066329366400498371)
                  ·
                    refine ⟨14944968099494049600747557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9963312066329366400498371 14944968099494049600747557)
                    ·
                      refine ⟨2802181518655134300140167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14944968099494049600747557 2802181518655134300140167)
                      ·
                        rfl

theorem cell23_5457229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_5457229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457229 prefixEnd_5457229 := by exact prefixLift 5457229
  have htrace : WordTrace (prefixWord ++ tailWord_5457229) baseStart_5457229 baseEnd_5457229 := by
    simpa [prefixWord, tailWord_5457229, baseEnd_5457229] using wordTrace_append hprefix tailTrace_5457229
  have hstable : (prefixWord ++ tailWord_5457229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457229).length < 2 ^ (prefixWord ++ tailWord_5457229).sum := by decide
  have hdescent : baseEnd_5457229 < baseStart_5457229 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457319 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 4, 2, 2]
def baseStart_5457319 : Nat := 118140960795 + 5457319 * 2 ^ 59
def prefixEnd_5457319 : Nat := 4983230072969 + 3 ^ 40 * 5457319 * 2
def baseEnd_5457319 : Nat := 2802227731914038948014753

theorem tailTrace_5457319 : CollatzResearch.WordTrace tailWord_5457319 prefixEnd_5457319 2802227731914038948014753 := by
  unfold tailWord_5457319
  simp only [CollatzResearch.WordTrace]
  refine ⟨199044776116072773727143011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132696517410715182484762007 199044776116072773727143011)
  ·
    refine ⟨298567164174109160590714517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199044776116072773727143011 298567164174109160590714517)
    ·
      refine ⟨13995335820661366902689743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 298567164174109160590714517 13995335820661366902689743)
      ·
        refine ⟨20993003730992050354034615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13995335820661366902689743 20993003730992050354034615)
        ·
          refine ⟨31489505596488075531051923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20993003730992050354034615 31489505596488075531051923)
          ·
            refine ⟨47234258394732113296577885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31489505596488075531051923 47234258394732113296577885)
            ·
              refine ⟨17712846898024542486216707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47234258394732113296577885 17712846898024542486216707)
              ·
                refine ⟨26569270347036813729325061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17712846898024542486216707 26569270347036813729325061)
                ·
                  refine ⟨4981738190069402574248449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26569270347036813729325061 4981738190069402574248449)
                  ·
                    refine ⟨3736303642552051930686337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4981738190069402574248449 3736303642552051930686337)
                    ·
                      refine ⟨2802227731914038948014753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3736303642552051930686337 2802227731914038948014753)
                      ·
                        rfl

theorem cell23_5457319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_5457319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457319 prefixEnd_5457319 := by exact prefixLift 5457319
  have htrace : WordTrace (prefixWord ++ tailWord_5457319) baseStart_5457319 baseEnd_5457319 := by
    simpa [prefixWord, tailWord_5457319, baseEnd_5457319] using wordTrace_append hprefix tailTrace_5457319
  have hstable : (prefixWord ++ tailWord_5457319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457319).length < 2 ^ (prefixWord ++ tailWord_5457319).sum := by decide
  have hdescent : baseEnd_5457319 < baseStart_5457319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457335 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 3]
def baseStart_5457335 : Nat := 118140960795 + 5457335 * 2 ^ 59
def prefixEnd_5457335 : Nat := 4983230072969 + 3 ^ 40 * 5457335 * 2
def baseEnd_5457335 : Nat := 2802235947604510885414679

theorem tailTrace_5457335 : CollatzResearch.WordTrace tailWord_5457335 prefixEnd_5457335 2802235947604510885414679 := by
  unfold tailWord_5457335
  simp only [CollatzResearch.WordTrace]
  refine ⟨199045359684014808459725459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132696906456009872306483639 199045359684014808459725459)
  ·
    refine ⟨298568039526022212689588189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199045359684014808459725459 298568039526022212689588189)
    ·
      refine ⟨111963014822258329758595571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298568039526022212689588189 111963014822258329758595571)
      ·
        refine ⟨167944522233387494637893357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111963014822258329758595571 167944522233387494637893357)
        ·
          refine ⟨62979195837520310489210009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167944522233387494637893357 62979195837520310489210009)
          ·
            refine ⟨47234396878140232866907507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62979195837520310489210009 47234396878140232866907507)
            ·
              refine ⟨70851595317210349300361261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47234396878140232866907507 70851595317210349300361261)
              ·
                refine ⟨26569348243953880987635473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70851595317210349300361261 26569348243953880987635473)
                ·
                  refine ⟨19927011182965410740726605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26569348243953880987635473 19927011182965410740726605)
                  ·
                    refine ⟨7472629193612029027772477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19927011182965410740726605 7472629193612029027772477)
                    ·
                      refine ⟨2802235947604510885414679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7472629193612029027772477 2802235947604510885414679)
                      ·
                        rfl

theorem cell23_5457335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_5457335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457335 prefixEnd_5457335 := by exact prefixLift 5457335
  have htrace : WordTrace (prefixWord ++ tailWord_5457335) baseStart_5457335 baseEnd_5457335 := by
    simpa [prefixWord, tailWord_5457335, baseEnd_5457335] using wordTrace_append hprefix tailTrace_5457335
  have hstable : (prefixWord ++ tailWord_5457335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457335).length < 2 ^ (prefixWord ++ tailWord_5457335).sum := by decide
  have hdescent : baseEnd_5457335 < baseStart_5457335 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457365 : List Nat := [1, 3, 2, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_5457365 : Nat := 118140960795 + 5457365 * 2 ^ 59
def prefixEnd_5457365 : Nat := 4983230072969 + 3 ^ 40 * 5457365 * 2
def baseEnd_5457365 : Nat := 2802251352024145768039541

theorem tailTrace_5457365 : CollatzResearch.WordTrace tailWord_5457365 prefixEnd_5457365 2802251352024145768039541 := by
  unfold tailWord_5457365
  simp only [CollatzResearch.WordTrace]
  refine ⟨199046453873906123583317549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132697635915937415722211699 199046453873906123583317549)
  ·
    refine ⟨74642420202714796343744081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199046453873906123583317549 74642420202714796343744081)
    ·
      refine ⟨55981815152036097257808061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74642420202714796343744081 55981815152036097257808061)
      ·
        refine ⟨20993180682013536471678023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55981815152036097257808061 20993180682013536471678023)
        ·
          refine ⟨31489771023020304707517035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20993180682013536471678023 31489771023020304707517035)
          ·
            refine ⟨47234656534530457061275553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31489771023020304707517035 47234656534530457061275553)
            ·
              refine ⟨35425992400897842795956665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47234656534530457061275553 35425992400897842795956665)
              ·
                refine ⟨26569494300673382096967499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35425992400897842795956665 26569494300673382096967499)
                ·
                  refine ⟨39854241451010073145451249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26569494300673382096967499 39854241451010073145451249)
                  ·
                    refine ⟨29890681088257554859088437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39854241451010073145451249 29890681088257554859088437)
                    ·
                      refine ⟨2802251352024145768039541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29890681088257554859088437 2802251352024145768039541)
                      ·
                        rfl

theorem cell23_5457365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_5457365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457365 prefixEnd_5457365 := by exact prefixLift 5457365
  have htrace : WordTrace (prefixWord ++ tailWord_5457365) baseStart_5457365 baseEnd_5457365 := by
    simpa [prefixWord, tailWord_5457365, baseEnd_5457365] using wordTrace_append hprefix tailTrace_5457365
  have hstable : (prefixWord ++ tailWord_5457365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457365).length < 2 ^ (prefixWord ++ tailWord_5457365).sum := by decide
  have hdescent : baseEnd_5457365 < baseStart_5457365 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457395 : List Nat := [1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 3]
def baseStart_5457395 : Nat := 118140960795 + 5457395 * 2 ^ 59
def prefixEnd_5457395 : Nat := 4983230072969 + 3 ^ 40 * 5457395 * 2
def baseEnd_5457395 : Nat := 2802266756443780650664403

theorem tailTrace_5457395 : CollatzResearch.WordTrace tailWord_5457395 prefixEnd_5457395 2802266756443780650664403 := by
  unfold tailWord_5457395
  simp only [CollatzResearch.WordTrace]
  refine ⟨199047548063797438706909639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132698365375864959137939759 199047548063797438706909639)
  ·
    refine ⟨298571322095696158060364459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199047548063797438706909639 298571322095696158060364459)
    ·
      refine ⟨447856983143544237090546689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298571322095696158060364459 447856983143544237090546689)
      ·
        refine ⟨335892737357658177817910017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447856983143544237090546689 335892737357658177817910017)
        ·
          refine ⟨251919553018243633363432513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335892737357658177817910017 251919553018243633363432513)
          ·
            refine ⟨188939664763682725022574385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251919553018243633363432513 188939664763682725022574385)
            ·
              refine ⟨141704748572762043766930789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188939664763682725022574385 141704748572762043766930789)
              ·
                refine ⟨26569640357392883206299523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141704748572762043766930789 26569640357392883206299523)
                ·
                  refine ⟨39854460536089324809449285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26569640357392883206299523 39854460536089324809449285)
                  ·
                    refine ⟨7472711350516748401771741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39854460536089324809449285 7472711350516748401771741)
                    ·
                      refine ⟨2802266756443780650664403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7472711350516748401771741 2802266756443780650664403)
                      ·
                        rfl

theorem cell23_5457395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 3].length) (baseStart_5457395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457395 prefixEnd_5457395 := by exact prefixLift 5457395
  have htrace : WordTrace (prefixWord ++ tailWord_5457395) baseStart_5457395 baseEnd_5457395 := by
    simpa [prefixWord, tailWord_5457395, baseEnd_5457395] using wordTrace_append hprefix tailTrace_5457395
  have hstable : (prefixWord ++ tailWord_5457395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457395).length < 2 ^ (prefixWord ++ tailWord_5457395).sum := by decide
  have hdescent : baseEnd_5457395 < baseStart_5457395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457406 : List Nat := [4, 2, 2, 3, 1, 1, 2, 1, 2, 5]
def baseStart_5457406 : Nat := 118140960795 + 5457406 * 2 ^ 59
def prefixEnd_5457406 : Nat := 4983230072969 + 3 ^ 40 * 5457406 * 2
def baseEnd_5457406 : Nat := 934090801576993369208951

theorem tailTrace_5457406 : CollatzResearch.WordTrace tailWord_5457406 prefixEnd_5457406 934090801576993369208951 := by
  unfold tailWord_5457406
  simp only [CollatzResearch.WordTrace]
  refine ⟨24880993658344698448195009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132698632844505058390373381 24880993658344698448195009)
  ·
    refine ⟨18660745243758523836146257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24880993658344698448195009 18660745243758523836146257)
    ·
      refine ⟨13995558932818892877109693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18660745243758523836146257 13995558932818892877109693)
      ·
        refine ⟨5248334599807084828916135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13995558932818892877109693 5248334599807084828916135)
        ·
          refine ⟨7872501899710627243374203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5248334599807084828916135 7872501899710627243374203)
          ·
            refine ⟨11808752849565940865061305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7872501899710627243374203 11808752849565940865061305)
            ·
              refine ⟨8856564637174455648795979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11808752849565940865061305 8856564637174455648795979)
              ·
                refine ⟨13284846955761683473193969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8856564637174455648795979 13284846955761683473193969)
                ·
                  refine ⟨9963635216821262604895477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13284846955761683473193969 9963635216821262604895477)
                  ·
                    refine ⟨934090801576993369208951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9963635216821262604895477 934090801576993369208951)
                    ·
                      rfl

theorem cell23_5457406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_5457406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457406 prefixEnd_5457406 := by exact prefixLift 5457406
  have htrace : WordTrace (prefixWord ++ tailWord_5457406) baseStart_5457406 baseEnd_5457406 := by
    simpa [prefixWord, tailWord_5457406, baseEnd_5457406] using wordTrace_append hprefix tailTrace_5457406
  have hstable : (prefixWord ++ tailWord_5457406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457406).length < 2 ^ (prefixWord ++ tailWord_5457406).sum := by decide
  have hdescent : baseEnd_5457406 < baseStart_5457406 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457409 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_5457409 : Nat := 118140960795 + 5457409 * 2 ^ 59
def prefixEnd_5457409 : Nat := 4983230072969 + 3 ^ 40 * 5457409 * 2
def baseEnd_5457409 : Nat := 2802273945172943595889339

theorem tailTrace_5457409 : CollatzResearch.WordTrace tailWord_5457409 prefixEnd_5457409 2802273945172943595889339 := by
  unfold tailWord_5457409
  simp only [CollatzResearch.WordTrace]
  refine ⟨199048058685746719097919281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132698705790497812731946187 199048058685746719097919281)
  ·
    refine ⟨149286044014310039323439461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199048058685746719097919281 149286044014310039323439461)
    ·
      refine ⟨27991133252683132373144899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149286044014310039323439461 27991133252683132373144899)
      ·
        refine ⟨41986699879024698559717349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27991133252683132373144899 41986699879024698559717349)
        ·
          refine ⟨7872506227317130979947003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41986699879024698559717349 7872506227317130979947003)
          ·
            refine ⟨11808759340975696469920505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7872506227317130979947003 11808759340975696469920505)
            ·
              refine ⟨8856569505731772352440379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11808759340975696469920505 8856569505731772352440379)
              ·
                refine ⟨13284854258597658528660569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8856569505731772352440379 13284854258597658528660569)
                ·
                  refine ⟨9963640693948243896495427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13284854258597658528660569 9963640693948243896495427)
                  ·
                    refine ⟨14945461040922365844743141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9963640693948243896495427 14945461040922365844743141)
                    ·
                      refine ⟨2802273945172943595889339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14945461040922365844743141 2802273945172943595889339)
                      ·
                        rfl

theorem cell23_5457409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_5457409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457409 prefixEnd_5457409 := by exact prefixLift 5457409
  have htrace : WordTrace (prefixWord ++ tailWord_5457409) baseStart_5457409 baseEnd_5457409 := by
    simpa [prefixWord, tailWord_5457409, baseEnd_5457409] using wordTrace_append hprefix tailTrace_5457409
  have hstable : (prefixWord ++ tailWord_5457409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457409).length < 2 ^ (prefixWord ++ tailWord_5457409).sum := by decide
  have hdescent : baseEnd_5457409 < baseStart_5457409 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457459 : List Nat := [1, 1, 1, 2, 4, 4, 1, 2, 3, 1, 3]
def baseStart_5457459 : Nat := 118140960795 + 5457459 * 2 ^ 59
def prefixEnd_5457459 : Nat := 4983230072969 + 3 ^ 40 * 5457459 * 2
def baseEnd_5457459 : Nat := 2802299619205668400264109

theorem tailTrace_5457459 : CollatzResearch.WordTrace tailWord_5457459 prefixEnd_5457459 2802299619205668400264109 := by
  unfold tailWord_5457459
  simp only [CollatzResearch.WordTrace]
  refine ⟨199049882335565577637239431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132699921557043718424826287 199049882335565577637239431)
  ·
    refine ⟨298574823503348366455859147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199049882335565577637239431 298574823503348366455859147)
    ·
      refine ⟨447862235255022549683788721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298574823503348366455859147 447862235255022549683788721)
      ·
        refine ⟨335896676441266912262841541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447862235255022549683788721 335896676441266912262841541)
        ·
          refine ⟨62980626832737546049282789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 335896676441266912262841541 62980626832737546049282789)
          ·
            refine ⟨11808867531138289884240523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62980626832737546049282789 11808867531138289884240523)
            ·
              refine ⟨17713301296707434826360785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11808867531138289884240523 17713301296707434826360785)
              ·
                refine ⟨13284975972530576119770589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17713301296707434826360785 13284975972530576119770589)
                ·
                  refine ⟨4981865989698966044913971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13284975972530576119770589 4981865989698966044913971)
                  ·
                    refine ⟨7472798984548449067370957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4981865989698966044913971 7472798984548449067370957)
                    ·
                      refine ⟨2802299619205668400264109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7472798984548449067370957 2802299619205668400264109)
                      ·
                        rfl

theorem cell23_5457459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 1, 3].length) (baseStart_5457459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457459 prefixEnd_5457459 := by exact prefixLift 5457459
  have htrace : WordTrace (prefixWord ++ tailWord_5457459) baseStart_5457459 baseEnd_5457459 := by
    simpa [prefixWord, tailWord_5457459, baseEnd_5457459] using wordTrace_append hprefix tailTrace_5457459
  have hstable : (prefixWord ++ tailWord_5457459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457459).length < 2 ^ (prefixWord ++ tailWord_5457459).sum := by decide
  have hdescent : baseEnd_5457459 < baseStart_5457459 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457479 : List Nat := [1, 1, 4, 1, 5, 1, 1, 3, 1, 5]
def baseStart_5457479 : Nat := 118140960795 + 5457479 * 2 ^ 59
def prefixEnd_5457479 : Nat := 4983230072969 + 3 ^ 40 * 5457479 * 2
def baseEnd_5457479 : Nat := 934103296272919440671339

theorem tailTrace_5457479 : CollatzResearch.WordTrace tailWord_5457479 prefixEnd_5457479 934103296272919440671339 := by
  unfold tailWord_5457479
  simp only [CollatzResearch.WordTrace]
  refine ⟨199050611795493121052967491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132700407863662080701978327 199050611795493121052967491)
  ·
    refine ⟨298575917693239681579451237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199050611795493121052967491 298575917693239681579451237)
    ·
      refine ⟨55982984567482440296147107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 298575917693239681579451237 55982984567482440296147107)
      ·
        refine ⟨83974476851223660444220661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55982984567482440296147107 83974476851223660444220661)
        ·
          refine ⟨7872607204802218166645687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83974476851223660444220661 7872607204802218166645687)
          ·
            refine ⟨11808910807203327249968531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7872607204802218166645687 11808910807203327249968531)
            ·
              refine ⟨17713366210804990874952797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11808910807203327249968531 17713366210804990874952797)
              ·
                refine ⟨6642512329051871578107299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17713366210804990874952797 6642512329051871578107299)
                ·
                  refine ⟨9963768493577807367160949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6642512329051871578107299 9963768493577807367160949)
                  ·
                    refine ⟨934103296272919440671339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9963768493577807367160949 934103296272919440671339)
                    ·
                      rfl

theorem cell23_5457479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_5457479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457479 prefixEnd_5457479 := by exact prefixLift 5457479
  have htrace : WordTrace (prefixWord ++ tailWord_5457479) baseStart_5457479 baseEnd_5457479 := by
    simpa [prefixWord, tailWord_5457479, baseEnd_5457479] using wordTrace_append hprefix tailTrace_5457479
  have hstable : (prefixWord ++ tailWord_5457479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457479).length < 2 ^ (prefixWord ++ tailWord_5457479).sum := by decide
  have hdescent : baseEnd_5457479 < baseStart_5457479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457505 : List Nat := [1, 2, 3, 1, 1, 3, 2, 10]
def baseStart_5457505 : Nat := 118140960795 + 5457505 * 2 ^ 59
def prefixEnd_5457505 : Nat := 4983230072969 + 3 ^ 40 * 5457505 * 2
def baseEnd_5457505 : Nat := 103789749604287971121811

theorem tailTrace_5457505 : CollatzResearch.WordTrace tailWord_5457505 prefixEnd_5457505 103789749604287971121811 := by
  unfold tailWord_5457505
  simp only [CollatzResearch.WordTrace]
  refine ⟨199051560093398927493413969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132701040062265951662275979 199051560093398927493413969)
  ·
    refine ⟨149288670070049195620060477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199051560093398927493413969 149288670070049195620060477)
    ·
      refine ⟨55983251276268448357522679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149288670070049195620060477 55983251276268448357522679)
      ·
        refine ⟨83974876914402672536284019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55983251276268448357522679 83974876914402672536284019)
        ·
          refine ⟨125962315371604008804426029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83974876914402672536284019 125962315371604008804426029)
          ·
            refine ⟨47235868264351503301659761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125962315371604008804426029 47235868264351503301659761)
            ·
              refine ⟨35426901198263627476244821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47235868264351503301659761 35426901198263627476244821)
              ·
                refine ⟨103789749604287971121811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35426901198263627476244821 103789749604287971121811)
                ·
                  rfl

theorem cell23_5457505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 10].length) (baseStart_5457505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457505 prefixEnd_5457505 := by exact prefixLift 5457505
  have htrace : WordTrace (prefixWord ++ tailWord_5457505) baseStart_5457505 baseEnd_5457505 := by
    simpa [prefixWord, tailWord_5457505, baseEnd_5457505] using wordTrace_append hprefix tailTrace_5457505
  have hstable : (prefixWord ++ tailWord_5457505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457505).length < 2 ^ (prefixWord ++ tailWord_5457505).sum := by decide
  have hdescent : baseEnd_5457505 < baseStart_5457505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457509 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 1, 6]
def baseStart_5457509 : Nat := 118140960795 + 5457509 * 2 ^ 59
def prefixEnd_5457509 : Nat := 4983230072969 + 3 ^ 40 * 5457509 * 2
def baseEnd_5457509 : Nat := 934108431079464401546293

theorem tailTrace_5457509 : CollatzResearch.WordTrace tailWord_5457509 prefixEnd_5457509 934108431079464401546293 := by
  unfold tailWord_5457509
  simp only [CollatzResearch.WordTrace]
  refine ⟨199051705985384436176559581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132701137323589624117706387 199051705985384436176559581)
  ·
    refine ⟨74644389744519163566209843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199051705985384436176559581 74644389744519163566209843)
    ·
      refine ⟨111966584616778745349314765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74644389744519163566209843 111966584616778745349314765)
      ·
        refine ⟨41987469231292029505993037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111966584616778745349314765 41987469231292029505993037)
        ·
          refine ⟨15745300961734511064747389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41987469231292029505993037 15745300961734511064747389)
          ·
            refine ⟨5904487860650441649280271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15745300961734511064747389 5904487860650441649280271)
            ·
              refine ⟨8856731790975662473920407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5904487860650441649280271 8856731790975662473920407)
              ·
                refine ⟨13285097686463493710880611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8856731790975662473920407 13285097686463493710880611)
                ·
                  refine ⟨19927646529695240566320917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13285097686463493710880611 19927646529695240566320917)
                  ·
                    refine ⟨934108431079464401546293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19927646529695240566320917 934108431079464401546293)
                    ·
                      rfl

theorem cell23_5457509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_5457509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457509 prefixEnd_5457509 := by exact prefixLift 5457509
  have htrace : WordTrace (prefixWord ++ tailWord_5457509) baseStart_5457509 baseEnd_5457509 := by
    simpa [prefixWord, tailWord_5457509, baseEnd_5457509] using wordTrace_append hprefix tailTrace_5457509
  have hstable : (prefixWord ++ tailWord_5457509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457509).length < 2 ^ (prefixWord ++ tailWord_5457509).sum := by decide
  have hdescent : baseEnd_5457509 < baseStart_5457509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457522 : List Nat := [3, 2, 1, 2, 3, 2, 1, 9]
def baseStart_5457522 : Nat := 118140960795 + 5457522 * 2 ^ 59
def prefixEnd_5457522 : Nat := 4983230072969 + 3 ^ 40 * 5457522 * 2
def baseEnd_5457522 : Nat := 103790072906922283473197

theorem tailTrace_5457522 : CollatzResearch.WordTrace tailWord_5457522 prefixEnd_5457522 103790072906922283473197 := by
  unfold tailWord_5457522
  simp only [CollatzResearch.WordTrace]
  refine ⟨49763045033584334849195705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132701453422891559597855213 49763045033584334849195705)
  ·
    refine ⟨37322283775188251136896779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49763045033584334849195705 37322283775188251136896779)
    ·
      refine ⟨55983425662782376705345169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37322283775188251136896779 55983425662782376705345169)
      ·
        refine ⟨41987569247086782529008877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55983425662782376705345169 41987569247086782529008877)
        ·
          refine ⟨15745338467657543448378329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41987569247086782529008877 15745338467657543448378329)
          ·
            refine ⟨11809003850743157586283747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15745338467657543448378329 11809003850743157586283747)
            ·
              refine ⟨17713505776114736379425621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11809003850743157586283747 17713505776114736379425621)
              ·
                refine ⟨103790072906922283473197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17713505776114736379425621 103790072906922283473197)
                ·
                  rfl

theorem cell23_5457522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 9].length) (baseStart_5457522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457522 prefixEnd_5457522 := by exact prefixLift 5457522
  have htrace : WordTrace (prefixWord ++ tailWord_5457522) baseStart_5457522 baseEnd_5457522 := by
    simpa [prefixWord, tailWord_5457522, baseEnd_5457522] using wordTrace_append hprefix tailTrace_5457522
  have hstable : (prefixWord ++ tailWord_5457522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457522).length < 2 ^ (prefixWord ++ tailWord_5457522).sum := by decide
  have hdescent : baseEnd_5457522 < baseStart_5457522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457532 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 3, 3, 3]
def baseStart_5457532 : Nat := 118140960795 + 5457532 * 2 ^ 59
def prefixEnd_5457532 : Nat := 4983230072969 + 3 ^ 40 * 5457532 * 2
def baseEnd_5457532 : Nat := 2802337103293446614651273

theorem tailTrace_5457532 : CollatzResearch.WordTrace tailWord_5457532 prefixEnd_5457532 2802337103293446614651273 := by
  unfold tailWord_5457532
  simp only [CollatzResearch.WordTrace]
  refine ⟨99526272432150555552323425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132701696576200740736431233 99526272432150555552323425)
  ·
    refine ⟨74644704324112916664242569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99526272432150555552323425 74644704324112916664242569)
    ·
      refine ⟨55983528243084687498181927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74644704324112916664242569 55983528243084687498181927)
      ·
        refine ⟨83975292364627031247272891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55983528243084687498181927 83975292364627031247272891)
        ·
          refine ⟨125962938546940546870909337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83975292364627031247272891 125962938546940546870909337)
          ·
            refine ⟨94472203910205410153182003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125962938546940546870909337 94472203910205410153182003)
            ·
              refine ⟨141708305865308115229773005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94472203910205410153182003 141708305865308115229773005)
              ·
                refine ⟨53140614699490543211164877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141708305865308115229773005 53140614699490543211164877)
                ·
                  refine ⟨19927730512308953704186829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53140614699490543211164877 19927730512308953704186829)
                  ·
                    refine ⟨7472898942115857639070061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19927730512308953704186829 7472898942115857639070061)
                    ·
                      refine ⟨2802337103293446614651273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7472898942115857639070061 2802337103293446614651273)
                      ·
                        rfl

theorem cell23_5457532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_5457532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457532 prefixEnd_5457532 := by exact prefixLift 5457532
  have htrace : WordTrace (prefixWord ++ tailWord_5457532) baseStart_5457532 baseEnd_5457532 := by
    simpa [prefixWord, tailWord_5457532, baseEnd_5457532] using wordTrace_append hprefix tailTrace_5457532
  have hstable : (prefixWord ++ tailWord_5457532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457532).length < 2 ^ (prefixWord ++ tailWord_5457532).sum := by decide
  have hdescent : baseEnd_5457532 < baseStart_5457532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457570 : List Nat := [3, 3, 1, 4, 1, 2, 1, 2, 1, 2, 3]
def baseStart_5457570 : Nat := 118140960795 + 5457570 * 2 ^ 59
def prefixEnd_5457570 : Nat := 4983230072969 + 3 ^ 40 * 5457570 * 2
def baseEnd_5457570 : Nat := 2802356615558317465976099

theorem tailTrace_5457570 : CollatzResearch.WordTrace tailWord_5457570 prefixEnd_5457570 2802356615558317465976099 := by
  unfold tailWord_5457570
  simp only [CollatzResearch.WordTrace]
  refine ⟨49763482709540860898632541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132702620558775629063020109 49763482709540860898632541)
  ·
    refine ⟨18661306016077822836987203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49763482709540860898632541 18661306016077822836987203)
    ·
      refine ⟨27991959024116734255480805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18661306016077822836987203 27991959024116734255480805)
      ·
        refine ⟨5248492317021887672902651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27991959024116734255480805 5248492317021887672902651)
        ·
          refine ⟨7872738475532831509353977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5248492317021887672902651 7872738475532831509353977)
          ·
            refine ⟨5904553856649623632015483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7872738475532831509353977 5904553856649623632015483)
            ·
              refine ⟨8856830784974435448023225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5904553856649623632015483 8856830784974435448023225)
              ·
                refine ⟨6642623088730826586017419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8856830784974435448023225 6642623088730826586017419)
                ·
                  refine ⟨9963934633096239879026129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6642623088730826586017419 9963934633096239879026129)
                  ·
                    refine ⟨7472950974822179909269597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9963934633096239879026129 7472950974822179909269597)
                    ·
                      refine ⟨2802356615558317465976099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7472950974822179909269597 2802356615558317465976099)
                      ·
                        rfl

theorem cell23_5457570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_5457570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457570 prefixEnd_5457570 := by exact prefixLift 5457570
  have htrace : WordTrace (prefixWord ++ tailWord_5457570) baseStart_5457570 baseEnd_5457570 := by
    simpa [prefixWord, tailWord_5457570, baseEnd_5457570] using wordTrace_append hprefix tailTrace_5457570
  have hstable : (prefixWord ++ tailWord_5457570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457570).length < 2 ^ (prefixWord ++ tailWord_5457570).sum := by decide
  have hdescent : baseEnd_5457570 < baseStart_5457570 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457592 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 4, 4, 3]
def baseStart_5457592 : Nat := 118140960795 + 5457592 * 2 ^ 59
def prefixEnd_5457592 : Nat := 4983230072969 + 3 ^ 40 * 5457592 * 2
def baseEnd_5457592 : Nat := 2802367912132716379900997

theorem tailTrace_5457592 : CollatzResearch.WordTrace tailWord_5457592 prefixEnd_5457592 2802367912132716379900997 := by
  unfold tailWord_5457592
  simp only [CollatzResearch.WordTrace]
  refine ⟨99527366622041870675915515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132703155496055827567887353 99527366622041870675915515)
  ·
    refine ⟨149291049933062806013873273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99527366622041870675915515 149291049933062806013873273)
    ·
      refine ⟨111968287449797104510404955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149291049933062806013873273 111968287449797104510404955)
      ·
        refine ⟨167952431174695656765607433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111968287449797104510404955 167952431174695656765607433)
        ·
          refine ⟨125964323381021742574205575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167952431174695656765607433 125964323381021742574205575)
          ·
            refine ⟨188946485071532613861308363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125964323381021742574205575 188946485071532613861308363)
            ·
              refine ⟨283419727607298920791962545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188946485071532613861308363 283419727607298920791962545)
              ·
                refine ⟨212564795705474190593971909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283419727607298920791962545 212564795705474190593971909)
                ·
                  refine ⟨39855899194776410736369733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 212564795705474190593971909 39855899194776410736369733)
                  ·
                    refine ⟨7472981099020577013069325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39855899194776410736369733 7472981099020577013069325)
                    ·
                      refine ⟨2802367912132716379900997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7472981099020577013069325 2802367912132716379900997)
                      ·
                        rfl

theorem cell23_5457592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 4, 4, 3].length) (baseStart_5457592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457592 prefixEnd_5457592 := by exact prefixLift 5457592
  have htrace : WordTrace (prefixWord ++ tailWord_5457592) baseStart_5457592 baseEnd_5457592 := by
    simpa [prefixWord, tailWord_5457592, baseEnd_5457592] using wordTrace_append hprefix tailTrace_5457592
  have hstable : (prefixWord ++ tailWord_5457592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457592).length < 2 ^ (prefixWord ++ tailWord_5457592).sum := by decide
  have hdescent : baseEnd_5457592 < baseStart_5457592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457646 : List Nat := [4, 1, 2, 1, 1, 2, 4, 3, 5]
def baseStart_5457646 : Nat := 118140960795 + 5457646 * 2 ^ 59
def prefixEnd_5457646 : Nat := 4983230072969 + 3 ^ 40 * 5457646 * 2
def baseEnd_5457646 : Nat := 311377293343117685402861

theorem tailTrace_5457646 : CollatzResearch.WordTrace tailWord_5457646 prefixEnd_5457646 311377293343117685402861 := by
  unfold tailWord_5457646
  simp only [CollatzResearch.WordTrace]
  refine ⟨24882087848236013571787099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132704468523925405716197861 24882087848236013571787099)
  ·
    refine ⟨37323131772354020357680649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24882087848236013571787099 37323131772354020357680649)
    ·
      refine ⟨27992348829265515268260487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37323131772354020357680649 27992348829265515268260487)
      ·
        refine ⟨41988523243898272902390731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27992348829265515268260487 41988523243898272902390731)
        ·
          refine ⟨62982784865847409353586097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41988523243898272902390731 62982784865847409353586097)
          ·
            refine ⟨47237088649385557015189573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62982784865847409353586097 47237088649385557015189573)
            ·
              refine ⟨8856954121759791940348045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47237088649385557015189573 8856954121759791940348045)
              ·
                refine ⟨3321357795659921977630517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8856954121759791940348045 3321357795659921977630517)
                ·
                  refine ⟨311377293343117685402861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3321357795659921977630517 311377293343117685402861)
                  ·
                    rfl

theorem cell23_5457646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 3, 5].length) (baseStart_5457646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457646 prefixEnd_5457646 := by exact prefixLift 5457646
  have htrace : WordTrace (prefixWord ++ tailWord_5457646) baseStart_5457646 baseEnd_5457646 := by
    simpa [prefixWord, tailWord_5457646, baseEnd_5457646] using wordTrace_append hprefix tailTrace_5457646
  have hstable : (prefixWord ++ tailWord_5457646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457646).length < 2 ^ (prefixWord ++ tailWord_5457646).sum := by decide
  have hdescent : baseEnd_5457646 < baseStart_5457646 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457679 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 1, 6, 2]
def baseStart_5457679 : Nat := 118140960795 + 5457679 * 2 ^ 59
def prefixEnd_5457679 : Nat := 4983230072969 + 3 ^ 40 * 5457679 * 2
def baseEnd_5457679 : Nat := 2802412584949657539513097

theorem tailTrace_5457679 : CollatzResearch.WordTrace tailWord_5457679 prefixEnd_5457679 2802412584949657539513097 := by
  unfold tailWord_5457679
  simp only [CollatzResearch.WordTrace]
  refine ⟨199057906394768555210248091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132705270929845703473498727 199057906394768555210248091)
  ·
    refine ⟨298586859592152832815372137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199057906394768555210248091 298586859592152832815372137)
    ·
      refine ⟨223940144694114624611529103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298586859592152832815372137 223940144694114624611529103)
      ·
        refine ⟨335910217041171936917293655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223940144694114624611529103 335910217041171936917293655)
        ·
          refine ⟨503865325561757905375940483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335910217041171936917293655 503865325561757905375940483)
          ·
            refine ⟨755797988342636858063910725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503865325561757905375940483 755797988342636858063910725)
            ·
              refine ⟨141712122814244410886983261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 755797988342636858063910725 141712122814244410886983261)
              ·
                refine ⟨53142046055341654082618723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141712122814244410886983261 53142046055341654082618723)
                ·
                  refine ⟨79713069083012481123928085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53142046055341654082618723 79713069083012481123928085)
                  ·
                    refine ⟨3736550113266210052684129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79713069083012481123928085 3736550113266210052684129)
                    ·
                      refine ⟨2802412584949657539513097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3736550113266210052684129 2802412584949657539513097)
                      ·
                        rfl

theorem cell23_5457679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 6, 2].length) (baseStart_5457679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457679 prefixEnd_5457679 := by exact prefixLift 5457679
  have htrace : WordTrace (prefixWord ++ tailWord_5457679) baseStart_5457679 baseEnd_5457679 := by
    simpa [prefixWord, tailWord_5457679, baseEnd_5457679] using wordTrace_append hprefix tailTrace_5457679
  have hstable : (prefixWord ++ tailWord_5457679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457679).length < 2 ^ (prefixWord ++ tailWord_5457679).sum := by decide
  have hdescent : baseEnd_5457679 < baseStart_5457679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457699 : List Nat := [1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 3]
def baseStart_5457699 : Nat := 118140960795 + 5457699 * 2 ^ 59
def prefixEnd_5457699 : Nat := 4983230072969 + 3 ^ 40 * 5457699 * 2
def baseEnd_5457699 : Nat := 2802422854562747461263005

theorem tailTrace_5457699 : CollatzResearch.WordTrace tailWord_5457699 prefixEnd_5457699 2802422854562747461263005 := by
  unfold tailWord_5457699
  simp only [CollatzResearch.WordTrace]
  refine ⟨199058635854696098625976151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132705757236464065750650767 199058635854696098625976151)
  ·
    refine ⟨298587953782044147938964227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199058635854696098625976151 298587953782044147938964227)
    ·
      refine ⟨447881930673066221908446341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298587953782044147938964227 447881930673066221908446341)
      ·
        refine ⟨83977862001199916607833689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 447881930673066221908446341 83977862001199916607833689)
        ·
          refine ⟨62983396500899937455875267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83977862001199916607833689 62983396500899937455875267)
          ·
            refine ⟨94475094751349906183812901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62983396500899937455875267 94475094751349906183812901)
            ·
              refine ⟨17714080265878107409464919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94475094751349906183812901 17714080265878107409464919)
              ·
                refine ⟨26571120398817161114197379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17714080265878107409464919 26571120398817161114197379)
                ·
                  refine ⟨39856680598225741671296069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26571120398817161114197379 39856680598225741671296069)
                  ·
                    refine ⟨7473127612167326563368013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39856680598225741671296069 7473127612167326563368013)
                    ·
                      refine ⟨2802422854562747461263005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7473127612167326563368013 2802422854562747461263005)
                      ·
                        rfl

theorem cell23_5457699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_5457699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457699 prefixEnd_5457699 := by exact prefixLift 5457699
  have htrace : WordTrace (prefixWord ++ tailWord_5457699) baseStart_5457699 baseEnd_5457699 := by
    simpa [prefixWord, tailWord_5457699, baseEnd_5457699] using wordTrace_append hprefix tailTrace_5457699
  have hstable : (prefixWord ++ tailWord_5457699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457699).length < 2 ^ (prefixWord ++ tailWord_5457699).sum := by decide
  have hdescent : baseEnd_5457699 < baseStart_5457699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457736 : List Nat := [2, 1, 3, 1, 1, 4, 4, 1, 6]
def baseStart_5457736 : Nat := 118140960795 + 5457736 * 2 ^ 59
def prefixEnd_5457736 : Nat := 4983230072969 + 3 ^ 40 * 5457736 * 2
def baseEnd_5457736 : Nat := 311382428149662646277815

theorem tailTrace_5457736 : CollatzResearch.WordTrace tailWord_5457736 prefixEnd_5457736 311382428149662646277815 := by
  unfold tailWord_5457736
  simp only [CollatzResearch.WordTrace]
  refine ⟨99529992677781026972536531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132706656903708035963382041 99529992677781026972536531)
  ·
    refine ⟨149294989016671540458804797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99529992677781026972536531 149294989016671540458804797)
    ·
      refine ⟨55985620881251827672051799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149294989016671540458804797 55985620881251827672051799)
      ·
        refine ⟨83978431321877741508077699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55985620881251827672051799 83978431321877741508077699)
        ·
          refine ⟨125967646982816612262116549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83978431321877741508077699 125967646982816612262116549)
          ·
            refine ⟨23618933809278114799146853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125967646982816612262116549 23618933809278114799146853)
            ·
              refine ⟨4428550089239646524840035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23618933809278114799146853 4428550089239646524840035)
              ·
                refine ⟨6642825133859469787260053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4428550089239646524840035 6642825133859469787260053)
                ·
                  refine ⟨311382428149662646277815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6642825133859469787260053 311382428149662646277815)
                  ·
                    rfl

theorem cell23_5457736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 1, 6].length) (baseStart_5457736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457736 prefixEnd_5457736 := by exact prefixLift 5457736
  have htrace : WordTrace (prefixWord ++ tailWord_5457736) baseStart_5457736 baseEnd_5457736 := by
    simpa [prefixWord, tailWord_5457736, baseEnd_5457736] using wordTrace_append hprefix tailTrace_5457736
  have hstable : (prefixWord ++ tailWord_5457736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457736).length < 2 ^ (prefixWord ++ tailWord_5457736).sum := by decide
  have hdescent : baseEnd_5457736 < baseStart_5457736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457773 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_5457773 : Nat := 118140960795 + 5457773 * 2 ^ 59
def prefixEnd_5457773 : Nat := 4983230072969 + 3 ^ 40 * 5457773 * 2
def baseEnd_5457773 : Nat := 2802460852131180171737665

theorem tailTrace_5457773 : CollatzResearch.WordTrace tailWord_5457773 prefixEnd_5457773 2802460852131180171737665 := by
  unfold tailWord_5457773
  simp only [CollatzResearch.WordTrace]
  refine ⟨199061334856428009264169973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132707556570952006176113315 199061334856428009264169973)
  ·
    refine ⟨18662000142790125868515935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199061334856428009264169973 18662000142790125868515935)
    ·
      refine ⟨27993000214185188802773903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18662000142790125868515935 27993000214185188802773903)
      ·
        refine ⟨41989500321277783204160855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27993000214185188802773903 41989500321277783204160855)
        ·
          refine ⟨62984250481916674806241283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41989500321277783204160855 62984250481916674806241283)
          ·
            refine ⟨94476375722875012209361925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62984250481916674806241283 94476375722875012209361925)
            ·
              refine ⟨17714320448039064789255361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94476375722875012209361925 17714320448039064789255361)
              ·
                refine ⟨13285740336029298591941521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17714320448039064789255361 13285740336029298591941521)
                ·
                  refine ⟨9964305252021973943956141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13285740336029298591941521 9964305252021973943956141)
                  ·
                    refine ⟨3736614469508240228983553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9964305252021973943956141 3736614469508240228983553)
                    ·
                      refine ⟨2802460852131180171737665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3736614469508240228983553 2802460852131180171737665)
                      ·
                        rfl

theorem cell23_5457773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_5457773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457773 prefixEnd_5457773 := by exact prefixLift 5457773
  have htrace : WordTrace (prefixWord ++ tailWord_5457773) baseStart_5457773 baseEnd_5457773 := by
    simpa [prefixWord, tailWord_5457773, baseEnd_5457773] using wordTrace_append hprefix tailTrace_5457773
  have hstable : (prefixWord ++ tailWord_5457773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457773).length < 2 ^ (prefixWord ++ tailWord_5457773).sum := by decide
  have hdescent : baseEnd_5457773 < baseStart_5457773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457789 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_5457789 : Nat := 118140960795 + 5457789 * 2 ^ 59
def prefixEnd_5457789 : Nat := 4983230072969 + 3 ^ 40 * 5457789 * 2
def baseEnd_5457789 : Nat := 2802469067821652109137591

theorem tailTrace_5457789 : CollatzResearch.WordTrace tailWord_5457789 prefixEnd_5457789 2802469067821652109137591 := by
  unfold tailWord_5457789
  simp only [CollatzResearch.WordTrace]
  refine ⟨199061918424370043996752421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132707945616246695997834947 199061918424370043996752421)
  ·
    refine ⟨37324109704569383249391079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199061918424370043996752421 37324109704569383249391079)
    ·
      refine ⟨55986164556854074874086619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37324109704569383249391079 55986164556854074874086619)
      ·
        refine ⟨83979246835281112311129929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55986164556854074874086619 83979246835281112311129929)
        ·
          refine ⟨62984435126460834233347447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83979246835281112311129929 62984435126460834233347447)
          ·
            refine ⟨94476652689691251350021171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62984435126460834233347447 94476652689691251350021171)
            ·
              refine ⟨141714979034536877025031757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94476652689691251350021171 141714979034536877025031757)
              ·
                refine ⟨53143117137951328884386909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141714979034536877025031757 53143117137951328884386909)
                ·
                  refine ⟨19928668926731748331645091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53143117137951328884386909 19928668926731748331645091)
                  ·
                    refine ⟨29893003390097622497467637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19928668926731748331645091 29893003390097622497467637)
                    ·
                      refine ⟨2802469067821652109137591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29893003390097622497467637 2802469067821652109137591)
                      ·
                        rfl

theorem cell23_5457789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_5457789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457789 prefixEnd_5457789 := by exact prefixLift 5457789
  have htrace : WordTrace (prefixWord ++ tailWord_5457789) baseStart_5457789 baseEnd_5457789 := by
    simpa [prefixWord, tailWord_5457789, baseEnd_5457789] using wordTrace_append hprefix tailTrace_5457789
  have hstable : (prefixWord ++ tailWord_5457789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457789).length < 2 ^ (prefixWord ++ tailWord_5457789).sum := by decide
  have hdescent : baseEnd_5457789 < baseStart_5457789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457820 : List Nat := [2, 2, 3, 3, 1, 1, 4, 1, 1, 1, 4]
def baseStart_5457820 : Nat := 118140960795 + 5457820 * 2 ^ 59
def prefixEnd_5457820 : Nat := 4983230072969 + 3 ^ 40 * 5457820 * 2
def baseEnd_5457820 : Nat := 2802484985721941487849949

theorem tailTrace_5457820 : CollatzResearch.WordTrace tailWord_5457820 prefixEnd_5457820 2802484985721941487849949 := by
  unfold tailWord_5457820
  simp only [CollatzResearch.WordTrace]
  refine ⟨99531524543628868145565457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132708699391505157527420609 99531524543628868145565457)
  ·
    refine ⟨74648643407721651109174093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99531524543628868145565457 74648643407721651109174093)
    ·
      refine ⟨27993241277895619165940285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74648643407721651109174093 27993241277895619165940285)
      ·
        refine ⟨10497465479210857187227607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27993241277895619165940285 10497465479210857187227607)
        ·
          refine ⟨15746198218816285780841411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10497465479210857187227607 15746198218816285780841411)
          ·
            refine ⟨23619297328224428671262117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15746198218816285780841411 23619297328224428671262117)
            ·
              refine ⟨4428618249042080375861647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23619297328224428671262117 4428618249042080375861647)
              ·
                refine ⟨6642927373563120563792471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4428618249042080375861647 6642927373563120563792471)
                ·
                  refine ⟨9964391060344680845688707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6642927373563120563792471 9964391060344680845688707)
                  ·
                    refine ⟨14946586590517021268533061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9964391060344680845688707 14946586590517021268533061)
                    ·
                      refine ⟨2802484985721941487849949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14946586590517021268533061 2802484985721941487849949)
                      ·
                        rfl

theorem cell23_5457820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_5457820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457820 prefixEnd_5457820 := by exact prefixLift 5457820
  have htrace : WordTrace (prefixWord ++ tailWord_5457820) baseStart_5457820 baseEnd_5457820 := by
    simpa [prefixWord, tailWord_5457820, baseEnd_5457820] using wordTrace_append hprefix tailTrace_5457820
  have hstable : (prefixWord ++ tailWord_5457820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457820).length < 2 ^ (prefixWord ++ tailWord_5457820).sum := by decide
  have hdescent : baseEnd_5457820 < baseStart_5457820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457826 : List Nat := [3, 3, 1, 2, 3, 1, 10]
def baseStart_5457826 : Nat := 118140960795 + 5457826 * 2 ^ 59
def prefixEnd_5457826 : Nat := 4983230072969 + 3 ^ 40 * 5457826 * 2
def baseEnd_5457826 : Nat := 34598618106245289683641

theorem tailTrace_5457826 : CollatzResearch.WordTrace tailWord_5457826 prefixEnd_5457826 34598618106245289683641 := by
  unfold tailWord_5457826
  simp only [CollatzResearch.WordTrace]
  refine ⟨49765816981308999828962333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132708845283490666210566221 49765816981308999828962333)
  ·
    refine ⟨18662181367990874935860875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49765816981308999828962333 18662181367990874935860875)
    ·
      refine ⟨27993272051986312403791313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18662181367990874935860875 27993272051986312403791313)
      ·
        refine ⟨20994954038989734302843485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27993272051986312403791313 20994954038989734302843485)
        ·
          refine ⟨7873107764621150363566307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20994954038989734302843485 7873107764621150363566307)
          ·
            refine ⟨11809661646931725545349461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7873107764621150363566307 11809661646931725545349461)
            ·
              refine ⟨34598618106245289683641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11809661646931725545349461 34598618106245289683641)
              ·
                rfl

theorem cell23_5457826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 10].length) (baseStart_5457826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457826 prefixEnd_5457826 := by exact prefixLift 5457826
  have htrace : WordTrace (prefixWord ++ tailWord_5457826) baseStart_5457826 baseEnd_5457826 := by
    simpa [prefixWord, tailWord_5457826, baseEnd_5457826] using wordTrace_append hprefix tailTrace_5457826
  have hstable : (prefixWord ++ tailWord_5457826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457826).length < 2 ^ (prefixWord ++ tailWord_5457826).sum := by decide
  have hdescent : baseEnd_5457826 < baseStart_5457826 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457853 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_5457853 : Nat := 118140960795 + 5457853 * 2 ^ 59
def prefixEnd_5457853 : Nat := 4983230072969 + 3 ^ 40 * 5457853 * 2
def baseEnd_5457853 : Nat := 2802501930583539858737297

theorem tailTrace_5457853 : CollatzResearch.WordTrace tailWord_5457853 prefixEnd_5457853 2802501930583539858737297 := by
  unfold tailWord_5457853
  simp only [CollatzResearch.WordTrace]
  refine ⟨199064252696138182927082213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132709501797425455284721475 199064252696138182927082213)
  ·
    refine ⟨37324547380525909298827915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199064252696138182927082213 37324547380525909298827915)
    ·
      refine ⟨55986821070788863948241873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37324547380525909298827915 55986821070788863948241873)
      ·
        refine ⟨41990115803091647961181405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55986821070788863948241873 41990115803091647961181405)
        ·
          refine ⟨15746293426159367985443027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41990115803091647961181405 15746293426159367985443027)
          ·
            refine ⟨23619440139239051978164541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15746293426159367985443027 23619440139239051978164541)
            ·
              refine ⟨8857290052214644491811703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23619440139239051978164541 8857290052214644491811703)
              ·
                refine ⟨13285935078321966737717555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8857290052214644491811703 13285935078321966737717555)
                ·
                  refine ⟨19928902617482950106576333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13285935078321966737717555 19928902617482950106576333)
                  ·
                    refine ⟨7473338481556106289966125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19928902617482950106576333 7473338481556106289966125)
                    ·
                      refine ⟨2802501930583539858737297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7473338481556106289966125 2802501930583539858737297)
                      ·
                        rfl

theorem cell23_5457853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_5457853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457853 prefixEnd_5457853 := by exact prefixLift 5457853
  have htrace : WordTrace (prefixWord ++ tailWord_5457853) baseStart_5457853 baseEnd_5457853 := by
    simpa [prefixWord, tailWord_5457853, baseEnd_5457853] using wordTrace_append hprefix tailTrace_5457853
  have hstable : (prefixWord ++ tailWord_5457853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457853).length < 2 ^ (prefixWord ++ tailWord_5457853).sum := by decide
  have hdescent : baseEnd_5457853 < baseStart_5457853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457896 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 2, 4, 3]
def baseStart_5457896 : Nat := 118140960795 + 5457896 * 2 ^ 59
def prefixEnd_5457896 : Nat := 4983230072969 + 3 ^ 40 * 5457896 * 2
def baseEnd_5457896 : Nat := 2802524010251683190499599

theorem tailTrace_5457896 : CollatzResearch.WordTrace tailWord_5457896 prefixEnd_5457896 2802524010251683190499599 := by
  unfold tailWord_5457896
  simp only [CollatzResearch.WordTrace]
  refine ⟨99532910517491200635448771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132710547356654934180598361 99532910517491200635448771)
  ·
    refine ⟨149299365776236800953173157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99532910517491200635448771 149299365776236800953173157)
    ·
      refine ⟨27993631083044400178719967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149299365776236800953173157 27993631083044400178719967)
      ·
        refine ⟨41990446624566600268079951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27993631083044400178719967 41990446624566600268079951)
        ·
          refine ⟨62985669936849900402119927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41990446624566600268079951 62985669936849900402119927)
          ·
            refine ⟨94478504905274850603179891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62985669936849900402119927 94478504905274850603179891)
            ·
              refine ⟨141717757357912275904769837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94478504905274850603179891 141717757357912275904769837)
              ·
                refine ⟨53144159009217103464288689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141717757357912275904769837 53144159009217103464288689)
                ·
                  refine ⟨39858119256912827598216517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53144159009217103464288689 39858119256912827598216517)
                  ·
                    refine ⟨7473397360671155174665597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39858119256912827598216517 7473397360671155174665597)
                    ·
                      refine ⟨2802524010251683190499599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7473397360671155174665597 2802524010251683190499599)
                      ·
                        rfl

theorem cell23_5457896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_5457896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457896 prefixEnd_5457896 := by exact prefixLift 5457896
  have htrace : WordTrace (prefixWord ++ tailWord_5457896) baseStart_5457896 baseEnd_5457896 := by
    simpa [prefixWord, tailWord_5457896, baseEnd_5457896] using wordTrace_append hprefix tailTrace_5457896
  have hstable : (prefixWord ++ tailWord_5457896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457896).length < 2 ^ (prefixWord ++ tailWord_5457896).sum := by decide
  have hdescent : baseEnd_5457896 < baseStart_5457896 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457919 : List Nat := [1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 8]
def baseStart_5457919 : Nat := 118140960795 + 5457919 * 2 ^ 59
def prefixEnd_5457919 : Nat := 4983230072969 + 3 ^ 40 * 5457919 * 2
def baseEnd_5457919 : Nat := 2802535820306736600511993

theorem tailTrace_5457919 : CollatzResearch.WordTrace tailWord_5457919 prefixEnd_5457919 2802535820306736600511993 := by
  unfold tailWord_5457919
  simp only [CollatzResearch.WordTrace]
  refine ⟨199066659913899076198984811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132711106609266050799323207 199066659913899076198984811)
  ·
    refine ⟨298599989870848614298477217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199066659913899076198984811 298599989870848614298477217)
    ·
      refine ⟨223949992403136460723857913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298599989870848614298477217 223949992403136460723857913)
      ·
        refine ⟨167962494302352345542893435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223949992403136460723857913 167962494302352345542893435)
        ·
          refine ⟨251943741453528518314340153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167962494302352345542893435 251943741453528518314340153)
          ·
            refine ⟨188957806090146388735755115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251943741453528518314340153 188957806090146388735755115)
            ·
              refine ⟨283436709135219583103632673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188957806090146388735755115 283436709135219583103632673)
              ·
                refine ⟨212577531851414687327724505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283436709135219583103632673 212577531851414687327724505)
                ·
                  refine ⟨159433148888561015495793379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212577531851414687327724505 159433148888561015495793379)
                  ·
                    refine ⟨239149723332841523243690069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159433148888561015495793379 239149723332841523243690069)
                    ·
                      refine ⟨2802535820306736600511993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 239149723332841523243690069 2802535820306736600511993)
                      ·
                        rfl

theorem cell23_5457919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_5457919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457919 prefixEnd_5457919 := by exact prefixLift 5457919
  have htrace : WordTrace (prefixWord ++ tailWord_5457919) baseStart_5457919 baseEnd_5457919 := by
    simpa [prefixWord, tailWord_5457919, baseEnd_5457919] using wordTrace_append hprefix tailTrace_5457919
  have hstable : (prefixWord ++ tailWord_5457919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457919).length < 2 ^ (prefixWord ++ tailWord_5457919).sum := by decide
  have hdescent : baseEnd_5457919 < baseStart_5457919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457983 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 4]
def baseStart_5457983 : Nat := 118140960795 + 5457983 * 2 ^ 59
def prefixEnd_5457983 : Nat := 4983230072969 + 3 ^ 40 * 5457983 * 2
def baseEnd_5457983 : Nat := 2802568683068624350111699

theorem tailTrace_5457983 : CollatzResearch.WordTrace tailWord_5457983 prefixEnd_5457983 2802568683068624350111699 := by
  unfold tailWord_5457983
  simp only [CollatzResearch.WordTrace]
  refine ⟨199068994185667215129314603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132712662790444810086209735 199068994185667215129314603)
  ·
    refine ⟨298603491278500822693971905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199068994185667215129314603 298603491278500822693971905)
    ·
      refine ⟨223952618458875617020478929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298603491278500822693971905 223952618458875617020478929)
      ·
        refine ⟨167964463844156712765359197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223952618458875617020478929 167964463844156712765359197)
        ·
          refine ⟨62986673941558767287009699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167964463844156712765359197 62986673941558767287009699)
          ·
            refine ⟨94480010912338150930514549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62986673941558767287009699 94480010912338150930514549)
            ·
              refine ⟨8857501023031701649735739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94480010912338150930514549 8857501023031701649735739)
              ·
                refine ⟨13286251534547552474603609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8857501023031701649735739 13286251534547552474603609)
                ·
                  refine ⟨9964688650910664355952707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13286251534547552474603609 9964688650910664355952707)
                  ·
                    refine ⟨14947032976365996533929061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9964688650910664355952707 14947032976365996533929061)
                    ·
                      refine ⟨2802568683068624350111699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14947032976365996533929061 2802568683068624350111699)
                      ·
                        rfl

theorem cell23_5457983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_5457983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457983 prefixEnd_5457983 := by exact prefixLift 5457983
  have htrace : WordTrace (prefixWord ++ tailWord_5457983) baseStart_5457983 baseEnd_5457983 := by
    simpa [prefixWord, tailWord_5457983, baseEnd_5457983] using wordTrace_append hprefix tailTrace_5457983
  have hstable : (prefixWord ++ tailWord_5457983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457983).length < 2 ^ (prefixWord ++ tailWord_5457983).sum := by decide
  have hdescent : baseEnd_5457983 < baseStart_5457983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5457996 : List Nat := [2, 2, 1, 3, 1, 1, 3, 1, 2, 1, 6]
def baseStart_5457996 : Nat := 118140960795 + 5457996 * 2 ^ 59
def prefixEnd_5457996 : Nat := 4983230072969 + 3 ^ 40 * 5457996 * 2
def baseEnd_5457996 : Nat := 2802575358317132799249139

theorem tailTrace_5457996 : CollatzResearch.WordTrace tailWord_5457996 prefixEnd_5457996 2802575358317132799249139 := by
  unfold tailWord_5457996
  simp only [CollatzResearch.WordTrace]
  refine ⟨99534734167310059174768921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132712978889746745566358561 99534734167310059174768921)
  ·
    refine ⟨74651050625482544381076691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99534734167310059174768921 74651050625482544381076691)
    ·
      refine ⟨111976575938223816571615037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74651050625482544381076691 111976575938223816571615037)
      ·
        refine ⟨41991215976833931214355639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111976575938223816571615037 41991215976833931214355639)
        ·
          refine ⟨62986823965250896821533459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41991215976833931214355639 62986823965250896821533459)
          ·
            refine ⟨94480235947876345232300189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62986823965250896821533459 94480235947876345232300189)
            ·
              refine ⟨35430088480453629462112571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94480235947876345232300189 35430088480453629462112571)
              ·
                refine ⟨53145132720680444193168857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35430088480453629462112571 53145132720680444193168857)
                ·
                  refine ⟨39858849540510333144876643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53145132720680444193168857 39858849540510333144876643)
                  ·
                    refine ⟨59788274310765499717314965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39858849540510333144876643 59788274310765499717314965)
                    ·
                      refine ⟨2802575358317132799249139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59788274310765499717314965 2802575358317132799249139)
                      ·
                        rfl

theorem cell23_5457996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_5457996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5457996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5457996 prefixEnd_5457996 := by exact prefixLift 5457996
  have htrace : WordTrace (prefixWord ++ tailWord_5457996) baseStart_5457996 baseEnd_5457996 := by
    simpa [prefixWord, tailWord_5457996, baseEnd_5457996] using wordTrace_append hprefix tailTrace_5457996
  have hstable : (prefixWord ++ tailWord_5457996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5457996).length < 2 ^ (prefixWord ++ tailWord_5457996).sum := by decide
  have hdescent : baseEnd_5457996 < baseStart_5457996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5457996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458010 : List Nat := [3, 1, 1, 2, 1, 1, 3, 6, 1, 4]
def baseStart_5458010 : Nat := 118140960795 + 5458010 * 2 ^ 59
def prefixEnd_5458010 : Nat := 4983230072969 + 3 ^ 40 * 5458010 * 2
def baseEnd_5458010 : Nat := 934194182348765248158025

theorem tailTrace_5458010 : CollatzResearch.WordTrace tailWord_5458010 prefixEnd_5458010 934194182348765248158025 := by
  unfold tailWord_5458010
  simp only [CollatzResearch.WordTrace]
  refine ⟨49767494739142349685136871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132713319304379599160364989 49767494739142349685136871)
  ·
    refine ⟨74651242108713524527705307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49767494739142349685136871 74651242108713524527705307)
    ·
      refine ⟨111976863163070286791557961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74651242108713524527705307 111976863163070286791557961)
      ·
        refine ⟨83982647372302715093668471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111976863163070286791557961 83982647372302715093668471)
        ·
          refine ⟨125973971058454072640502707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83982647372302715093668471 125973971058454072640502707)
          ·
            refine ⟨188960956587681108960754061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125973971058454072640502707 188960956587681108960754061)
            ·
              refine ⟨70860358720380415860282773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188960956587681108960754061 70860358720380415860282773)
              ·
                refine ⟨3321579315017831993450755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70860358720380415860282773 3321579315017831993450755)
                ·
                  refine ⟨4982368972526747990176133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321579315017831993450755 4982368972526747990176133)
                  ·
                    refine ⟨934194182348765248158025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4982368972526747990176133 934194182348765248158025)
                    ·
                      rfl

theorem cell23_5458010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_5458010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458010 prefixEnd_5458010 := by exact prefixLift 5458010
  have htrace : WordTrace (prefixWord ++ tailWord_5458010) baseStart_5458010 baseEnd_5458010 := by
    simpa [prefixWord, tailWord_5458010, baseEnd_5458010] using wordTrace_append hprefix tailTrace_5458010
  have hstable : (prefixWord ++ tailWord_5458010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458010).length < 2 ^ (prefixWord ++ tailWord_5458010).sum := by decide
  have hdescent : baseEnd_5458010 < baseStart_5458010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458074 : List Nat := [3, 1, 1, 5, 3, 1, 2, 1, 6]
def baseStart_5458074 : Nat := 118140960795 + 5458074 * 2 ^ 59
def prefixEnd_5458074 : Nat := 4983230072969 + 3 ^ 40 * 5458074 * 2
def baseEnd_5458074 : Nat := 311401712200909277119309

theorem tailTrace_5458074 : CollatzResearch.WordTrace tailWord_5458074 prefixEnd_5458074 311401712200909277119309 := by
  unfold tailWord_5458074
  simp only [CollatzResearch.WordTrace]
  refine ⟨49768078307084384417719319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132714875485558358447251517 49768078307084384417719319)
  ·
    refine ⟨74652117460626576626578979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49768078307084384417719319 74652117460626576626578979)
    ·
      refine ⟨111978176190939864939868469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74652117460626576626578979 111978176190939864939868469)
      ·
        refine ⟨10497954017900612338112669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111978176190939864939868469 10497954017900612338112669)
        ·
          refine ⟨3936732756712729626792251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10497954017900612338112669 3936732756712729626792251)
          ·
            refine ⟨5905099135069094440188377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3936732756712729626792251 5905099135069094440188377)
            ·
              refine ⟨4428824351301820830141283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5905099135069094440188377 4428824351301820830141283)
              ·
                refine ⟨6643236526952731245211925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4428824351301820830141283 6643236526952731245211925)
                ·
                  refine ⟨311401712200909277119309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6643236526952731245211925 311401712200909277119309)
                  ·
                    rfl

theorem cell23_5458074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 1, 6].length) (baseStart_5458074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458074 prefixEnd_5458074 := by exact prefixLift 5458074
  have htrace : WordTrace (prefixWord ++ tailWord_5458074) baseStart_5458074 baseEnd_5458074 := by
    simpa [prefixWord, tailWord_5458074, baseEnd_5458074] using wordTrace_append hprefix tailTrace_5458074
  have hstable : (prefixWord ++ tailWord_5458074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458074).length < 2 ^ (prefixWord ++ tailWord_5458074).sum := by decide
  have hdescent : baseEnd_5458074 < baseStart_5458074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458103 : List Nat := [1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_5458103 : Nat := 118140960795 + 5458103 * 2 ^ 59
def prefixEnd_5458103 : Nat := 4983230072969 + 3 ^ 40 * 5458103 * 2
def baseEnd_5458103 : Nat := 2802630300747163880611147

theorem tailTrace_5458103 : CollatzResearch.WordTrace tailWord_5458103 prefixEnd_5458103 2802630300747163880611147 := by
  unfold tailWord_5458103
  simp only [CollatzResearch.WordTrace]
  refine ⟨199073370945232475623682963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132715580630154983749121975 199073370945232475623682963)
  ·
    refine ⟨298610056417848713435524445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199073370945232475623682963 298610056417848713435524445)
    ·
      refine ⟨111978771156693267538321667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298610056417848713435524445 111978771156693267538321667)
      ·
        refine ⟨167968156735039901307482501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111978771156693267538321667 167968156735039901307482501)
        ·
          refine ⟨31494029387819981495152969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167968156735039901307482501 31494029387819981495152969)
          ·
            refine ⟨23620522040864986121364727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31494029387819981495152969 23620522040864986121364727)
            ·
              refine ⟨35430783061297479182047091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23620522040864986121364727 35430783061297479182047091)
              ·
                refine ⟨53146174591946218773070637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35430783061297479182047091 53146174591946218773070637)
                ·
                  refine ⟨19929815471979832039901489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53146174591946218773070637 19929815471979832039901489)
                  ·
                    refine ⟨14947361603984874029926117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19929815471979832039901489 14947361603984874029926117)
                    ·
                      refine ⟨2802630300747163880611147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14947361603984874029926117 2802630300747163880611147)
                      ·
                        rfl

theorem cell23_5458103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_5458103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458103 prefixEnd_5458103 := by exact prefixLift 5458103
  have htrace : WordTrace (prefixWord ++ tailWord_5458103) baseStart_5458103 baseEnd_5458103 := by
    simpa [prefixWord, tailWord_5458103, baseEnd_5458103] using wordTrace_append hprefix tailTrace_5458103
  have hstable : (prefixWord ++ tailWord_5458103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458103).length < 2 ^ (prefixWord ++ tailWord_5458103).sum := by decide
  have hdescent : baseEnd_5458103 < baseStart_5458103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458113 : List Nat := [1, 2, 6, 1, 13]
def baseStart_5458113 : Nat := 118140960795 + 5458113 * 2 ^ 59
def prefixEnd_5458113 : Nat := 4983230072969 + 3 ^ 40 * 5458113 * 2
def baseEnd_5458113 : Nat := 3844493052885746010269

theorem tailTrace_5458113 : CollatzResearch.WordTrace tailWord_5458113 prefixEnd_5458113 3844493052885746010269 := by
  unfold tailWord_5458113
  simp only [CollatzResearch.WordTrace]
  refine ⟨199073735675196247331546993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132715823783464164887697995 199073735675196247331546993)
  ·
    refine ⟨149305301756397185498660245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199073735675196247331546993 149305301756397185498660245)
    ·
      refine ⟨6998686019831118070249699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 149305301756397185498660245 6998686019831118070249699)
      ·
        refine ⟨10498029029746677105374549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6998686019831118070249699 10498029029746677105374549)
        ·
          refine ⟨3844493052885746010269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 10498029029746677105374549 3844493052885746010269)
          ·
            rfl

theorem cell23_5458113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 13].length) (baseStart_5458113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458113 prefixEnd_5458113 := by exact prefixLift 5458113
  have htrace : WordTrace (prefixWord ++ tailWord_5458113) baseStart_5458113 baseEnd_5458113 := by
    simpa [prefixWord, tailWord_5458113, baseEnd_5458113] using wordTrace_append hprefix tailTrace_5458113
  have hstable : (prefixWord ++ tailWord_5458113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458113).length < 2 ^ (prefixWord ++ tailWord_5458113).sum := by decide
  have hdescent : baseEnd_5458113 < baseStart_5458113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458123 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 3]
def baseStart_5458123 : Nat := 118140960795 + 5458123 * 2 ^ 59
def prefixEnd_5458123 : Nat := 4983230072969 + 3 ^ 40 * 5458123 * 2
def baseEnd_5458123 : Nat := 2802640570360253802361055

theorem tailTrace_5458123 : CollatzResearch.WordTrace tailWord_5458123 prefixEnd_5458123 2802640570360253802361055 := by
  unfold tailWord_5458123
  simp only [CollatzResearch.WordTrace]
  refine ⟨199074100405160019039411023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132716066936773346026274015 199074100405160019039411023)
  ·
    refine ⟨298611150607740028559116535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199074100405160019039411023 298611150607740028559116535)
    ·
      refine ⟨447916725911610042838674803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298611150607740028559116535 447916725911610042838674803)
      ·
        refine ⟨671875088867415064258012205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447916725911610042838674803 671875088867415064258012205)
        ·
          refine ⟨251953158325280649096754577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 671875088867415064258012205 251953158325280649096754577)
          ·
            refine ⟨188964868743960486822565933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251953158325280649096754577 188964868743960486822565933)
            ·
              refine ⟨70861825778985182558462225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188964868743960486822565933 70861825778985182558462225)
              ·
                refine ⟨53146369334238886918846669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70861825778985182558462225 53146369334238886918846669)
                ·
                  refine ⟨19929888500339582594567501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53146369334238886918846669 19929888500339582594567501)
                  ·
                    refine ⟨7473708187627343472962813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19929888500339582594567501 7473708187627343472962813)
                    ·
                      refine ⟨2802640570360253802361055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7473708187627343472962813 2802640570360253802361055)
                      ·
                        rfl

theorem cell23_5458123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 3].length) (baseStart_5458123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458123 prefixEnd_5458123 := by exact prefixLift 5458123
  have htrace : WordTrace (prefixWord ++ tailWord_5458123) baseStart_5458123 baseEnd_5458123 := by
    simpa [prefixWord, tailWord_5458123, baseEnd_5458123] using wordTrace_append hprefix tailTrace_5458123
  have hstable : (prefixWord ++ tailWord_5458123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458123).length < 2 ^ (prefixWord ++ tailWord_5458123).sum := by decide
  have hdescent : baseEnd_5458123 < baseStart_5458123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458130 : List Nat := [3, 2, 2, 2, 1, 4, 1, 8]
def baseStart_5458130 : Nat := 118140960795 + 5458130 * 2 ^ 59
def prefixEnd_5458130 : Nat := 4983230072969 + 3 ^ 40 * 5458130 * 2
def baseEnd_5458130 : Nat := 103801635730549454628649

theorem tailTrace_5458130 : CollatzResearch.WordTrace tailWord_5458130 prefixEnd_5458130 103801635730549454628649 := by
  unfold tailWord_5458130
  simp only [CollatzResearch.WordTrace]
  refine ⟨49768588929033664808728961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132716237144089772823277229 49768588929033664808728961)
  ·
    refine ⟨37326441696775248606546721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49768588929033664808728961 37326441696775248606546721)
    ·
      refine ⟨27994831272581436454910041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37326441696775248606546721 27994831272581436454910041)
      ·
        refine ⟨20996123454436077341182531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27994831272581436454910041 20996123454436077341182531)
        ·
          refine ⟨31494185181654116011773797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20996123454436077341182531 31494185181654116011773797)
          ·
            refine ⟨5905159721560146752207587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31494185181654116011773797 5905159721560146752207587)
            ·
              refine ⟨8857739582340220128311381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5905159721560146752207587 8857739582340220128311381)
              ·
                refine ⟨103801635730549454628649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8857739582340220128311381 103801635730549454628649)
                ·
                  rfl

theorem cell23_5458130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 8].length) (baseStart_5458130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458130 prefixEnd_5458130 := by exact prefixLift 5458130
  have htrace : WordTrace (prefixWord ++ tailWord_5458130) baseStart_5458130 baseEnd_5458130 := by
    simpa [prefixWord, tailWord_5458130, baseEnd_5458130] using wordTrace_append hprefix tailTrace_5458130
  have hstable : (prefixWord ++ tailWord_5458130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458130).length < 2 ^ (prefixWord ++ tailWord_5458130).sum := by decide
  have hdescent : baseEnd_5458130 < baseStart_5458130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458134 : List Nat := [5, 2, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_5458134 : Nat := 118140960795 + 5458134 * 2 ^ 59
def prefixEnd_5458134 : Nat := 4983230072969 + 3 ^ 40 * 5458134 * 2
def baseEnd_5458134 : Nat := 934215406215817753107835

theorem tailTrace_5458134 : CollatzResearch.WordTrace tailWord_5458134 prefixEnd_5458134 934215406215817753107835 := by
  unfold tailWord_5458134
  simp only [CollatzResearch.WordTrace]
  refine ⟨12442156350507510494878841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132716334405413445278707637 12442156350507510494878841)
  ·
    refine ⟨9331617262880632871159131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12442156350507510494878841 9331617262880632871159131)
    ·
      refine ⟨13997425894320949306738697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9331617262880632871159131 13997425894320949306738697)
      ·
        refine ⟨10498069420740711980054023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13997425894320949306738697 10498069420740711980054023)
        ·
          refine ⟨15747104131111067970081035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10498069420740711980054023 15747104131111067970081035)
          ·
            refine ⟨23620656196666601955121553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15747104131111067970081035 23620656196666601955121553)
            ·
              refine ⟨17715492147499951466341165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23620656196666601955121553 17715492147499951466341165)
              ·
                refine ⟨6643309555312481799877937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17715492147499951466341165 6643309555312481799877937)
                ·
                  refine ⟨4982482166484361349908453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6643309555312481799877937 4982482166484361349908453)
                  ·
                    refine ⟨934215406215817753107835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4982482166484361349908453 934215406215817753107835)
                    ·
                      rfl

theorem cell23_5458134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_5458134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458134 prefixEnd_5458134 := by exact prefixLift 5458134
  have htrace : WordTrace (prefixWord ++ tailWord_5458134) baseStart_5458134 baseEnd_5458134 := by
    simpa [prefixWord, tailWord_5458134, baseEnd_5458134] using wordTrace_append hprefix tailTrace_5458134
  have hstable : (prefixWord ++ tailWord_5458134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458134).length < 2 ^ (prefixWord ++ tailWord_5458134).sum := by decide
  have hdescent : baseEnd_5458134 < baseStart_5458134 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458147 : List Nat := [1, 1, 1, 8, 1, 1, 3, 7]
def baseStart_5458147 : Nat := 118140960795 + 5458147 * 2 ^ 59
def prefixEnd_5458147 : Nat := 4983230072969 + 3 ^ 40 * 5458147 * 2
def baseEnd_5458147 : Nat := 103801959033183766980035

theorem tailTrace_5458147 : CollatzResearch.WordTrace tailWord_5458147 prefixEnd_5458147 103801959033183766980035 := by
  unfold tailWord_5458147
  simp only [CollatzResearch.WordTrace]
  refine ⟨199074975757073071138284695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132716650504715380758856463 199074975757073071138284695)
  ·
    refine ⟨298612463635609606707427043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199074975757073071138284695 298612463635609606707427043)
    ·
      refine ⟨447918695453414410061140565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298612463635609606707427043 447918695453414410061140565)
      ·
        refine ⟨5249047212344700117903991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 447918695453414410061140565 5249047212344700117903991)
        ·
          refine ⟨7873570818517050176855987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5249047212344700117903991 7873570818517050176855987)
          ·
            refine ⟨11810356227775575265283981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7873570818517050176855987 11810356227775575265283981)
            ·
              refine ⟨4428883585415840724481493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11810356227775575265283981 4428883585415840724481493)
              ·
                refine ⟨103801959033183766980035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4428883585415840724481493 103801959033183766980035)
                ·
                  rfl

theorem cell23_5458147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 7].length) (baseStart_5458147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458147 prefixEnd_5458147 := by exact prefixLift 5458147
  have htrace : WordTrace (prefixWord ++ tailWord_5458147) baseStart_5458147 baseEnd_5458147 := by
    simpa [prefixWord, tailWord_5458147, baseEnd_5458147] using wordTrace_append hprefix tailTrace_5458147
  have hstable : (prefixWord ++ tailWord_5458147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458147).length < 2 ^ (prefixWord ++ tailWord_5458147).sum := by decide
  have hdescent : baseEnd_5458147 < baseStart_5458147 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458197 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 1, 4, 2]
def baseStart_5458197 : Nat := 118140960795 + 5458197 * 2 ^ 59
def prefixEnd_5458197 : Nat := 4983230072969 + 3 ^ 40 * 5458197 * 2
def baseEnd_5458197 : Nat := 2802678567928686512835715

theorem tailTrace_5458197 : CollatzResearch.WordTrace tailWord_5458197 prefixEnd_5458197 2802678567928686512835715 := by
  unfold tailWord_5458197
  simp only [CollatzResearch.WordTrace]
  refine ⟨199076799406891929677604845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132717866271261286451736563 199076799406891929677604845)
  ·
    refine ⟨74653799777584473629101817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199076799406891929677604845 74653799777584473629101817)
    ·
      refine ⟨55990349833188355221826363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74653799777584473629101817 55990349833188355221826363)
      ·
        refine ⟨83985524749782532832739545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55990349833188355221826363 83985524749782532832739545)
        ·
          refine ⟨62989143562336899624554659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83985524749782532832739545 62989143562336899624554659)
          ·
            refine ⟨94483715343505349436831989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62989143562336899624554659 94483715343505349436831989)
            ·
              refine ⟨8857848313453626509702999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94483715343505349436831989 8857848313453626509702999)
              ·
                refine ⟨13286772470180439764554499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8857848313453626509702999 13286772470180439764554499)
                ·
                  refine ⟨19930158705270659646831749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13286772470180439764554499 19930158705270659646831749)
                  ·
                    refine ⟨3736904757238248683780953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19930158705270659646831749 3736904757238248683780953)
                    ·
                      refine ⟨2802678567928686512835715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3736904757238248683780953 2802678567928686512835715)
                      ·
                        rfl

theorem cell23_5458197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_5458197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458197 prefixEnd_5458197 := by exact prefixLift 5458197
  have htrace : WordTrace (prefixWord ++ tailWord_5458197) baseStart_5458197 baseEnd_5458197 := by
    simpa [prefixWord, tailWord_5458197, baseEnd_5458197] using wordTrace_append hprefix tailTrace_5458197
  have hstable : (prefixWord ++ tailWord_5458197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458197).length < 2 ^ (prefixWord ++ tailWord_5458197).sum := by decide
  have hdescent : baseEnd_5458197 < baseStart_5458197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458203 : List Nat := [1, 1, 1, 1, 1, 1, 8, 2, 7]
def baseStart_5458203 : Nat := 118140960795 + 5458203 * 2 ^ 59
def prefixEnd_5458203 : Nat := 4983230072969 + 3 ^ 40 * 5458203 * 2
def baseEnd_5458203 : Nat := 311409072090290387706743

theorem tailTrace_5458203 : CollatzResearch.WordTrace tailWord_5458203 prefixEnd_5458203 311409072090290387706743 := by
  unfold tailWord_5458203
  simp only [CollatzResearch.WordTrace]
  refine ⟨199077018244870192702323263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132718012163246795134882175 199077018244870192702323263)
  ·
    refine ⟨298615527367305289053484895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199077018244870192702323263 298615527367305289053484895)
    ·
      refine ⟨447923291050957933580227343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298615527367305289053484895 447923291050957933580227343)
      ·
        refine ⟨671884936576436900370341015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447923291050957933580227343 671884936576436900370341015)
        ·
          refine ⟨1007827404864655350555511523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671884936576436900370341015 1007827404864655350555511523)
          ·
            refine ⟨1511741107296983025833267285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007827404864655350555511523 1511741107296983025833267285)
            ·
              refine ⟨17715716101136519833983601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1511741107296983025833267285 17715716101136519833983601)
              ·
                refine ⟨13286787075852389875487701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17715716101136519833983601 13286787075852389875487701)
                ·
                  refine ⟨311409072090290387706743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13286787075852389875487701 311409072090290387706743)
                  ·
                    rfl

theorem cell23_5458203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 2, 7].length) (baseStart_5458203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458203 prefixEnd_5458203 := by exact prefixLift 5458203
  have htrace : WordTrace (prefixWord ++ tailWord_5458203) baseStart_5458203 baseEnd_5458203 := by
    simpa [prefixWord, tailWord_5458203, baseEnd_5458203] using wordTrace_append hprefix tailTrace_5458203
  have hstable : (prefixWord ++ tailWord_5458203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458203).length < 2 ^ (prefixWord ++ tailWord_5458203).sum := by decide
  have hdescent : baseEnd_5458203 < baseStart_5458203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458243 : List Nat := [1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 7]
def baseStart_5458243 : Nat := 118140960795 + 5458243 * 2 ^ 59
def prefixEnd_5458243 : Nat := 4983230072969 + 3 ^ 40 * 5458243 * 2
def baseEnd_5458243 : Nat := 2802702188038793332860503

theorem tailTrace_5458243 : CollatzResearch.WordTrace tailWord_5458243 prefixEnd_5458243 2802702188038793332860503 := by
  unfold tailWord_5458243
  simp only [CollatzResearch.WordTrace]
  refine ⟨199078477164725279533779383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132718984776483519689186255 199078477164725279533779383)
  ·
    refine ⟨298617715747087919300669075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199078477164725279533779383 298617715747087919300669075)
    ·
      refine ⟨447926573620631878951003613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298617715747087919300669075 447926573620631878951003613)
      ·
        refine ⟨167972465107736954606626355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 447926573620631878951003613 167972465107736954606626355)
        ·
          refine ⟨251958697661605431909939533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167972465107736954606626355 251958697661605431909939533)
          ·
            refine ⟨94484511623102036966227325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 251958697661605431909939533 94484511623102036966227325)
            ·
              refine ⟨35431691858663263862335247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94484511623102036966227325 35431691858663263862335247)
              ·
                refine ⟨53147537787994895793502871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35431691858663263862335247 53147537787994895793502871)
                ·
                  refine ⟨79721306681992343690254307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53147537787994895793502871 79721306681992343690254307)
                  ·
                    refine ⟨119581960022988515535381461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79721306681992343690254307 119581960022988515535381461)
                    ·
                      refine ⟨2802702188038793332860503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119581960022988515535381461 2802702188038793332860503)
                      ·
                        rfl

theorem cell23_5458243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_5458243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458243 prefixEnd_5458243 := by exact prefixLift 5458243
  have htrace : WordTrace (prefixWord ++ tailWord_5458243) baseStart_5458243 baseEnd_5458243 := by
    simpa [prefixWord, tailWord_5458243, baseEnd_5458243] using wordTrace_append hprefix tailTrace_5458243
  have hstable : (prefixWord ++ tailWord_5458243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458243).length < 2 ^ (prefixWord ++ tailWord_5458243).sum := by decide
  have hdescent : baseEnd_5458243 < baseStart_5458243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458273 : List Nat := [1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_5458273 : Nat := 118140960795 + 5458273 * 2 ^ 59
def prefixEnd_5458273 : Nat := 4983230072969 + 3 ^ 40 * 5458273 * 2
def baseEnd_5458273 : Nat := 2802717592458428215485365

theorem tailTrace_5458273 : CollatzResearch.WordTrace tailWord_5458273 prefixEnd_5458273 2802717592458428215485365 := by
  unfold tailWord_5458273
  simp only [CollatzResearch.WordTrace]
  refine ⟨199079571354616594657371473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132719714236411063104914315 199079571354616594657371473)
  ·
    refine ⟨149309678515962445993028605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199079571354616594657371473 149309678515962445993028605)
    ·
      refine ⟨55991129443485917247385727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149309678515962445993028605 55991129443485917247385727)
      ·
        refine ⟨83986694165228875871078591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55991129443485917247385727 83986694165228875871078591)
        ·
          refine ⟨125980041247843313806617887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83986694165228875871078591 125980041247843313806617887)
          ·
            refine ⟨188970061871764970709926831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125980041247843313806617887 188970061871764970709926831)
            ·
              refine ⟨283455092807647456064890247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188970061871764970709926831 283455092807647456064890247)
              ·
                refine ⟨425182639211471184097335371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283455092807647456064890247 425182639211471184097335371)
                ·
                  refine ⟨637773958817206776146003057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425182639211471184097335371 637773958817206776146003057)
                  ·
                    refine ⟨478330469112905082109502293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 637773958817206776146003057 478330469112905082109502293)
                    ·
                      refine ⟨2802717592458428215485365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 478330469112905082109502293 2802717592458428215485365)
                      ·
                        rfl

theorem cell23_5458273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_5458273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458273 prefixEnd_5458273 := by exact prefixLift 5458273
  have htrace : WordTrace (prefixWord ++ tailWord_5458273) baseStart_5458273 baseEnd_5458273 := by
    simpa [prefixWord, tailWord_5458273, baseEnd_5458273] using wordTrace_append hprefix tailTrace_5458273
  have hstable : (prefixWord ++ tailWord_5458273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458273).length < 2 ^ (prefixWord ++ tailWord_5458273).sum := by decide
  have hdescent : baseEnd_5458273 < baseStart_5458273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458283 : List Nat := [1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 6]
def baseStart_5458283 : Nat := 118140960795 + 5458283 * 2 ^ 59
def prefixEnd_5458283 : Nat := 4983230072969 + 3 ^ 40 * 5458283 * 2
def baseEnd_5458283 : Nat := 2802722727264973176360319

theorem tailTrace_5458283 : CollatzResearch.WordTrace tailWord_5458283 prefixEnd_5458283 2802722727264973176360319 := by
  unfold tailWord_5458283
  simp only [CollatzResearch.WordTrace]
  refine ⟨199079936084580366365235503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132719957389720244243490335 199079936084580366365235503)
  ·
    refine ⟨298619904126870549547853255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199079936084580366365235503 298619904126870549547853255)
    ·
      refine ⟨447929856190305824321779883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298619904126870549547853255 447929856190305824321779883)
      ·
        refine ⟨671894784285458736482669825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447929856190305824321779883 671894784285458736482669825)
        ·
          refine ⟨503921088214094052362002369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 671894784285458736482669825 503921088214094052362002369)
          ·
            refine ⟨377940816160570539271501777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503921088214094052362002369 377940816160570539271501777)
            ·
              refine ⟨283455612120427904453626333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377940816160570539271501777 283455612120427904453626333)
              ·
                refine ⟨106295854545160464170109875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283455612120427904453626333 106295854545160464170109875)
                ·
                  refine ⟨159443781817740696255164813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106295854545160464170109875 159443781817740696255164813)
                  ·
                    refine ⟨59791418181652761095686805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159443781817740696255164813 59791418181652761095686805)
                    ·
                      refine ⟨2802722727264973176360319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59791418181652761095686805 2802722727264973176360319)
                      ·
                        rfl

theorem cell23_5458283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 6].length) (baseStart_5458283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458283 prefixEnd_5458283 := by exact prefixLift 5458283
  have htrace : WordTrace (prefixWord ++ tailWord_5458283) baseStart_5458283 baseEnd_5458283 := by
    simpa [prefixWord, tailWord_5458283, baseEnd_5458283] using wordTrace_append hprefix tailTrace_5458283
  have hstable : (prefixWord ++ tailWord_5458283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458283).length < 2 ^ (prefixWord ++ tailWord_5458283).sum := by decide
  have hdescent : baseEnd_5458283 < baseStart_5458283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458324 : List Nat := [2, 4, 2, 1, 3, 1, 1, 1, 1, 4, 3]
def baseStart_5458324 : Nat := 118140960795 + 5458324 * 2 ^ 59
def prefixEnd_5458324 : Nat := 4983230072969 + 3 ^ 40 * 5458324 * 2
def baseEnd_5458324 : Nat := 2802743779971807515947631

theorem tailTrace_5458324 : CollatzResearch.WordTrace tailWord_5458324 prefixEnd_5458324 2802743779971807515947631 := by
  unfold tailWord_5458324
  simp only [CollatzResearch.WordTrace]
  refine ⟨99540715738715915183739013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132720954318287886911652017 99540715738715915183739013)
  ·
    refine ⟨18663884201009234096951065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99540715738715915183739013 18663884201009234096951065)
    ·
      refine ⟨13997913150756925572713299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18663884201009234096951065 13997913150756925572713299)
      ·
        refine ⟨20996869726135388359069949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13997913150756925572713299 20996869726135388359069949)
        ·
          refine ⟨7873826147300770634651231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20996869726135388359069949 7873826147300770634651231)
          ·
            refine ⟨11810739220951155951976847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7873826147300770634651231 11810739220951155951976847)
            ·
              refine ⟨17716108831426733927965271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11810739220951155951976847 17716108831426733927965271)
              ·
                refine ⟨26574163247140100891947907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17716108831426733927965271 26574163247140100891947907)
                ·
                  refine ⟨39861244870710151337921861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26574163247140100891947907 39861244870710151337921861)
                  ·
                    refine ⟨7473983413258153375860349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39861244870710151337921861 7473983413258153375860349)
                    ·
                      refine ⟨2802743779971807515947631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7473983413258153375860349 2802743779971807515947631)
                      ·
                        rfl

theorem cell23_5458324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_5458324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458324 prefixEnd_5458324 := by exact prefixLift 5458324
  have htrace : WordTrace (prefixWord ++ tailWord_5458324) baseStart_5458324 baseEnd_5458324 := by
    simpa [prefixWord, tailWord_5458324, baseEnd_5458324] using wordTrace_append hprefix tailTrace_5458324
  have hstable : (prefixWord ++ tailWord_5458324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458324).length < 2 ^ (prefixWord ++ tailWord_5458324).sum := by decide
  have hdescent : baseEnd_5458324 < baseStart_5458324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458344 : List Nat := [2, 1, 6, 1, 1, 1, 3, 2, 6]
def baseStart_5458344 : Nat := 118140960795 + 5458344 * 2 ^ 59
def prefixEnd_5458344 : Nat := 4983230072969 + 3 ^ 40 * 5458344 * 2
def baseEnd_5458344 : Nat := 311417116620544159744171

theorem tailTrace_5458344 : CollatzResearch.WordTrace tailWord_5458344 prefixEnd_5458344 311417116620544159744171 := by
  unfold tailWord_5458344
  simp only [CollatzResearch.WordTrace]
  refine ⟨99541080468679686891603043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132721440624906249188804057 99541080468679686891603043)
  ·
    refine ⟨149311620703019530337404565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99541080468679686891603043 149311620703019530337404565)
    ·
      refine ⟨6998982220454040484565839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 149311620703019530337404565 6998982220454040484565839)
      ·
        refine ⟨10498473330681060726848759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6998982220454040484565839 10498473330681060726848759)
        ·
          refine ⟨15747709996021591090273139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10498473330681060726848759 15747709996021591090273139)
          ·
            refine ⟨23621564994032386635409709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15747709996021591090273139 23621564994032386635409709)
            ·
              refine ⟨8858086872762144988278641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23621564994032386635409709 8858086872762144988278641)
              ·
                refine ⟨6643565154571608741208981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8858086872762144988278641 6643565154571608741208981)
                ·
                  refine ⟨311417116620544159744171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6643565154571608741208981 311417116620544159744171)
                  ·
                    rfl

theorem cell23_5458344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 2, 6].length) (baseStart_5458344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458344 prefixEnd_5458344 := by exact prefixLift 5458344
  have htrace : WordTrace (prefixWord ++ tailWord_5458344) baseStart_5458344 baseEnd_5458344 := by
    simpa [prefixWord, tailWord_5458344, baseEnd_5458344] using wordTrace_append hprefix tailTrace_5458344
  have hstable : (prefixWord ++ tailWord_5458344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458344).length < 2 ^ (prefixWord ++ tailWord_5458344).sum := by decide
  have hdescent : baseEnd_5458344 < baseStart_5458344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458354 : List Nat := [3, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3]
def baseStart_5458354 : Nat := 118140960795 + 5458354 * 2 ^ 59
def prefixEnd_5458354 : Nat := 4983230072969 + 3 ^ 40 * 5458354 * 2
def baseEnd_5458354 : Nat := 2802759184391442398572493

theorem tailTrace_5458354 : CollatzResearch.WordTrace tailWord_5458354 prefixEnd_5458354 2802759184391442398572493 := by
  unfold tailWord_5458354
  simp only [CollatzResearch.WordTrace]
  refine ⟨49770631416830786372767529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132721683778215430327380077 49770631416830786372767529)
  ·
    refine ⟨37327973562623089779575647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49770631416830786372767529 37327973562623089779575647)
    ·
      refine ⟨55991960343934634669363471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37327973562623089779575647 55991960343934634669363471)
      ·
        refine ⟨83987940515901952004045207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55991960343934634669363471 83987940515901952004045207)
        ·
          refine ⟨125981910773852928006067811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83987940515901952004045207 125981910773852928006067811)
          ·
            refine ⟨188972866160779392009101717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125981910773852928006067811 188972866160779392009101717)
            ·
              refine ⟨8858103101286534000426643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 188972866160779392009101717 8858103101286534000426643)
              ·
                refine ⟨13287154651929801000639965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8858103101286534000426643 13287154651929801000639965)
                ·
                  refine ⟨4982682994473675375239987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13287154651929801000639965 4982682994473675375239987)
                  ·
                    refine ⟨7474024491710513062859981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4982682994473675375239987 7474024491710513062859981)
                    ·
                      refine ⟨2802759184391442398572493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7474024491710513062859981 2802759184391442398572493)
                      ·
                        rfl

theorem cell23_5458354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_5458354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458354 prefixEnd_5458354 := by exact prefixLift 5458354
  have htrace : WordTrace (prefixWord ++ tailWord_5458354) baseStart_5458354 baseEnd_5458354 := by
    simpa [prefixWord, tailWord_5458354, baseEnd_5458354] using wordTrace_append hprefix tailTrace_5458354
  have hstable : (prefixWord ++ tailWord_5458354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458354).length < 2 ^ (prefixWord ++ tailWord_5458354).sum := by decide
  have hdescent : baseEnd_5458354 < baseStart_5458354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458364 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 1, 5, 2]
def baseStart_5458364 : Nat := 118140960795 + 5458364 * 2 ^ 59
def prefixEnd_5458364 : Nat := 4983230072969 + 3 ^ 40 * 5458364 * 2
def baseEnd_5458364 : Nat := 2802764319197987359447447

theorem tailTrace_5458364 : CollatzResearch.WordTrace tailWord_5458364 prefixEnd_5458364 2802764319197987359447447 := by
  unfold tailWord_5458364
  simp only [CollatzResearch.WordTrace]
  refine ⟨99541445198643458599467073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132721926931524611465956097 99541445198643458599467073)
  ·
    refine ⟨74656083898982593949600305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99541445198643458599467073 74656083898982593949600305)
    ·
      refine ⟨55992062924236945462200229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74656083898982593949600305 55992062924236945462200229)
      ·
        refine ⟨10498511798294427274162543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55992062924236945462200229 10498511798294427274162543)
        ·
          refine ⟨15747767697441640911243815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10498511798294427274162543 15747767697441640911243815)
          ·
            refine ⟨23621651546162461366865723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15747767697441640911243815 23621651546162461366865723)
            ·
              refine ⟨35432477319243692050298585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23621651546162461366865723 35432477319243692050298585)
              ·
                refine ⟨26574357989432769037723939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35432477319243692050298585 26574357989432769037723939)
                ·
                  refine ⟨39861536984149153556585909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26574357989432769037723939 39861536984149153556585909)
                  ·
                    refine ⟨3737019092263983145929929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39861536984149153556585909 3737019092263983145929929)
                    ·
                      refine ⟨2802764319197987359447447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3737019092263983145929929 2802764319197987359447447)
                      ·
                        rfl

theorem cell23_5458364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_5458364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458364 prefixEnd_5458364 := by exact prefixLift 5458364
  have htrace : WordTrace (prefixWord ++ tailWord_5458364) baseStart_5458364 baseEnd_5458364 := by
    simpa [prefixWord, tailWord_5458364, baseEnd_5458364] using wordTrace_append hprefix tailTrace_5458364
  have hstable : (prefixWord ++ tailWord_5458364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458364).length < 2 ^ (prefixWord ++ tailWord_5458364).sum := by decide
  have hdescent : baseEnd_5458364 < baseStart_5458364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458377 : List Nat := [1, 2, 1, 1, 2, 1, 5, 4, 1, 1, 4]
def baseStart_5458377 : Nat := 118140960795 + 5458377 * 2 ^ 59
def prefixEnd_5458377 : Nat := 4983230072969 + 3 ^ 40 * 5458377 * 2
def baseEnd_5458377 : Nat := 2802770994446495808584887

theorem tailTrace_5458377 : CollatzResearch.WordTrace tailWord_5458377 prefixEnd_5458377 2802770994446495808584887 := by
  unfold tailWord_5458377
  simp only [CollatzResearch.WordTrace]
  refine ⟨199083364546239820419157385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132722243030826546946104923 199083364546239820419157385)
  ·
    refine ⟨149312523409679865314368039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199083364546239820419157385 149312523409679865314368039)
    ·
      refine ⟨223968785114519797971552059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149312523409679865314368039 223968785114519797971552059)
      ·
        refine ⟨335953177671779696957328089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223968785114519797971552059 335953177671779696957328089)
        ·
          refine ⟨251964883253834772717996067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335953177671779696957328089 251964883253834772717996067)
          ·
            refine ⟨377947324880752159076994101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251964883253834772717996067 377947324880752159076994101)
            ·
              refine ⟨35432561707570514913468197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 377947324880752159076994101 35432561707570514913468197)
              ·
                refine ⟨6643605320169471546275287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35432561707570514913468197 6643605320169471546275287)
                ·
                  refine ⟨9965407980254207319412931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6643605320169471546275287 9965407980254207319412931)
                  ·
                    refine ⟨14948111970381310979119397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9965407980254207319412931 14948111970381310979119397)
                    ·
                      refine ⟨2802770994446495808584887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14948111970381310979119397 2802770994446495808584887)
                      ·
                        rfl

theorem cell23_5458377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 1, 4].length) (baseStart_5458377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458377 prefixEnd_5458377 := by exact prefixLift 5458377
  have htrace : WordTrace (prefixWord ++ tailWord_5458377) baseStart_5458377 baseEnd_5458377 := by
    simpa [prefixWord, tailWord_5458377, baseEnd_5458377] using wordTrace_append hprefix tailTrace_5458377
  have hstable : (prefixWord ++ tailWord_5458377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458377).length < 2 ^ (prefixWord ++ tailWord_5458377).sum := by decide
  have hdescent : baseEnd_5458377 < baseStart_5458377 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458388 : List Nat := [2, 4, 1, 2, 2, 1, 3, 3, 1, 1, 3]
def baseStart_5458388 : Nat := 118140960795 + 5458388 * 2 ^ 59
def prefixEnd_5458388 : Nat := 4983230072969 + 3 ^ 40 * 5458388 * 2
def baseEnd_5458388 : Nat := 2802776642733695265547337

theorem tailTrace_5458388 : CollatzResearch.WordTrace tailWord_5458388 prefixEnd_5458388 2802776642733695265547337 := by
  unfold tailWord_5458388
  simp only [CollatzResearch.WordTrace]
  refine ⟨99541882874599984648903909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132722510499466646198538545 99541882874599984648903909)
  ·
    refine ⟨18664103038987497121669483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99541882874599984648903909 18664103038987497121669483)
    ·
      refine ⟨27996154558481245682504225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18664103038987497121669483 27996154558481245682504225)
      ·
        refine ⟨20997115918860934261878169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27996154558481245682504225 20997115918860934261878169)
        ·
          refine ⟨15747836939145700696408627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20997115918860934261878169 15747836939145700696408627)
          ·
            refine ⟨23621755408718551044612941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15747836939145700696408627 23621755408718551044612941)
            ·
              refine ⟨8858158278269456641729853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23621755408718551044612941 8858158278269456641729853)
              ·
                refine ⟨3321809354351046240648695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8858158278269456641729853 3321809354351046240648695)
                ·
                  refine ⟨4982714031526569360973043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321809354351046240648695 4982714031526569360973043)
                  ·
                    refine ⟨7474071047289854041459565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4982714031526569360973043 7474071047289854041459565)
                    ·
                      refine ⟨2802776642733695265547337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7474071047289854041459565 2802776642733695265547337)
                      ·
                        rfl

theorem cell23_5458388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 3, 3, 1, 1, 3].length) (baseStart_5458388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458388 prefixEnd_5458388 := by exact prefixLift 5458388
  have htrace : WordTrace (prefixWord ++ tailWord_5458388) baseStart_5458388 baseEnd_5458388 := by
    simpa [prefixWord, tailWord_5458388, baseEnd_5458388] using wordTrace_append hprefix tailTrace_5458388
  have hstable : (prefixWord ++ tailWord_5458388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458388).length < 2 ^ (prefixWord ++ tailWord_5458388).sum := by decide
  have hdescent : baseEnd_5458388 < baseStart_5458388 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458405 : List Nat := [1, 3, 1, 5, 2, 1, 3, 2, 1, 1, 3]
def baseStart_5458405 : Nat := 118140960795 + 5458405 * 2 ^ 59
def prefixEnd_5458405 : Nat := 4983230072969 + 3 ^ 40 * 5458405 * 2
def baseEnd_5458405 : Nat := 2802785371904821699034759

theorem tailTrace_5458405 : CollatzResearch.WordTrace tailWord_5458405 prefixEnd_5458405 2802785371904821699034759 := by
  unfold tailWord_5458405
  simp only [CollatzResearch.WordTrace]
  refine ⟨199084385790138381201176669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132722923860092254134117779 199084385790138381201176669)
  ·
    refine ⟨74656644671301892950441251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199084385790138381201176669 74656644671301892950441251)
    ·
      refine ⟨111984967006952839425661877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74656644671301892950441251 111984967006952839425661877)
      ·
        refine ⟨10498590656901828696155801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111984967006952839425661877 10498590656901828696155801)
        ·
          refine ⟨7873942992676371522116851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10498590656901828696155801 7873942992676371522116851)
          ·
            refine ⟨11810914489014557283175277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7873942992676371522116851 11810914489014557283175277)
            ·
              refine ⟨4429092933380458981190729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11810914489014557283175277 4429092933380458981190729)
              ·
                refine ⟨3321819700035344235893047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4429092933380458981190729 3321819700035344235893047)
                ·
                  refine ⟨4982729550053016353839571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3321819700035344235893047 4982729550053016353839571)
                  ·
                    refine ⟨7474094325079524530759357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4982729550053016353839571 7474094325079524530759357)
                    ·
                      refine ⟨2802785371904821699034759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7474094325079524530759357 2802785371904821699034759)
                      ·
                        rfl

theorem cell23_5458405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_5458405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458405 prefixEnd_5458405 := by exact prefixLift 5458405
  have htrace : WordTrace (prefixWord ++ tailWord_5458405) baseStart_5458405 baseEnd_5458405 := by
    simpa [prefixWord, tailWord_5458405, baseEnd_5458405] using wordTrace_append hprefix tailTrace_5458405
  have hstable : (prefixWord ++ tailWord_5458405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458405).length < 2 ^ (prefixWord ++ tailWord_5458405).sum := by decide
  have hdescent : baseEnd_5458405 < baseStart_5458405 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458438 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 1, 6]
def baseStart_5458438 : Nat := 118140960795 + 5458438 * 2 ^ 59
def prefixEnd_5458438 : Nat := 4983230072969 + 3 ^ 40 * 5458438 * 2
def baseEnd_5458438 : Nat := 934267438922140023307369

theorem tailTrace_5458438 : CollatzResearch.WordTrace tailWord_5458438 prefixEnd_5458438 934267438922140023307369 := by
  unfold tailWord_5458438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6221424668719338369910249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132723726266012551891418645 6221424668719338369910249)
  ·
    refine ⟨4666068501539503777432687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6221424668719338369910249 4666068501539503777432687)
    ·
      refine ⟨6999102752309255666149031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4666068501539503777432687 6999102752309255666149031)
      ·
        refine ⟨10498654128463883499223547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6999102752309255666149031 10498654128463883499223547)
        ·
          refine ⟨15747981192695825248835321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10498654128463883499223547 15747981192695825248835321)
          ·
            refine ⟨11810985894521868936626491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15747981192695825248835321 11810985894521868936626491)
            ·
              refine ⟨17716478841782803404939737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11810985894521868936626491 17716478841782803404939737)
              ·
                refine ⟨13287359131337102553704803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17716478841782803404939737 13287359131337102553704803)
                ·
                  refine ⟨19931038697005653830557205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13287359131337102553704803 19931038697005653830557205)
                  ·
                    refine ⟨934267438922140023307369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19931038697005653830557205 934267438922140023307369)
                    ·
                      rfl

theorem cell23_5458438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_5458438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458438 prefixEnd_5458438 := by exact prefixLift 5458438
  have htrace : WordTrace (prefixWord ++ tailWord_5458438) baseStart_5458438 baseEnd_5458438 := by
    simpa [prefixWord, tailWord_5458438, baseEnd_5458438] using wordTrace_append hprefix tailTrace_5458438
  have hstable : (prefixWord ++ tailWord_5458438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458438).length < 2 ^ (prefixWord ++ tailWord_5458438).sum := by decide
  have hdescent : baseEnd_5458438 < baseStart_5458438 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458444 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 1, 3, 3]
def baseStart_5458444 : Nat := 118140960795 + 5458444 * 2 ^ 59
def prefixEnd_5458444 : Nat := 4983230072969 + 3 ^ 40 * 5458444 * 2
def baseEnd_5458444 : Nat := 2802805397650347046447079

theorem tailTrace_5458444 : CollatzResearch.WordTrace tailWord_5458444 prefixEnd_5458444 2802805397650347046447079 := by
  unfold tailWord_5458444
  simp only [CollatzResearch.WordTrace]
  refine ⟨99542904118498545430923193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132723872157998060574564257 99542904118498545430923193)
  ·
    refine ⟨74657178088873909073192395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99542904118498545430923193 74657178088873909073192395)
    ·
      refine ⟨111985767133310863609788593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74657178088873909073192395 111985767133310863609788593)
      ·
        refine ⟨83989325349983147707341445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111985767133310863609788593 83989325349983147707341445)
        ·
          refine ⟨15747998503121840195126521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83989325349983147707341445 15747998503121840195126521)
          ·
            refine ⟨11810998877341380146344891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15747998503121840195126521 11810998877341380146344891)
            ·
              refine ⟨17716498316012070219517337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11810998877341380146344891 17716498316012070219517337)
              ·
                refine ⟨13287373737009052664638003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17716498316012070219517337 13287373737009052664638003)
                ·
                  refine ⟨19931060605513578996957005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13287373737009052664638003 19931060605513578996957005)
                  ·
                    refine ⟨7474147727067592123858877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19931060605513578996957005 7474147727067592123858877)
                    ·
                      refine ⟨2802805397650347046447079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7474147727067592123858877 2802805397650347046447079)
                      ·
                        rfl

theorem cell23_5458444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 1, 3, 3].length) (baseStart_5458444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458444 prefixEnd_5458444 := by exact prefixLift 5458444
  have htrace : WordTrace (prefixWord ++ tailWord_5458444) baseStart_5458444 baseEnd_5458444 := by
    simpa [prefixWord, tailWord_5458444, baseEnd_5458444] using wordTrace_append hprefix tailTrace_5458444
  have hstable : (prefixWord ++ tailWord_5458444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458444).length < 2 ^ (prefixWord ++ tailWord_5458444).sum := by decide
  have hdescent : baseEnd_5458444 < baseStart_5458444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458445 : List Nat := [1, 7, 1, 1, 1, 2, 3, 1, 1, 1, 4]
def baseStart_5458445 : Nat := 118140960795 + 5458445 * 2 ^ 59
def prefixEnd_5458445 : Nat := 4983230072969 + 3 ^ 40 * 5458445 * 2
def baseEnd_5458445 : Nat := 2802805911131001542534575

theorem tailTrace_5458445 : CollatzResearch.WordTrace tailWord_5458445 prefixEnd_5458445 2802805911131001542534575 := by
  unfold tailWord_5458445
  simp only [CollatzResearch.WordTrace]
  refine ⟨199085844709993468032632789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132723896473328978688421859 199085844709993468032632789)
  ·
    refine ⟨4666074485390471907014831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 199085844709993468032632789 4666074485390471907014831)
    ·
      refine ⟨6999111728085707860522247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4666074485390471907014831 6999111728085707860522247)
      ·
        refine ⟨10498667592128561790783371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6999111728085707860522247 10498667592128561790783371)
        ·
          refine ⟨15748001388192842686175057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10498667592128561790783371 15748001388192842686175057)
          ·
            refine ⟨11811001041144632014631293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15748001388192842686175057 11811001041144632014631293)
            ·
              refine ⟨4429125390429237005486735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11811001041144632014631293 4429125390429237005486735)
              ·
                refine ⟨6643688085643855508230103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4429125390429237005486735 6643688085643855508230103)
                ·
                  refine ⟨9965532128465783262345155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6643688085643855508230103 9965532128465783262345155)
                  ·
                    refine ⟨14948298192698674893517733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9965532128465783262345155 14948298192698674893517733)
                    ·
                      refine ⟨2802805911131001542534575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14948298192698674893517733 2802805911131001542534575)
                      ·
                        rfl

theorem cell23_5458445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_5458445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458445 prefixEnd_5458445 := by exact prefixLift 5458445
  have htrace : WordTrace (prefixWord ++ tailWord_5458445) baseStart_5458445 baseEnd_5458445 := by
    simpa [prefixWord, tailWord_5458445, baseEnd_5458445] using wordTrace_append hprefix tailTrace_5458445
  have hstable : (prefixWord ++ tailWord_5458445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458445).length < 2 ^ (prefixWord ++ tailWord_5458445).sum := by decide
  have hdescent : baseEnd_5458445 < baseStart_5458445 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458461 : List Nat := [1, 4, 2, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_5458461 : Nat := 118140960795 + 5458461 * 2 ^ 59
def prefixEnd_5458461 : Nat := 4983230072969 + 3 ^ 40 * 5458461 * 2
def baseEnd_5458461 : Nat := 2802814126821473479934501

theorem tailTrace_5458461 : CollatzResearch.WordTrace tailWord_5458461 prefixEnd_5458461 2802814126821473479934501 := by
  unfold tailWord_5458461
  simp only [CollatzResearch.WordTrace]
  refine ⟨199086428277935502765215237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132724285518623668510143491 199086428277935502765215237)
  ·
    refine ⟨37328705302112906768477857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199086428277935502765215237 37328705302112906768477857)
    ·
      refine ⟨27996528976584680076358393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37328705302112906768477857 27996528976584680076358393)
      ·
        refine ⟨20997396732438510057268795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27996528976584680076358393 20997396732438510057268795)
        ·
          refine ⟨31496095098657765085903193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20997396732438510057268795 31496095098657765085903193)
          ·
            refine ⟨23622071323993323814427395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31496095098657765085903193 23622071323993323814427395)
            ·
              refine ⟨35433106985989985721641093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23622071323993323814427395 35433106985989985721641093)
              ·
                refine ⟨6643707559873122322807705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35433106985989985721641093 6643707559873122322807705)
                ·
                  refine ⟨4982780669904841742105779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6643707559873122322807705 4982780669904841742105779)
                  ·
                    refine ⟨7474171004857262613158669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4982780669904841742105779 7474171004857262613158669)
                    ·
                      refine ⟨2802814126821473479934501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7474171004857262613158669 2802814126821473479934501)
                      ·
                        rfl

theorem cell23_5458461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_5458461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458461 prefixEnd_5458461 := by exact prefixLift 5458461
  have htrace : WordTrace (prefixWord ++ tailWord_5458461) baseStart_5458461 baseEnd_5458461 := by
    simpa [prefixWord, tailWord_5458461, baseEnd_5458461] using wordTrace_append hprefix tailTrace_5458461
  have hstable : (prefixWord ++ tailWord_5458461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458461).length < 2 ^ (prefixWord ++ tailWord_5458461).sum := by decide
  have hdescent : baseEnd_5458461 < baseStart_5458461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458467 : List Nat := [1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 4]
def baseStart_5458467 : Nat := 118140960795 + 5458467 * 2 ^ 59
def prefixEnd_5458467 : Nat := 4983230072969 + 3 ^ 40 * 5458467 * 2
def baseEnd_5458467 : Nat := 2802817207705400456459473

theorem tailTrace_5458467 : CollatzResearch.WordTrace tailWord_5458467 prefixEnd_5458467 2802817207705400456459473 := by
  unfold tailWord_5458467
  simp only [CollatzResearch.WordTrace]
  refine ⟨199086647115913765789933655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132724431410609177193289103 199086647115913765789933655)
  ·
    refine ⟨298629970673870648684900483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199086647115913765789933655 298629970673870648684900483)
    ·
      refine ⟨447944956010805973027350725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298629970673870648684900483 447944956010805973027350725)
      ·
        refine ⟨83989679252026119942628261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 447944956010805973027350725 83989679252026119942628261)
        ·
          refine ⟨15748064859754897489242799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83989679252026119942628261 15748064859754897489242799)
          ·
            refine ⟨23622097289632346233864199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15748064859754897489242799 23622097289632346233864199)
            ·
              refine ⟨35433145934448519350796299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23622097289632346233864199 35433145934448519350796299)
              ·
                refine ⟨53149718901672779026194449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35433145934448519350796299 53149718901672779026194449)
                ·
                  refine ⟨39862289176254584269645837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53149718901672779026194449 39862289176254584269645837)
                  ·
                    refine ⟨14948358441095469101117189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39862289176254584269645837 14948358441095469101117189)
                    ·
                      refine ⟨2802817207705400456459473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14948358441095469101117189 2802817207705400456459473)
                      ·
                        rfl

theorem cell23_5458467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_5458467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458467 prefixEnd_5458467 := by exact prefixLift 5458467
  have htrace : WordTrace (prefixWord ++ tailWord_5458467) baseStart_5458467 baseEnd_5458467 := by
    simpa [prefixWord, tailWord_5458467, baseEnd_5458467] using wordTrace_append hprefix tailTrace_5458467
  have hstable : (prefixWord ++ tailWord_5458467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458467).length < 2 ^ (prefixWord ++ tailWord_5458467).sum := by decide
  have hdescent : baseEnd_5458467 < baseStart_5458467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458487 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 3]
def baseStart_5458487 : Nat := 118140960795 + 5458487 * 2 ^ 59
def prefixEnd_5458487 : Nat := 4983230072969 + 3 ^ 40 * 5458487 * 2
def baseEnd_5458487 : Nat := 2802827477318490378209381

theorem tailTrace_5458487 : CollatzResearch.WordTrace tailWord_5458487 prefixEnd_5458487 2802827477318490378209381 := by
  unfold tailWord_5458487
  simp only [CollatzResearch.WordTrace]
  refine ⟨199087376575841309205661715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132724917717227539470441143 199087376575841309205661715)
  ·
    refine ⟨298631064863761963808492573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199087376575841309205661715 298631064863761963808492573)
    ·
      refine ⟨111986649323910736428184715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298631064863761963808492573 111986649323910736428184715)
      ·
        refine ⟨167979973985866104642277073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111986649323910736428184715 167979973985866104642277073)
        ·
          refine ⟨125984980489399578481707805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167979973985866104642277073 125984980489399578481707805)
          ·
            refine ⟨47244367683524841930640427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125984980489399578481707805 47244367683524841930640427)
            ·
              refine ⟨70866551525287262895960641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47244367683524841930640427 70866551525287262895960641)
              ·
                refine ⟨53149913643965447171970481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70866551525287262895960641 53149913643965447171970481)
                ·
                  refine ⟨39862435232974085378977861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53149913643965447171970481 39862435232974085378977861)
                  ·
                    refine ⟨7474206606182641008558349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39862435232974085378977861 7474206606182641008558349)
                    ·
                      refine ⟨2802827477318490378209381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7474206606182641008558349 2802827477318490378209381)
                      ·
                        rfl

theorem cell23_5458487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_5458487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458487 prefixEnd_5458487 := by exact prefixLift 5458487
  have htrace : WordTrace (prefixWord ++ tailWord_5458487) baseStart_5458487 baseEnd_5458487 := by
    simpa [prefixWord, tailWord_5458487, baseEnd_5458487] using wordTrace_append hprefix tailTrace_5458487
  have hstable : (prefixWord ++ tailWord_5458487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458487).length < 2 ^ (prefixWord ++ tailWord_5458487).sum := by decide
  have hdescent : baseEnd_5458487 < baseStart_5458487 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458611 : List Nat := [1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 3]
def baseStart_5458611 : Nat := 118140960795 + 5458611 * 2 ^ 59
def prefixEnd_5458611 : Nat := 4983230072969 + 3 ^ 40 * 5458611 * 2
def baseEnd_5458611 : Nat := 2802891148919647893058811

theorem tailTrace_5458611 : CollatzResearch.WordTrace tailWord_5458611 prefixEnd_5458611 2802891148919647893058811 := by
  unfold tailWord_5458611
  simp only [CollatzResearch.WordTrace]
  refine ⟨199091899227392078383175687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132727932818261385588783791 199091899227392078383175687)
  ·
    refine ⟨298637848841088117574763531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199091899227392078383175687 298637848841088117574763531)
    ·
      refine ⟨447956773261632176362145297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298637848841088117574763531 447956773261632176362145297)
      ·
        refine ⟨335967579946224132271608973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447956773261632176362145297 335967579946224132271608973)
        ·
          refine ⟨125987842479834049601853365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 335967579946224132271608973 125987842479834049601853365)
          ·
            refine ⟨11811360232484442150173753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125987842479834049601853365 11811360232484442150173753)
            ·
              refine ⟨8858520174363331612630315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11811360232484442150173753 8858520174363331612630315)
              ·
                refine ⟨13287780261544997418945473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8858520174363331612630315 13287780261544997418945473)
                ·
                  refine ⟨9965835196158748064209105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13287780261544997418945473 9965835196158748064209105)
                  ·
                    refine ⟨7474376397119061048156829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9965835196158748064209105 7474376397119061048156829)
                    ·
                      refine ⟨2802891148919647893058811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7474376397119061048156829 2802891148919647893058811)
                      ·
                        rfl

theorem cell23_5458611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 3].length) (baseStart_5458611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458611 prefixEnd_5458611 := by exact prefixLift 5458611
  have htrace : WordTrace (prefixWord ++ tailWord_5458611) baseStart_5458611 baseEnd_5458611 := by
    simpa [prefixWord, tailWord_5458611, baseEnd_5458611] using wordTrace_append hprefix tailTrace_5458611
  have hstable : (prefixWord ++ tailWord_5458611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458611).length < 2 ^ (prefixWord ++ tailWord_5458611).sum := by decide
  have hdescent : baseEnd_5458611 < baseStart_5458611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458617 : List Nat := [1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 8]
def baseStart_5458617 : Nat := 118140960795 + 5458617 * 2 ^ 59
def prefixEnd_5458617 : Nat := 4983230072969 + 3 ^ 40 * 5458617 * 2
def baseEnd_5458617 : Nat := 2802894229803574869583783

theorem tailTrace_5458617 : CollatzResearch.WordTrace tailWord_5458617 prefixEnd_5458617 2802894229803574869583783 := by
  unfold tailWord_5458617
  simp only [CollatzResearch.WordTrace]
  refine ⟨199092118065370341407894105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132728078710246894271929403 199092118065370341407894105)
  ·
    refine ⟨149319088549027756055920579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199092118065370341407894105 149319088549027756055920579)
    ·
      refine ⟨223978632823541634083880869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149319088549027756055920579 223978632823541634083880869)
      ·
        refine ⟨41995993654414056390727663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 223978632823541634083880869 41995993654414056390727663)
        ·
          refine ⟨62993990481621084586091495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41995993654414056390727663 62993990481621084586091495)
          ·
            refine ⟨94490985722431626879137243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62993990481621084586091495 94490985722431626879137243)
            ·
              refine ⟨141736478583647440318705865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94490985722431626879137243 141736478583647440318705865)
              ·
                refine ⟨106302358937735580239029399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141736478583647440318705865 106302358937735580239029399)
                ·
                  refine ⟨159453538406603370358544099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106302358937735580239029399 159453538406603370358544099)
                  ·
                    refine ⟨239180307609905055537816149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159453538406603370358544099 239180307609905055537816149)
                    ·
                      refine ⟨2802894229803574869583783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 239180307609905055537816149 2802894229803574869583783)
                      ·
                        rfl

theorem cell23_5458617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_5458617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458617 prefixEnd_5458617 := by exact prefixLift 5458617
  have htrace : WordTrace (prefixWord ++ tailWord_5458617) baseStart_5458617 baseEnd_5458617 := by
    simpa [prefixWord, tailWord_5458617, baseEnd_5458617] using wordTrace_append hprefix tailTrace_5458617
  have hstable : (prefixWord ++ tailWord_5458617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458617).length < 2 ^ (prefixWord ++ tailWord_5458617).sum := by decide
  have hdescent : baseEnd_5458617 < baseStart_5458617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458641 : List Nat := [1, 2, 2, 1, 2, 3, 2, 3, 3, 1, 3]
def baseStart_5458641 : Nat := 118140960795 + 5458641 * 2 ^ 59
def prefixEnd_5458641 : Nat := 4983230072969 + 3 ^ 40 * 5458641 * 2
def baseEnd_5458641 : Nat := 2802906553339282775683673

theorem tailTrace_5458641 : CollatzResearch.WordTrace tailWord_5458641 prefixEnd_5458641 2802906553339282775683673 := by
  unfold tailWord_5458641
  simp only [CollatzResearch.WordTrace]
  refine ⟨199092993417283393506767777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132728662278188929004511851 199092993417283393506767777)
  ·
    refine ⟨149319745062962545130075833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199092993417283393506767777 149319745062962545130075833)
    ·
      refine ⟨111989808797221908847556875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149319745062962545130075833 111989808797221908847556875)
      ·
        refine ⟨167984713195832863271335313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111989808797221908847556875 167984713195832863271335313)
        ·
          refine ⟨125988534896874647453501485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167984713195832863271335313 125988534896874647453501485)
          ·
            refine ⟨47245700586327992795063057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125988534896874647453501485 47245700586327992795063057)
            ·
              refine ⟨35434275439745994596297293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47245700586327992795063057 35434275439745994596297293)
              ·
                refine ⟨13287853289904747973611485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35434275439745994596297293 13287853289904747973611485)
                ·
                  refine ⟨4982944983714280490104307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13287853289904747973611485 4982944983714280490104307)
                  ·
                    refine ⟨7474417475571420735156461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4982944983714280490104307 7474417475571420735156461)
                    ·
                      refine ⟨2802906553339282775683673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7474417475571420735156461 2802906553339282775683673)
                      ·
                        rfl

theorem cell23_5458641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_5458641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458641 prefixEnd_5458641 := by exact prefixLift 5458641
  have htrace : WordTrace (prefixWord ++ tailWord_5458641) baseStart_5458641 baseEnd_5458641 := by
    simpa [prefixWord, tailWord_5458641, baseEnd_5458641] using wordTrace_append hprefix tailTrace_5458641
  have hstable : (prefixWord ++ tailWord_5458641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458641).length < 2 ^ (prefixWord ++ tailWord_5458641).sum := by decide
  have hdescent : baseEnd_5458641 < baseStart_5458641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458711 : List Nat := [1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 6]
def baseStart_5458711 : Nat := 118140960795 + 5458711 * 2 ^ 59
def prefixEnd_5458711 : Nat := 4983230072969 + 3 ^ 40 * 5458711 * 2
def baseEnd_5458711 : Nat := 2802942496985097501808351

theorem tailTrace_5458711 : CollatzResearch.WordTrace tailWord_5458711 prefixEnd_5458711 2802942496985097501808351 := by
  unfold tailWord_5458711
  simp only [CollatzResearch.WordTrace]
  refine ⟨199095546527029795461815987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132730364351353196974543991 199095546527029795461815987)
  ·
    refine ⟨298643319790544693192723981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199095546527029795461815987 298643319790544693192723981)
    ·
      refine ⟨111991244921454259947271493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298643319790544693192723981 111991244921454259947271493)
      ·
        refine ⟨20998358422772673740113405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111991244921454259947271493 20998358422772673740113405)
        ·
          refine ⟨7874384408539752652542527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20998358422772673740113405 7874384408539752652542527)
          ·
            refine ⟨11811576612809628978813791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7874384408539752652542527 11811576612809628978813791)
            ·
              refine ⟨17717364919214443468220687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11811576612809628978813791 17717364919214443468220687)
              ·
                refine ⟨26576047378821665202331031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17717364919214443468220687 26576047378821665202331031)
                ·
                  refine ⟨39864071068232497803496547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26576047378821665202331031 39864071068232497803496547)
                  ·
                    refine ⟨59796106602348746705244821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39864071068232497803496547 59796106602348746705244821)
                    ·
                      refine ⟨2802942496985097501808351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59796106602348746705244821 2802942496985097501808351)
                      ·
                        rfl

theorem cell23_5458711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_5458711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458711 prefixEnd_5458711 := by exact prefixLift 5458711
  have htrace : WordTrace (prefixWord ++ tailWord_5458711) baseStart_5458711 baseEnd_5458711 := by
    simpa [prefixWord, tailWord_5458711, baseEnd_5458711] using wordTrace_append hprefix tailTrace_5458711
  have hstable : (prefixWord ++ tailWord_5458711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458711).length < 2 ^ (prefixWord ++ tailWord_5458711).sum := by decide
  have hdescent : baseEnd_5458711 < baseStart_5458711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458731 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 4, 1, 3]
def baseStart_5458731 : Nat := 118140960795 + 5458731 * 2 ^ 59
def prefixEnd_5458731 : Nat := 4983230072969 + 3 ^ 40 * 5458731 * 2
def baseEnd_5458731 : Nat := 2802952766598187423558259

theorem tailTrace_5458731 : CollatzResearch.WordTrace tailWord_5458731 prefixEnd_5458731 2802952766598187423558259 := by
  unfold tailWord_5458731
  simp only [CollatzResearch.WordTrace]
  refine ⟨199096275986957338877544047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132730850657971559251696031 199096275986957338877544047)
  ·
    refine ⟨298644413980436008316316071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199096275986957338877544047 298644413980436008316316071)
    ·
      refine ⟨447966620970654012474474107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298644413980436008316316071 447966620970654012474474107)
      ·
        refine ⟨671949931455981018711711161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447966620970654012474474107 671949931455981018711711161)
        ·
          refine ⟨503962448591985764033783371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 671949931455981018711711161 503962448591985764033783371)
          ·
            refine ⟨755943672887978646050675057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503962448591985764033783371 755943672887978646050675057)
            ·
              refine ⟨566957754665983984538006293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755943672887978646050675057 566957754665983984538006293)
              ·
                refine ⟨26576144749967999275219045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 566957754665983984538006293 26576144749967999275219045)
                ·
                  refine ⟨4983027140618999864103571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26576144749967999275219045 4983027140618999864103571)
                  ·
                    refine ⟨7474540710928499796155357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4983027140618999864103571 7474540710928499796155357)
                    ·
                      refine ⟨2802952766598187423558259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7474540710928499796155357 2802952766598187423558259)
                      ·
                        rfl

theorem cell23_5458731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 1, 3].length) (baseStart_5458731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458731 prefixEnd_5458731 := by exact prefixLift 5458731
  have htrace : WordTrace (prefixWord ++ tailWord_5458731) baseStart_5458731 baseEnd_5458731 := by
    simpa [prefixWord, tailWord_5458731, baseEnd_5458731] using wordTrace_append hprefix tailTrace_5458731
  have hstable : (prefixWord ++ tailWord_5458731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458731).length < 2 ^ (prefixWord ++ tailWord_5458731).sum := by decide
  have hdescent : baseEnd_5458731 < baseStart_5458731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458744 : List Nat := [2, 1, 2, 1, 3, 2, 1, 2, 2, 2, 5]
def baseStart_5458744 : Nat := 118140960795 + 5458744 * 2 ^ 59
def prefixEnd_5458744 : Nat := 4983230072969 + 3 ^ 40 * 5458744 * 2
def baseEnd_5458744 : Nat := 2802959441846695872695699

theorem tailTrace_5458744 : CollatzResearch.WordTrace tailWord_5458744 prefixEnd_5458744 2802959441846695872695699 := by
  unfold tailWord_5458744
  simp only [CollatzResearch.WordTrace]
  refine ⟨99548375067955121048883643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132731166757273494731844857 99548375067955121048883643)
  ·
    refine ⟨149322562601932681573325465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99548375067955121048883643 149322562601932681573325465)
    ·
      refine ⟨111991921951449511179994099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149322562601932681573325465 111991921951449511179994099)
      ·
        refine ⟨167987882927174266769991149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111991921951449511179994099 167987882927174266769991149)
        ·
          refine ⟨62995456097690350038746681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167987882927174266769991149 62995456097690350038746681)
          ·
            refine ⟨47246592073267762529060011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62995456097690350038746681 47246592073267762529060011)
            ·
              refine ⟨70869888109901643793590017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47246592073267762529060011 70869888109901643793590017)
              ·
                refine ⟨53152416082426232845192513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70869888109901643793590017 53152416082426232845192513)
                ·
                  refine ⟨39864312061819674633894385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53152416082426232845192513 39864312061819674633894385)
                  ·
                    refine ⟨29898234046364755975420789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39864312061819674633894385 29898234046364755975420789)
                    ·
                      refine ⟨2802959441846695872695699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29898234046364755975420789 2802959441846695872695699)
                      ·
                        rfl

theorem cell23_5458744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 2, 2, 2, 5].length) (baseStart_5458744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458744 prefixEnd_5458744 := by exact prefixLift 5458744
  have htrace : WordTrace (prefixWord ++ tailWord_5458744) baseStart_5458744 baseEnd_5458744 := by
    simpa [prefixWord, tailWord_5458744, baseEnd_5458744] using wordTrace_append hprefix tailTrace_5458744
  have hstable : (prefixWord ++ tailWord_5458744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458744).length < 2 ^ (prefixWord ++ tailWord_5458744).sum := by decide
  have hdescent : baseEnd_5458744 < baseStart_5458744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458748 : List Nat := [2, 2, 2, 2, 1, 1, 1, 6, 2, 1, 3]
def baseStart_5458748 : Nat := 118140960795 + 5458748 * 2 ^ 59
def prefixEnd_5458748 : Nat := 4983230072969 + 3 ^ 40 * 5458748 * 2
def baseEnd_5458748 : Nat := 2802961495769313857045681

theorem tailTrace_5458748 : CollatzResearch.WordTrace tailWord_5458748 prefixEnd_5458748 2802961495769313857045681 := by
  unfold tailWord_5458748
  simp only [CollatzResearch.WordTrace]
  refine ⟨99548448013947875390456449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132731264018597167187275265 99548448013947875390456449)
  ·
    refine ⟨74661336010460906542842337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99548448013947875390456449 74661336010460906542842337)
    ·
      refine ⟨55996002007845679907131753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74661336010460906542842337 55996002007845679907131753)
      ·
        refine ⟨41997001505884259930348815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55996002007845679907131753 41997001505884259930348815)
        ·
          refine ⟨62995502258826389895523223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41997001505884259930348815 62995502258826389895523223)
          ·
            refine ⟨94493253388239584843284835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62995502258826389895523223 94493253388239584843284835)
            ·
              refine ⟨141739880082359377264927253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94493253388239584843284835 141739880082359377264927253)
              ·
                refine ⟨6644056878860595809293465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141739880082359377264927253 6644056878860595809293465)
                ·
                  refine ⟨4983042659145446856970099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6644056878860595809293465 4983042659145446856970099)
                  ·
                    refine ⟨7474563988718170285455149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4983042659145446856970099 7474563988718170285455149)
                    ·
                      refine ⟨2802961495769313857045681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7474563988718170285455149 2802961495769313857045681)
                      ·
                        rfl

theorem cell23_5458748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_5458748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458748 prefixEnd_5458748 := by exact prefixLift 5458748
  have htrace : WordTrace (prefixWord ++ tailWord_5458748) baseStart_5458748 baseEnd_5458748 := by
    simpa [prefixWord, tailWord_5458748, baseEnd_5458748] using wordTrace_append hprefix tailTrace_5458748
  have hstable : (prefixWord ++ tailWord_5458748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458748).length < 2 ^ (prefixWord ++ tailWord_5458748).sum := by decide
  have hdescent : baseEnd_5458748 < baseStart_5458748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458749 : List Nat := [1, 4, 1, 4, 3, 1, 1, 1, 3, 2, 2]
def baseStart_5458749 : Nat := 118140960795 + 5458749 * 2 ^ 59
def prefixEnd_5458749 : Nat := 4983230072969 + 3 ^ 40 * 5458749 * 2
def baseEnd_5458749 : Nat := 2802962009249968353133177

theorem tailTrace_5458749 : CollatzResearch.WordTrace tailWord_5458749 prefixEnd_5458749 2802962009249968353133177 := by
  unfold tailWord_5458749
  simp only [CollatzResearch.WordTrace]
  refine ⟨199096932500892127951699301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132731288333928085301132867 199096932500892127951699301)
  ·
    refine ⟨37330674843917273990943619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199096932500892127951699301 37330674843917273990943619)
    ·
      refine ⟨55996012265875910986415429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37330674843917273990943619 55996012265875910986415429)
      ·
        refine ⟨10499252299851733309952893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55996012265875910986415429 10499252299851733309952893)
        ·
          refine ⟨3937219612444399991232335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10499252299851733309952893 3937219612444399991232335)
          ·
            refine ⟨5905829418666599986848503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3937219612444399991232335 5905829418666599986848503)
            ·
              refine ⟨8858744127999899980272755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5905829418666599986848503 8858744127999899980272755)
              ·
                refine ⟨13288116191999849970409133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8858744127999899980272755 13288116191999849970409133)
                ·
                  refine ⟨4983043571999943738903425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13288116191999849970409133 4983043571999943738903425)
                  ·
                    refine ⟨3737282678999957804177569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4983043571999943738903425 3737282678999957804177569)
                    ·
                      refine ⟨2802962009249968353133177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3737282678999957804177569 2802962009249968353133177)
                      ·
                        rfl

theorem cell23_5458749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_5458749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458749 prefixEnd_5458749 := by exact prefixLift 5458749
  have htrace : WordTrace (prefixWord ++ tailWord_5458749) baseStart_5458749 baseEnd_5458749 := by
    simpa [prefixWord, tailWord_5458749, baseEnd_5458749] using wordTrace_append hprefix tailTrace_5458749
  have hstable : (prefixWord ++ tailWord_5458749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458749).length < 2 ^ (prefixWord ++ tailWord_5458749).sum := by decide
  have hdescent : baseEnd_5458749 < baseStart_5458749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458771 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 5, 4, 2]
def baseStart_5458771 : Nat := 118140960795 + 5458771 * 2 ^ 59
def prefixEnd_5458771 : Nat := 4983230072969 + 3 ^ 40 * 5458771 * 2
def baseEnd_5458771 : Nat := 2802973305824367267058075

theorem tailTrace_5458771 : CollatzResearch.WordTrace tailWord_5458771 prefixEnd_5458771 2802973305824367267058075 := by
  unfold tailWord_5458771
  simp only [CollatzResearch.WordTrace]
  refine ⟨199097734906812425709000167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132731823271208283806000111 199097734906812425709000167)
  ·
    refine ⟨298646602360218638563500251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199097734906812425709000167 298646602360218638563500251)
    ·
      refine ⟨447969903540327957845250377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298646602360218638563500251 447969903540327957845250377)
      ·
        refine ⟨335977427655245968383937783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 447969903540327957845250377 335977427655245968383937783)
        ·
          refine ⟨503966141482868952575906675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335977427655245968383937783 503966141482868952575906675)
          ·
            refine ⟨755949212224303428863860013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503966141482868952575906675 755949212224303428863860013)
            ·
              refine ⟨283480954584113785823947505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 755949212224303428863860013 283480954584113785823947505)
              ·
                refine ⟨212610715938085339367960629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283480954584113785823947505 212610715938085339367960629)
                ·
                  refine ⟨19932254619195500565746309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 212610715938085339367960629 19932254619195500565746309)
                  ·
                    refine ⟨3737297741099156356077433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19932254619195500565746309 3737297741099156356077433)
                    ·
                      refine ⟨2802973305824367267058075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3737297741099156356077433 2802973305824367267058075)
                      ·
                        rfl

theorem cell23_5458771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 5, 4, 2].length) (baseStart_5458771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458771 prefixEnd_5458771 := by exact prefixLift 5458771
  have htrace : WordTrace (prefixWord ++ tailWord_5458771) baseStart_5458771 baseEnd_5458771 := by
    simpa [prefixWord, tailWord_5458771, baseEnd_5458771] using wordTrace_append hprefix tailTrace_5458771
  have hstable : (prefixWord ++ tailWord_5458771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458771).length < 2 ^ (prefixWord ++ tailWord_5458771).sum := by decide
  have hdescent : baseEnd_5458771 < baseStart_5458771 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458775 : List Nat := [1, 1, 3, 2, 4, 1, 3, 2, 1, 3, 2]
def baseStart_5458775 : Nat := 118140960795 + 5458775 * 2 ^ 59
def prefixEnd_5458775 : Nat := 4983230072969 + 3 ^ 40 * 5458775 * 2
def baseEnd_5458775 : Nat := 2802975359746985251408057

theorem tailTrace_5458775 : CollatzResearch.WordTrace tailWord_5458775 prefixEnd_5458775 2802975359746985251408057 := by
  unfold tailWord_5458775
  simp only [CollatzResearch.WordTrace]
  refine ⟨199097880798797934392145779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132731920532531956261430519 199097880798797934392145779)
  ·
    refine ⟨298646821198196901588218669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199097880798797934392145779 298646821198196901588218669)
    ·
      refine ⟨111992557949323838095582001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298646821198196901588218669 111992557949323838095582001)
      ·
        refine ⟨83994418461992878571686501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111992557949323838095582001 83994418461992878571686501)
        ·
          refine ⟨15748953461623664732191219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83994418461992878571686501 15748953461623664732191219)
          ·
            refine ⟨23623430192435497098286829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15748953461623664732191219 23623430192435497098286829)
            ·
              refine ⟨8858786322163311411857561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23623430192435497098286829 8858786322163311411857561)
              ·
                refine ⟨6644089741622483558893171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8858786322163311411857561 6644089741622483558893171)
                ·
                  refine ⟨9966134612433725338339757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6644089741622483558893171 9966134612433725338339757)
                  ·
                    refine ⟨3737300479662647001877409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9966134612433725338339757 3737300479662647001877409)
                    ·
                      refine ⟨2802975359746985251408057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3737300479662647001877409 2802975359746985251408057)
                      ·
                        rfl

theorem cell23_5458775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 1, 3, 2].length) (baseStart_5458775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458775 prefixEnd_5458775 := by exact prefixLift 5458775
  have htrace : WordTrace (prefixWord ++ tailWord_5458775) baseStart_5458775 baseEnd_5458775 := by
    simpa [prefixWord, tailWord_5458775, baseEnd_5458775] using wordTrace_append hprefix tailTrace_5458775
  have hstable : (prefixWord ++ tailWord_5458775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458775).length < 2 ^ (prefixWord ++ tailWord_5458775).sum := by decide
  have hdescent : baseEnd_5458775 < baseStart_5458775 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458788 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 3, 4, 2]
def baseStart_5458788 : Nat := 118140960795 + 5458788 * 2 ^ 59
def prefixEnd_5458788 : Nat := 4983230072969 + 3 ^ 40 * 5458788 * 2
def baseEnd_5458788 : Nat := 2802982034995493700545497

theorem tailTrace_5458788 : CollatzResearch.WordTrace tailWord_5458788 prefixEnd_5458788 2802982034995493700545497 := by
  unfold tailWord_5458788
  simp only [CollatzResearch.WordTrace]
  refine ⟨99549177473875418806184509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132732236631833891741579345 99549177473875418806184509)
  ·
    refine ⟨37330941552703282052319191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99549177473875418806184509 37330941552703282052319191)
    ·
      refine ⟨55996412329054923078478787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37330941552703282052319191 55996412329054923078478787)
      ·
        refine ⟨83994618493582384617718181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55996412329054923078478787 83994618493582384617718181)
        ·
          refine ⟨15748990967546697115822159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83994618493582384617718181 15748990967546697115822159)
          ·
            refine ⟨23623486451320045673733239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15748990967546697115822159 23623486451320045673733239)
            ·
              refine ⟨35435229676980068510599859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23623486451320045673733239 35435229676980068510599859)
              ·
                refine ⟨53152844515470102765899789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35435229676980068510599859 53152844515470102765899789)
                ·
                  refine ⟨19932316693301288537212421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53152844515470102765899789 19932316693301288537212421)
                  ·
                    refine ⟨3737309379993991600727329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19932316693301288537212421 3737309379993991600727329)
                    ·
                      refine ⟨2802982034995493700545497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3737309379993991600727329 2802982034995493700545497)
                      ·
                        rfl

theorem cell23_5458788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_5458788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458788 prefixEnd_5458788 := by exact prefixLift 5458788
  have htrace : WordTrace (prefixWord ++ tailWord_5458788) baseStart_5458788 baseEnd_5458788 := by
    simpa [prefixWord, tailWord_5458788, baseEnd_5458788] using wordTrace_append hprefix tailTrace_5458788
  have hstable : (prefixWord ++ tailWord_5458788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458788).length < 2 ^ (prefixWord ++ tailWord_5458788).sum := by decide
  have hdescent : baseEnd_5458788 < baseStart_5458788 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458791 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_5458791 : Nat := 118140960795 + 5458791 * 2 ^ 59
def prefixEnd_5458791 : Nat := 4983230072969 + 3 ^ 40 * 5458791 * 2
def baseEnd_5458791 : Nat := 2802983575437457188807983

theorem tailTrace_5458791 : CollatzResearch.WordTrace tailWord_5458791 prefixEnd_5458791 2802983575437457188807983 := by
  unfold tailWord_5458791
  simp only [CollatzResearch.WordTrace]
  refine ⟨199098464366739969124728227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132732309577826646083152151 199098464366739969124728227)
  ·
    refine ⟨298647696550109953687092341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199098464366739969124728227 298647696550109953687092341)
    ·
      refine ⟨27998221551572808158164907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 298647696550109953687092341 27998221551572808158164907)
      ·
        refine ⟨41997332327359212237247361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27998221551572808158164907 41997332327359212237247361)
        ·
          refine ⟨31497999245519409177935521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41997332327359212237247361 31497999245519409177935521)
          ·
            refine ⟨23623499434139556883451641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31497999245519409177935521 23623499434139556883451641)
            ·
              refine ⟨17717624575604667662588731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23623499434139556883451641 17717624575604667662588731)
              ·
                refine ⟨26576436863407001493883097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17717624575604667662588731 26576436863407001493883097)
                ·
                  refine ⟨19932327647555251120412323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26576436863407001493883097 19932327647555251120412323)
                  ·
                    refine ⟨29898491471332876680618485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19932327647555251120412323 29898491471332876680618485)
                    ·
                      refine ⟨2802983575437457188807983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29898491471332876680618485 2802983575437457188807983)
                      ·
                        rfl

theorem cell23_5458791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_5458791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458791 prefixEnd_5458791 := by exact prefixLift 5458791
  have htrace : WordTrace (prefixWord ++ tailWord_5458791) baseStart_5458791 baseEnd_5458791 := by
    simpa [prefixWord, tailWord_5458791, baseEnd_5458791] using wordTrace_append hprefix tailTrace_5458791
  have hstable : (prefixWord ++ tailWord_5458791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458791).length < 2 ^ (prefixWord ++ tailWord_5458791).sum := by decide
  have hdescent : baseEnd_5458791 < baseStart_5458791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458792 : List Nat := [2, 1, 4, 2, 1, 3, 3, 1, 1, 3, 2]
def baseStart_5458792 : Nat := 118140960795 + 5458792 * 2 ^ 59
def prefixEnd_5458792 : Nat := 4983230072969 + 3 ^ 40 * 5458792 * 2
def baseEnd_5458792 : Nat := 2802984088918111684895479

theorem tailTrace_5458792 : CollatzResearch.WordTrace tailWord_5458792 prefixEnd_5458792 2802984088918111684895479 := by
  unfold tailWord_5458792
  simp only [CollatzResearch.WordTrace]
  refine ⟨99549250419868173147757315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132732333893157564197009753 99549250419868173147757315)
  ·
    refine ⟨149323875629802259721635973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99549250419868173147757315 149323875629802259721635973)
    ·
      refine ⟨27998226680587923697806745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149323875629802259721635973 27998226680587923697806745)
      ·
        refine ⟨20998670010440942773355059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27998226680587923697806745 20998670010440942773355059)
        ·
          refine ⟨31498005015661414160032589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20998670010440942773355059 31498005015661414160032589)
          ·
            refine ⟨11811751880873030310012221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31498005015661414160032589 11811751880873030310012221)
            ·
              refine ⟨4429406955327386366254583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11811751880873030310012221 4429406955327386366254583)
              ·
                refine ⟨6644110432991079549381875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4429406955327386366254583 6644110432991079549381875)
                ·
                  refine ⟨9966165649486619324072813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6644110432991079549381875 9966165649486619324072813)
                  ·
                    refine ⟨3737312118557482246527305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9966165649486619324072813 3737312118557482246527305)
                    ·
                      refine ⟨2802984088918111684895479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3737312118557482246527305 2802984088918111684895479)
                      ·
                        rfl

theorem cell23_5458792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_5458792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458792 prefixEnd_5458792 := by exact prefixLift 5458792
  have htrace : WordTrace (prefixWord ++ tailWord_5458792) baseStart_5458792 baseEnd_5458792 := by
    simpa [prefixWord, tailWord_5458792, baseEnd_5458792] using wordTrace_append hprefix tailTrace_5458792
  have hstable : (prefixWord ++ tailWord_5458792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458792).length < 2 ^ (prefixWord ++ tailWord_5458792).sum := by decide
  have hdescent : baseEnd_5458792 < baseStart_5458792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458821 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 1, 5, 3]
def baseStart_5458821 : Nat := 118140960795 + 5458821 * 2 ^ 59
def prefixEnd_5458821 : Nat := 4983230072969 + 3 ^ 40 * 5458821 * 2
def baseEnd_5458821 : Nat := 2802998979857092071432845

theorem tailTrace_5458821 : CollatzResearch.WordTrace tailWord_5458821 prefixEnd_5458821 2802998979857092071432845 := by
  unfold tailWord_5458821
  simp only [CollatzResearch.WordTrace]
  refine ⟨199099558556631284248320317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132733039037754189498880211 199099558556631284248320317)
  ·
    refine ⟨74662334458736731593120119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199099558556631284248320317 74662334458736731593120119)
    ·
      refine ⟨111993501688105097389680179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74662334458736731593120119 111993501688105097389680179)
      ·
        refine ⟨167990252532157646084520269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111993501688105097389680179 167990252532157646084520269)
        ·
          refine ⟨62996344699559117281695101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167990252532157646084520269 62996344699559117281695101)
          ·
            refine ⟨23623629262334668980635663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62996344699559117281695101 23623629262334668980635663)
            ·
              refine ⟨35435443893502003470953495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23623629262334668980635663 35435443893502003470953495)
              ·
                refine ⟨53153165840253005206430243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35435443893502003470953495 53153165840253005206430243)
                ·
                  refine ⟨79729748760379507809645365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53153165840253005206430243 79729748760379507809645365)
                  ·
                    refine ⟨7474663946285578857154253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79729748760379507809645365 7474663946285578857154253)
                    ·
                      refine ⟨2802998979857092071432845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7474663946285578857154253 2802998979857092071432845)
                      ·
                        rfl

theorem cell23_5458821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_5458821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458821 prefixEnd_5458821 := by exact prefixLift 5458821
  have htrace : WordTrace (prefixWord ++ tailWord_5458821) baseStart_5458821 baseEnd_5458821 := by
    simpa [prefixWord, tailWord_5458821, baseEnd_5458821] using wordTrace_append hprefix tailTrace_5458821
  have hstable : (prefixWord ++ tailWord_5458821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458821).length < 2 ^ (prefixWord ++ tailWord_5458821).sum := by decide
  have hdescent : baseEnd_5458821 < baseStart_5458821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458938 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2]
def baseStart_5458938 : Nat := 118140960795 + 5458938 * 2 ^ 59
def prefixEnd_5458938 : Nat := 4983230072969 + 3 ^ 40 * 5458938 * 2
def baseEnd_5458938 : Nat := 2803059057093668113669807

theorem tailTrace_5458938 : CollatzResearch.WordTrace tailWord_5458938 prefixEnd_5458938 2803059057093668113669807 := by
  unfold tailWord_5458938
  simp only [CollatzResearch.WordTrace]
  refine ⟨49775956474301853307582367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132735883931471608820219645 49775956474301853307582367)
  ·
    refine ⟨74663934711452779961373551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49775956474301853307582367 74663934711452779961373551)
    ·
      refine ⟨111995902067179169942060327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74663934711452779961373551 111995902067179169942060327)
      ·
        refine ⟨167993853100768754913090491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111995902067179169942060327 167993853100768754913090491)
        ·
          refine ⟨251990779651153132369635737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167993853100768754913090491 251990779651153132369635737)
          ·
            refine ⟨188993084738364849277226803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251990779651153132369635737 188993084738364849277226803)
            ·
              refine ⟨283489627107547273915840205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188993084738364849277226803 283489627107547273915840205)
              ·
                refine ⟨106308610165330227718440077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283489627107547273915840205 106308610165330227718440077)
                ·
                  refine ⟨39865728811998835394415029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106308610165330227718440077 39865728811998835394415029)
                  ·
                    refine ⟨3737412076124890818226409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39865728811998835394415029 3737412076124890818226409)
                    ·
                      refine ⟨2803059057093668113669807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3737412076124890818226409 2803059057093668113669807)
                      ·
                        rfl

theorem cell23_5458938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 3, 5, 2].length) (baseStart_5458938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458938 prefixEnd_5458938 := by exact prefixLift 5458938
  have htrace : WordTrace (prefixWord ++ tailWord_5458938) baseStart_5458938 baseEnd_5458938 := by
    simpa [prefixWord, tailWord_5458938, baseEnd_5458938] using wordTrace_append hprefix tailTrace_5458938
  have hstable : (prefixWord ++ tailWord_5458938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458938).length < 2 ^ (prefixWord ++ tailWord_5458938).sum := by decide
  have hdescent : baseEnd_5458938 < baseStart_5458938 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458955 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 2, 3, 2]
def baseStart_5458955 : Nat := 118140960795 + 5458955 * 2 ^ 59
def prefixEnd_5458955 : Nat := 4983230072969 + 3 ^ 40 * 5458955 * 2
def baseEnd_5458955 : Nat := 2803067786264794547157229

theorem tailTrace_5458955 : CollatzResearch.WordTrace tailWord_5458955 prefixEnd_5458955 2803067786264794547157229 := by
  unfold tailWord_5458955
  simp only [CollatzResearch.WordTrace]
  refine ⟨199104445938145825133698319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132736297292097216755798879 199104445938145825133698319)
  ·
    refine ⟨298656668907218737700547479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199104445938145825133698319 298656668907218737700547479)
    ·
      refine ⟨447985003360828106550821219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298656668907218737700547479 447985003360828106550821219)
      ·
        refine ⟨671977505041242159826231829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447985003360828106550821219 671977505041242159826231829)
        ·
          refine ⟨31498945548808226241854617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 671977505041242159826231829 31498945548808226241854617)
          ·
            refine ⟨23624209161606169681390963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31498945548808226241854617 23624209161606169681390963)
            ·
              refine ⟨35436313742409254522086445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23624209161606169681390963 35436313742409254522086445)
              ·
                refine ⟨13288617653403470445782417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35436313742409254522086445 13288617653403470445782417)
                ·
                  refine ⟨9966463240052602834336813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13288617653403470445782417 9966463240052602834336813)
                  ·
                    refine ⟨3737423715019726062876305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9966463240052602834336813 3737423715019726062876305)
                    ·
                      refine ⟨2803067786264794547157229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3737423715019726062876305 2803067786264794547157229)
                      ·
                        rfl

theorem cell23_5458955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 2, 3, 2].length) (baseStart_5458955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458955 prefixEnd_5458955 := by exact prefixLift 5458955
  have htrace : WordTrace (prefixWord ++ tailWord_5458955) baseStart_5458955 baseEnd_5458955 := by
    simpa [prefixWord, tailWord_5458955, baseEnd_5458955] using wordTrace_append hprefix tailTrace_5458955
  have hstable : (prefixWord ++ tailWord_5458955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458955).length < 2 ^ (prefixWord ++ tailWord_5458955).sum := by decide
  have hdescent : baseEnd_5458955 < baseStart_5458955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458979 : List Nat := [1, 1, 1, 4, 3, 2, 4, 2, 1, 1, 3]
def baseStart_5458979 : Nat := 118140960795 + 5458979 * 2 ^ 59
def prefixEnd_5458979 : Nat := 4983230072969 + 3 ^ 40 * 5458979 * 2
def baseEnd_5458979 : Nat := 2803080109800502453257119

theorem tailTrace_5458979 : CollatzResearch.WordTrace tailWord_5458979 prefixEnd_5458979 2803080109800502453257119 := by
  unfold tailWord_5458979
  simp only [CollatzResearch.WordTrace]
  refine ⟨199105321290058877232571991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132736880860039251488381327 199105321290058877232571991)
  ·
    refine ⟨298657981935088315848857987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199105321290058877232571991 298657981935088315848857987)
    ·
      refine ⟨447986972902632473773286981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298657981935088315848857987 447986972902632473773286981)
      ·
        refine ⟨83997557419243588832491309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 447986972902632473773286981 83997557419243588832491309)
        ·
          refine ⟨31499084032216345812184241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83997557419243588832491309 31499084032216345812184241)
          ·
            refine ⟨23624313024162259359138181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31499084032216345812184241 23624313024162259359138181)
            ·
              refine ⟨4429558692030423629838409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23624313024162259359138181 4429558692030423629838409)
              ·
                refine ⟨3322169019022817722378807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4429558692030423629838409 3322169019022817722378807)
                ·
                  refine ⟨4983253528534226583568211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3322169019022817722378807 4983253528534226583568211)
                  ·
                    refine ⟨7474880292801339875352317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4983253528534226583568211 7474880292801339875352317)
                    ·
                      refine ⟨2803080109800502453257119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7474880292801339875352317 2803080109800502453257119)
                      ·
                        rfl

theorem cell23_5458979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 4, 2, 1, 1, 3].length) (baseStart_5458979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458979 prefixEnd_5458979 := by exact prefixLift 5458979
  have htrace : WordTrace (prefixWord ++ tailWord_5458979) baseStart_5458979 baseEnd_5458979 := by
    simpa [prefixWord, tailWord_5458979, baseEnd_5458979] using wordTrace_append hprefix tailTrace_5458979
  have hstable : (prefixWord ++ tailWord_5458979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458979).length < 2 ^ (prefixWord ++ tailWord_5458979).sum := by decide
  have hdescent : baseEnd_5458979 < baseStart_5458979 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5458988 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 3]
def baseStart_5458988 : Nat := 118140960795 + 5458988 * 2 ^ 59
def prefixEnd_5458988 : Nat := 4983230072969 + 3 ^ 40 * 5458988 * 2
def baseEnd_5458988 : Nat := 2803084731126392918044577

theorem tailTrace_5458988 : CollatzResearch.WordTrace tailWord_5458988 prefixEnd_5458988 2803084731126392918044577 := by
  unfold tailWord_5458988
  simp only [CollatzResearch.WordTrace]
  refine ⟨99552824773513135884824809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132737099698017514513099745 99552824773513135884824809)
  ·
    refine ⟨74664618580134851913618607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99552824773513135884824809 74664618580134851913618607)
    ·
      refine ⟨111996927870202277870427911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74664618580134851913618607 111996927870202277870427911)
      ·
        refine ⟨167995391805303416805641867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111996927870202277870427911 167995391805303416805641867)
        ·
          refine ⟨251993087707955125208462801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167995391805303416805641867 251993087707955125208462801)
          ·
            refine ⟨188994815780966343906347101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 251993087707955125208462801 188994815780966343906347101)
            ·
              refine ⟨70873055917862378964880163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188994815780966343906347101 70873055917862378964880163)
              ·
                refine ⟨106309583876793568447320245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70873055917862378964880163 106309583876793568447320245)
                ·
                  refine ⟨9966523488449397041936273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106309583876793568447320245 9966523488449397041936273)
                  ·
                    refine ⟨7474892616337047781452205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9966523488449397041936273 7474892616337047781452205)
                    ·
                      refine ⟨2803084731126392918044577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7474892616337047781452205 2803084731126392918044577)
                      ·
                        rfl

theorem cell23_5458988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 3].length) (baseStart_5458988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5458988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5458988 prefixEnd_5458988 := by exact prefixLift 5458988
  have htrace : WordTrace (prefixWord ++ tailWord_5458988) baseStart_5458988 baseEnd_5458988 := by
    simpa [prefixWord, tailWord_5458988, baseEnd_5458988] using wordTrace_append hprefix tailTrace_5458988
  have hstable : (prefixWord ++ tailWord_5458988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5458988).length < 2 ^ (prefixWord ++ tailWord_5458988).sum := by decide
  have hdescent : baseEnd_5458988 < baseStart_5458988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5458988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459005 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_5459005 : Nat := 118140960795 + 5459005 * 2 ^ 59
def prefixEnd_5459005 : Nat := 4983230072969 + 3 ^ 40 * 5459005 * 2
def baseEnd_5459005 : Nat := 2803093460297519351531999

theorem tailTrace_5459005 : CollatzResearch.WordTrace tailWord_5459005 prefixEnd_5459005 2803093460297519351531999 := by
  unfold tailWord_5459005
  simp only [CollatzResearch.WordTrace]
  refine ⟨199106269587964683673018469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132737513058643122448678979 199106269587964683673018469)
  ·
    refine ⟨37332425547743378188690963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199106269587964683673018469 37332425547743378188690963)
    ·
      refine ⟨55998638321615067283036445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37332425547743378188690963 55998638321615067283036445)
      ·
        refine ⟨20999489370605650231138667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55998638321615067283036445 20999489370605650231138667)
        ·
          refine ⟨31499234055908475346708001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20999489370605650231138667 31499234055908475346708001)
          ·
            refine ⟨23624425541931356510031001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31499234055908475346708001 23624425541931356510031001)
            ·
              refine ⟨17718319156448517382523251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23624425541931356510031001 17718319156448517382523251)
              ·
                refine ⟨26577478734672776073784877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17718319156448517382523251 26577478734672776073784877)
                ·
                  refine ⟨9966554525502291027669329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26577478734672776073784877 9966554525502291027669329)
                  ·
                    refine ⟨7474915894126718270751997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9966554525502291027669329 7474915894126718270751997)
                    ·
                      refine ⟨2803093460297519351531999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7474915894126718270751997 2803093460297519351531999)
                      ·
                        rfl

theorem cell23_5459005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_5459005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459005 prefixEnd_5459005 := by exact prefixLift 5459005
  have htrace : WordTrace (prefixWord ++ tailWord_5459005) baseStart_5459005 baseEnd_5459005 := by
    simpa [prefixWord, tailWord_5459005, baseEnd_5459005] using wordTrace_append hprefix tailTrace_5459005
  have hstable : (prefixWord ++ tailWord_5459005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459005).length < 2 ^ (prefixWord ++ tailWord_5459005).sum := by decide
  have hdescent : baseEnd_5459005 < baseStart_5459005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459008 : List Nat := [2, 1, 1, 2, 2, 3, 5, 7]
def baseStart_5459008 : Nat := 118140960795 + 5459008 * 2 ^ 59
def prefixEnd_5459008 : Nat := 4983230072969 + 3 ^ 40 * 5459008 * 2
def baseEnd_5459008 : Nat := 103818333360721586659055

theorem tailTrace_5459008 : CollatzResearch.WordTrace tailWord_5459008 prefixEnd_5459008 103818333360721586659055 := by
  unfold tailWord_5459008
  simp only [CollatzResearch.WordTrace]
  refine ⟨99553189503476907592688839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132737586004635876790251785 99553189503476907592688839)
  ·
    refine ⟨149329784255215361389033259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99553189503476907592688839 149329784255215361389033259)
    ·
      refine ⟨223994676382823042083549889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149329784255215361389033259 223994676382823042083549889)
      ·
        refine ⟨167996007287117281562662417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 223994676382823042083549889 167996007287117281562662417)
        ·
          refine ⟨125997005465337961171996813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167996007287117281562662417 125997005465337961171996813)
          ·
            refine ⟨47248877049501735439498805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125997005465337961171996813 47248877049501735439498805)
            ·
              refine ⟨4429582223390787697453013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47248877049501735439498805 4429582223390787697453013)
              ·
                refine ⟨103818333360721586659055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4429582223390787697453013 103818333360721586659055)
                ·
                  rfl

theorem cell23_5459008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 7].length) (baseStart_5459008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459008 prefixEnd_5459008 := by exact prefixLift 5459008
  have htrace : WordTrace (prefixWord ++ tailWord_5459008) baseStart_5459008 baseEnd_5459008 := by
    simpa [prefixWord, tailWord_5459008, baseEnd_5459008] using wordTrace_append hprefix tailTrace_5459008
  have hstable : (prefixWord ++ tailWord_5459008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459008).length < 2 ^ (prefixWord ++ tailWord_5459008).sum := by decide
  have hdescent : baseEnd_5459008 < baseStart_5459008 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459075 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 3, 4, 2]
def baseStart_5459075 : Nat := 118140960795 + 5459075 * 2 ^ 59
def prefixEnd_5459075 : Nat := 4983230072969 + 3 ^ 40 * 5459075 * 2
def baseEnd_5459075 : Nat := 2803129403943334077656677

theorem tailTrace_5459075 : CollatzResearch.WordTrace tailWord_5459075 prefixEnd_5459075 2803129403943334077656677 := by
  unfold tailWord_5459075
  simp only [CollatzResearch.WordTrace]
  refine ⟨199108822697711085628066679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132739215131807390418711119 199108822697711085628066679)
  ·
    refine ⟨298663234046566628442100019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199108822697711085628066679 298663234046566628442100019)
    ·
      refine ⟨447994851069849942663150029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298663234046566628442100019 447994851069849942663150029)
      ·
        refine ⟨167998069151193728498681261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 447994851069849942663150029 167998069151193728498681261)
        ·
          refine ⟨62999275931697648187005473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167998069151193728498681261 62999275931697648187005473)
          ·
            refine ⟨47249456948773236140254105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62999275931697648187005473 47249456948773236140254105)
            ·
              refine ⟨35437092711579927105190579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47249456948773236140254105 35437092711579927105190579)
              ·
                refine ⟨53155639067369890657785869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35437092711579927105190579 53155639067369890657785869)
                ·
                  refine ⟨19933364650263708996669701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53155639067369890657785869 19933364650263708996669701)
                  ·
                    refine ⟨3737505871924445436875569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19933364650263708996669701 3737505871924445436875569)
                    ·
                      refine ⟨2803129403943334077656677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3737505871924445436875569 2803129403943334077656677)
                      ·
                        rfl

theorem cell23_5459075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 3, 4, 2].length) (baseStart_5459075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459075 prefixEnd_5459075 := by exact prefixLift 5459075
  have htrace : WordTrace (prefixWord ++ tailWord_5459075) baseStart_5459075 baseEnd_5459075 := by
    simpa [prefixWord, tailWord_5459075, baseEnd_5459075] using wordTrace_append hprefix tailTrace_5459075
  have hstable : (prefixWord ++ tailWord_5459075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459075).length < 2 ^ (prefixWord ++ tailWord_5459075).sum := by decide
  have hdescent : baseEnd_5459075 < baseStart_5459075 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459088 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 4]
def baseStart_5459088 : Nat := 118140960795 + 5459088 * 2 ^ 59
def prefixEnd_5459088 : Nat := 4983230072969 + 3 ^ 40 * 5459088 * 2
def baseEnd_5459088 : Nat := 2803136079191842526794117

theorem tailTrace_5459088 : CollatzResearch.WordTrace tailWord_5459088 prefixEnd_5459088 2803136079191842526794117 := by
  unfold tailWord_5459088
  simp only [CollatzResearch.WordTrace]
  refine ⟨99554648423331994424144959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132739531231109325898859945 99554648423331994424144959)
  ·
    refine ⟨149331972634997991636217439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99554648423331994424144959 149331972634997991636217439)
    ·
      refine ⟨223997958952496987454326159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149331972634997991636217439 223997958952496987454326159)
      ·
        refine ⟨335996938428745481181489239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223997958952496987454326159 335996938428745481181489239)
        ·
          refine ⟨503995407643118221772233859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335996938428745481181489239 503995407643118221772233859)
          ·
            refine ⟨755993111464677332658350789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 503995407643118221772233859 755993111464677332658350789)
            ·
              refine ⟨141748708399626999873440773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 755993111464677332658350789 141748708399626999873440773)
              ·
                refine ⟨26577882824930062476270145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141748708399626999873440773 26577882824930062476270145)
                ·
                  refine ⟨19933412118697546857202609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26577882824930062476270145 19933412118697546857202609)
                  ·
                    refine ⟨14950059089023160142901957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19933412118697546857202609 14950059089023160142901957)
                    ·
                      refine ⟨2803136079191842526794117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14950059089023160142901957 2803136079191842526794117)
                      ·
                        rfl

theorem cell23_5459088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_5459088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459088 prefixEnd_5459088 := by exact prefixLift 5459088
  have htrace : WordTrace (prefixWord ++ tailWord_5459088) baseStart_5459088 baseEnd_5459088 := by
    simpa [prefixWord, tailWord_5459088, baseEnd_5459088] using wordTrace_append hprefix tailTrace_5459088
  have hstable : (prefixWord ++ tailWord_5459088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459088).length < 2 ^ (prefixWord ++ tailWord_5459088).sum := by decide
  have hdescent : baseEnd_5459088 < baseStart_5459088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459103 : List Nat := [1, 1, 2, 6, 3, 1, 2, 1, 2, 1, 3]
def baseStart_5459103 : Nat := 118140960795 + 5459103 * 2 ^ 59
def prefixEnd_5459103 : Nat := 4983230072969 + 3 ^ 40 * 5459103 * 2
def baseEnd_5459103 : Nat := 2803143781401659968106549

theorem tailTrace_5459103 : CollatzResearch.WordTrace tailWord_5459103 prefixEnd_5459103 2803143781401659968106549 := by
  unfold tailWord_5459103
  simp only [CollatzResearch.WordTrace]
  refine ⟨199109843941609646410085963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132739895961073097606723975 199109843941609646410085963)
  ·
    refine ⟨298664765912414469615128945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199109843941609646410085963 298664765912414469615128945)
    ·
      refine ⟨223998574434310852211346709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298664765912414469615128945 223998574434310852211346709)
      ·
        refine ⟨10499933176608321197406877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 223998574434310852211346709 10499933176608321197406877)
        ·
          refine ⟨3937474941228120449027579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10499933176608321197406877 3937474941228120449027579)
          ·
            refine ⟨5906212411842180673541369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3937474941228120449027579 5906212411842180673541369)
            ·
              refine ⟨4429659308881635505156027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5906212411842180673541369 4429659308881635505156027)
              ·
                refine ⟨6644488963322453257734041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4429659308881635505156027 6644488963322453257734041)
                ·
                  refine ⟨4983366722491839943300531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6644488963322453257734041 4983366722491839943300531)
                  ·
                    refine ⟨7475050083737759914950797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4983366722491839943300531 7475050083737759914950797)
                    ·
                      refine ⟨2803143781401659968106549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7475050083737759914950797 2803143781401659968106549)
                      ·
                        rfl

theorem cell23_5459103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 2, 1, 3].length) (baseStart_5459103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459103 prefixEnd_5459103 := by exact prefixLift 5459103
  have htrace : WordTrace (prefixWord ++ tailWord_5459103) baseStart_5459103 baseEnd_5459103 := by
    simpa [prefixWord, tailWord_5459103, baseEnd_5459103] using wordTrace_append hprefix tailTrace_5459103
  have hstable : (prefixWord ++ tailWord_5459103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459103).length < 2 ^ (prefixWord ++ tailWord_5459103).sum := by decide
  have hdescent : baseEnd_5459103 < baseStart_5459103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459109 : List Nat := [1, 3, 1, 2, 1, 5, 1, 3, 2, 2, 2]
def baseStart_5459109 : Nat := 118140960795 + 5459109 * 2 ^ 59
def prefixEnd_5459109 : Nat := 4983230072969 + 3 ^ 40 * 5459109 * 2
def baseEnd_5459109 : Nat := 2803146862285586944631521

theorem tailTrace_5459109 : CollatzResearch.WordTrace tailWord_5459109 prefixEnd_5459109 2803146862285586944631521 := by
  unfold tailWord_5459109
  simp only [CollatzResearch.WordTrace]
  refine ⟨199110062779587909434804381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132740041853058606289869587 199110062779587909434804381)
  ·
    refine ⟨74666273542345466038051643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199110062779587909434804381 74666273542345466038051643)
    ·
      refine ⟨111999410313518199057077465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74666273542345466038051643 111999410313518199057077465)
      ·
        refine ⟨83999557735138649292808099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111999410313518199057077465 83999557735138649292808099)
        ·
          refine ⟨125999336602707973939212149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83999557735138649292808099 125999336602707973939212149)
          ·
            refine ⟨11812437806503872556801139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125999336602707973939212149 11812437806503872556801139)
            ·
              refine ⟨17718656709755808835201709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11812437806503872556801139 17718656709755808835201709)
              ·
                refine ⟨6644496266158428313200641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17718656709755808835201709 6644496266158428313200641)
                ·
                  refine ⟨4983372199618821234900481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6644496266158428313200641 4983372199618821234900481)
                  ·
                    refine ⟨3737529149714115926175361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4983372199618821234900481 3737529149714115926175361)
                    ·
                      refine ⟨2803146862285586944631521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3737529149714115926175361 2803146862285586944631521)
                      ·
                        rfl

theorem cell23_5459109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 3, 2, 2, 2].length) (baseStart_5459109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459109 prefixEnd_5459109 := by exact prefixLift 5459109
  have htrace : WordTrace (prefixWord ++ tailWord_5459109) baseStart_5459109 baseEnd_5459109 := by
    simpa [prefixWord, tailWord_5459109, baseEnd_5459109] using wordTrace_append hprefix tailTrace_5459109
  have hstable : (prefixWord ++ tailWord_5459109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459109).length < 2 ^ (prefixWord ++ tailWord_5459109).sum := by decide
  have hdescent : baseEnd_5459109 < baseStart_5459109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459182 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_5459182 : Nat := 118140960795 + 5459182 * 2 ^ 59
def prefixEnd_5459182 : Nat := 4983230072969 + 3 ^ 40 * 5459182 * 2
def baseEnd_5459182 : Nat := 2803184346373365159018685

theorem tailTrace_5459182 : CollatzResearch.WordTrace tailWord_5459182 prefixEnd_5459182 2803184346373365159018685 := by
  unfold tailWord_5459182
  simp only [CollatzResearch.WordTrace]
  refine ⟨24889090663540430362776475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132741816872215628601474533 24889090663540430362776475)
  ·
    refine ⟨37333635995310645544164713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24889090663540430362776475 37333635995310645544164713)
    ·
      refine ⟨28000226996482984158123535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37333635995310645544164713 28000226996482984158123535)
      ·
        refine ⟨42000340494724476237185303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28000226996482984158123535 42000340494724476237185303)
        ·
          refine ⟨63000510742086714355777955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42000340494724476237185303 63000510742086714355777955)
          ·
            refine ⟨94500766113130071533666933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63000510742086714355777955 94500766113130071533666933)
            ·
              refine ⟨8859446823105944206281275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94500766113130071533666933 8859446823105944206281275)
              ·
                refine ⟨13289170234658916309421913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8859446823105944206281275 13289170234658916309421913)
                ·
                  refine ⟨9966877675994187232066435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13289170234658916309421913 9966877675994187232066435)
                  ·
                    refine ⟨14950316513991280848099653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9966877675994187232066435 14950316513991280848099653)
                    ·
                      refine ⟨2803184346373365159018685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14950316513991280848099653 2803184346373365159018685)
                      ·
                        rfl

theorem cell23_5459182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_5459182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459182 prefixEnd_5459182 := by exact prefixLift 5459182
  have htrace : WordTrace (prefixWord ++ tailWord_5459182) baseStart_5459182 baseEnd_5459182 := by
    simpa [prefixWord, tailWord_5459182, baseEnd_5459182] using wordTrace_append hprefix tailTrace_5459182
  have hstable : (prefixWord ++ tailWord_5459182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459182).length < 2 ^ (prefixWord ++ tailWord_5459182).sum := by decide
  have hdescent : baseEnd_5459182 < baseStart_5459182 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459255 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 4]
def baseStart_5459255 : Nat := 118140960795 + 5459255 * 2 ^ 59
def prefixEnd_5459255 : Nat := 4983230072969 + 3 ^ 40 * 5459255 * 2
def baseEnd_5459255 : Nat := 2803221830461143373405849

theorem tailTrace_5459255 : CollatzResearch.WordTrace tailWord_5459255 prefixEnd_5459255 2803221830461143373405849 := by
  unfold tailWord_5459255
  simp only [CollatzResearch.WordTrace]
  refine ⟨199115387837058976369619219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132743591891372650913079479 199115387837058976369619219)
  ·
    refine ⟨298673081755588464554428829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199115387837058976369619219 298673081755588464554428829)
    ·
      refine ⟨112002405658345674207910811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298673081755588464554428829 112002405658345674207910811)
      ·
        refine ⟨168003608487518511311866217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112002405658345674207910811 168003608487518511311866217)
        ·
          refine ⟨126002706365638883483899663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168003608487518511311866217 126002706365638883483899663)
          ·
            refine ⟨189004059548458325225849495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126002706365638883483899663 189004059548458325225849495)
            ·
              refine ⟨283506089322687487838774243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189004059548458325225849495 283506089322687487838774243)
              ·
                refine ⟨425259133984031231758161365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283506089322687487838774243 425259133984031231758161365)
                ·
                  refine ⟨9967010952750731994331907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 425259133984031231758161365 9967010952750731994331907)
                  ·
                    refine ⟨14950516429126097991497861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9967010952750731994331907 14950516429126097991497861)
                    ·
                      refine ⟨2803221830461143373405849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14950516429126097991497861 2803221830461143373405849)
                      ·
                        rfl

theorem cell23_5459255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_5459255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459255 prefixEnd_5459255 := by exact prefixLift 5459255
  have htrace : WordTrace (prefixWord ++ tailWord_5459255) baseStart_5459255 baseEnd_5459255 := by
    simpa [prefixWord, tailWord_5459255, baseEnd_5459255] using wordTrace_append hprefix tailTrace_5459255
  have hstable : (prefixWord ++ tailWord_5459255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459255).length < 2 ^ (prefixWord ++ tailWord_5459255).sum := by decide
  have hdescent : baseEnd_5459255 < baseStart_5459255 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459289 : List Nat := [1, 2, 1, 2, 2, 2, 2, 4, 3, 2, 2]
def baseStart_5459289 : Nat := 118140960795 + 5459289 * 2 ^ 59
def prefixEnd_5459289 : Nat := 4983230072969 + 3 ^ 40 * 5459289 * 2
def baseEnd_5459289 : Nat := 2803239288803396240380693

theorem tailTrace_5459289 : CollatzResearch.WordTrace tailWord_5459289 prefixEnd_5459289 2803239288803396240380693 := by
  unfold tailWord_5459289
  simp only [CollatzResearch.WordTrace]
  refine ⟨199116627918935800176356921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132744418612623866784237947 199116627918935800176356921)
  ·
    refine ⟨149337470939201850132267691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199116627918935800176356921 149337470939201850132267691)
    ·
      refine ⟨224006206408802775198401537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149337470939201850132267691 224006206408802775198401537)
      ·
        refine ⟨168004654806602081398801153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224006206408802775198401537 168004654806602081398801153)
        ·
          refine ⟨126003491104951561049100865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168004654806602081398801153 126003491104951561049100865)
          ·
            refine ⟨94502618328713670786825649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126003491104951561049100865 94502618328713670786825649)
            ·
              refine ⟨70876963746535253090119237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94502618328713670786825649 70876963746535253090119237)
              ·
                refine ⟨13289430702475359954397357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70876963746535253090119237 13289430702475359954397357)
                ·
                  refine ⟨4983536513428259982899009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13289430702475359954397357 4983536513428259982899009)
                  ·
                    refine ⟨3737652385071194987174257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4983536513428259982899009 3737652385071194987174257)
                    ·
                      refine ⟨2803239288803396240380693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3737652385071194987174257 2803239288803396240380693)
                      ·
                        rfl

theorem cell23_5459289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 4, 3, 2, 2].length) (baseStart_5459289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459289 prefixEnd_5459289 := by exact prefixLift 5459289
  have htrace : WordTrace (prefixWord ++ tailWord_5459289) baseStart_5459289 baseEnd_5459289 := by
    simpa [prefixWord, tailWord_5459289, baseEnd_5459289] using wordTrace_append hprefix tailTrace_5459289
  have hstable : (prefixWord ++ tailWord_5459289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459289).length < 2 ^ (prefixWord ++ tailWord_5459289).sum := by decide
  have hdescent : baseEnd_5459289 < baseStart_5459289 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459309 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_5459309 : Nat := 118140960795 + 5459309 * 2 ^ 59
def prefixEnd_5459309 : Nat := 4983230072969 + 3 ^ 40 * 5459309 * 2
def baseEnd_5459309 : Nat := 2803249558416486162130601

theorem tailTrace_5459309 : CollatzResearch.WordTrace tailWord_5459309 prefixEnd_5459309 2803249558416486162130601 := by
  unfold tailWord_5459309
  simp only [CollatzResearch.WordTrace]
  refine ⟨199117357378863343592084981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132744904919242229061389987 199117357378863343592084981)
  ·
    refine ⟨18667252254268438461757967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199117357378863343592084981 18667252254268438461757967)
    ·
      refine ⟨28000878381402657692636951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18667252254268438461757967 28000878381402657692636951)
      ·
        refine ⟨42001317572103986538955427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28000878381402657692636951 42001317572103986538955427)
        ·
          refine ⟨63001976358155979808433141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42001317572103986538955427 63001976358155979808433141)
          ·
            refine ⟨5906435283577123107040607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63001976358155979808433141 5906435283577123107040607)
            ·
              refine ⟨8859652925365684660560911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5906435283577123107040607 8859652925365684660560911)
              ·
                refine ⟨13289479388048526990841367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8859652925365684660560911 13289479388048526990841367)
                ·
                  refine ⟨19934219082072790486262051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13289479388048526990841367 19934219082072790486262051)
                  ·
                    refine ⟨29901328623109185729393077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19934219082072790486262051 29901328623109185729393077)
                    ·
                      refine ⟨2803249558416486162130601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29901328623109185729393077 2803249558416486162130601)
                      ·
                        rfl

theorem cell23_5459309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_5459309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459309 prefixEnd_5459309 := by exact prefixLift 5459309
  have htrace : WordTrace (prefixWord ++ tailWord_5459309) baseStart_5459309 baseEnd_5459309 := by
    simpa [prefixWord, tailWord_5459309, baseEnd_5459309] using wordTrace_append hprefix tailTrace_5459309
  have hstable : (prefixWord ++ tailWord_5459309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459309).length < 2 ^ (prefixWord ++ tailWord_5459309).sum := by decide
  have hdescent : baseEnd_5459309 < baseStart_5459309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459317 : List Nat := [1, 3, 4, 1, 4, 1, 2, 2, 1, 1, 3]
def baseStart_5459317 : Nat := 118140960795 + 5459317 * 2 ^ 59
def prefixEnd_5459317 : Nat := 4983230072969 + 3 ^ 40 * 5459317 * 2
def baseEnd_5459317 : Nat := 2803253666261722130830565

theorem tailTrace_5459317 : CollatzResearch.WordTrace tailWord_5459317 prefixEnd_5459317 2803253666261722130830565 := by
  unfold tailWord_5459317
  simp only [CollatzResearch.WordTrace]
  refine ⟨199117649162834360958376205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132745099441889573972250803 199117649162834360958376205)
  ·
    refine ⟨74669118436062885359391077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199117649162834360958376205 74669118436062885359391077)
    ·
      refine ⟨14000459706761791004885827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74669118436062885359391077 14000459706761791004885827)
      ·
        refine ⟨21000689560142686507328741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14000459706761791004885827 21000689560142686507328741)
        ·
          refine ⟨3937629292526753720124139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21000689560142686507328741 3937629292526753720124139)
          ·
            refine ⟨5906443938790130580186209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3937629292526753720124139 5906443938790130580186209)
            ·
              refine ⟨4429832954092597935139657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5906443938790130580186209 4429832954092597935139657)
              ·
                refine ⟨3322374715569448451354743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4429832954092597935139657 3322374715569448451354743)
                ·
                  refine ⟨4983562073354172677032115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3322374715569448451354743 4983562073354172677032115)
                  ·
                    refine ⟨7475343110031259015548173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4983562073354172677032115 7475343110031259015548173)
                    ·
                      refine ⟨2803253666261722130830565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7475343110031259015548173 2803253666261722130830565)
                      ·
                        rfl

theorem cell23_5459317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_5459317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459317 prefixEnd_5459317 := by exact prefixLift 5459317
  have htrace : WordTrace (prefixWord ++ tailWord_5459317) baseStart_5459317 baseEnd_5459317 := by
    simpa [prefixWord, tailWord_5459317, baseEnd_5459317] using wordTrace_append hprefix tailTrace_5459317
  have hstable : (prefixWord ++ tailWord_5459317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459317).length < 2 ^ (prefixWord ++ tailWord_5459317).sum := by decide
  have hdescent : baseEnd_5459317 < baseStart_5459317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459325 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_5459325 : Nat := 118140960795 + 5459325 * 2 ^ 59
def prefixEnd_5459325 : Nat := 4983230072969 + 3 ^ 40 * 5459325 * 2
def baseEnd_5459325 : Nat := 934419258035652699843509

theorem tailTrace_5459325 : CollatzResearch.WordTrace tailWord_5459325 prefixEnd_5459325 934419258035652699843509 := by
  unfold tailWord_5459325
  simp only [CollatzResearch.WordTrace]
  refine ⟨199117940946805378324667429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132745293964536918883111619 199117940946805378324667429)
  ·
    refine ⟨37334613927526008435875143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199117940946805378324667429 37334613927526008435875143)
    ·
      refine ⟨56001920891289012653812715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37334613927526008435875143 56001920891289012653812715)
      ·
        refine ⟨84002881336933518980719073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56001920891289012653812715 84002881336933518980719073)
        ·
          refine ⟨63002161002700139235539305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84002881336933518980719073 63002161002700139235539305)
          ·
            refine ⟨47251620752025104426654479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63002161002700139235539305 47251620752025104426654479)
            ·
              refine ⟨70877431128037656639981719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47251620752025104426654479 70877431128037656639981719)
              ·
                refine ⟨106316146692056484959972579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70877431128037656639981719 106316146692056484959972579)
                ·
                  refine ⟨159474220038084727439958869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106316146692056484959972579 159474220038084727439958869)
                  ·
                    refine ⟨934419258035652699843509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 159474220038084727439958869 934419258035652699843509)
                    ·
                      rfl

theorem cell23_5459325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_5459325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459325 prefixEnd_5459325 := by exact prefixLift 5459325
  have htrace : WordTrace (prefixWord ++ tailWord_5459325) baseStart_5459325 baseEnd_5459325 := by
    simpa [prefixWord, tailWord_5459325, baseEnd_5459325] using wordTrace_append hprefix tailTrace_5459325
  have hstable : (prefixWord ++ tailWord_5459325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459325).length < 2 ^ (prefixWord ++ tailWord_5459325).sum := by decide
  have hdescent : baseEnd_5459325 < baseStart_5459325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459329 : List Nat := [1, 2, 4, 3, 2, 2, 1, 8]
def baseStart_5459329 : Nat := 118140960795 + 5459329 * 2 ^ 59
def prefixEnd_5459329 : Nat := 4983230072969 + 3 ^ 40 * 5459329 * 2
def baseEnd_5459329 : Nat := 103824438075169484588167

theorem tailTrace_5459329 : CollatzResearch.WordTrace tailWord_5459329 prefixEnd_5459329 103824438075169484588167 := by
  unfold tailWord_5459329
  simp only [CollatzResearch.WordTrace]
  refine ⟨199118086838790887007813041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132745391225860591338542027 199118086838790887007813041)
  ·
    refine ⟨149338565129093165255859781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199118086838790887007813041 149338565129093165255859781)
    ·
      refine ⟨28000980961704968485473709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149338565129093165255859781 28000980961704968485473709)
      ·
        refine ⟨10500367860639363182052641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28000980961704968485473709 10500367860639363182052641)
        ·
          refine ⟨7875275895479522386539481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10500367860639363182052641 7875275895479522386539481)
          ·
            refine ⟨5906456921609641789904611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7875275895479522386539481 5906456921609641789904611)
            ·
              refine ⟨8859685382414462684856917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5906456921609641789904611 8859685382414462684856917)
              ·
                refine ⟨103824438075169484588167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8859685382414462684856917 103824438075169484588167)
                ·
                  rfl

theorem cell23_5459329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 8].length) (baseStart_5459329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459329 prefixEnd_5459329 := by exact prefixLift 5459329
  have htrace : WordTrace (prefixWord ++ tailWord_5459329) baseStart_5459329 baseEnd_5459329 := by
    simpa [prefixWord, tailWord_5459329, baseEnd_5459329] using wordTrace_append hprefix tailTrace_5459329
  have hstable : (prefixWord ++ tailWord_5459329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459329).length < 2 ^ (prefixWord ++ tailWord_5459329).sum := by decide
  have hdescent : baseEnd_5459329 < baseStart_5459329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459339 : List Nat := [1, 1, 1, 1, 4, 3, 1, 5, 2, 1, 3]
def baseStart_5459339 : Nat := 118140960795 + 5459339 * 2 ^ 59
def prefixEnd_5459339 : Nat := 4983230072969 + 3 ^ 40 * 5459339 * 2
def baseEnd_5459339 : Nat := 2803264962836121044755463

theorem tailTrace_5459339 : CollatzResearch.WordTrace tailWord_5459339 prefixEnd_5459339 2803264962836121044755463 := by
  unfold tailWord_5459339
  simp only [CollatzResearch.WordTrace]
  refine ⟨199118451568754658715677071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132745634379169772477118047 199118451568754658715677071)
  ·
    refine ⟨298677677353131988073515607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199118451568754658715677071 298677677353131988073515607)
    ·
      refine ⟨448016516029697982110273411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298677677353131988073515607 448016516029697982110273411)
      ·
        refine ⟨672024774044546973165410117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448016516029697982110273411 672024774044546973165410117)
        ·
          refine ⟨126004645133352557468514397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 672024774044546973165410117 126004645133352557468514397)
          ·
            refine ⟨47251741925007209050692899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126004645133352557468514397 47251741925007209050692899)
            ·
              refine ⟨70877612887510813576039349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47251741925007209050692899 70877612887510813576039349)
              ·
                refine ⟨6644776208204138772753689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70877612887510813576039349 6644776208204138772753689)
                ·
                  refine ⟨4983582156153104079565267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6644776208204138772753689 4983582156153104079565267)
                  ·
                    refine ⟨7475373234229656119347901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4983582156153104079565267 7475373234229656119347901)
                    ·
                      refine ⟨2803264962836121044755463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7475373234229656119347901 2803264962836121044755463)
                      ·
                        rfl

theorem cell23_5459339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 1, 3].length) (baseStart_5459339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459339 prefixEnd_5459339 := by exact prefixLift 5459339
  have htrace : WordTrace (prefixWord ++ tailWord_5459339) baseStart_5459339 baseEnd_5459339 := by
    simpa [prefixWord, tailWord_5459339, baseEnd_5459339] using wordTrace_append hprefix tailTrace_5459339
  have hstable : (prefixWord ++ tailWord_5459339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459339).length < 2 ^ (prefixWord ++ tailWord_5459339).sum := by decide
  have hdescent : baseEnd_5459339 < baseStart_5459339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459346 : List Nat := [3, 2, 3, 3, 1, 1, 3, 7]
def baseStart_5459346 : Nat := 118140960795 + 5459346 * 2 ^ 59
def prefixEnd_5459346 : Nat := 4983230072969 + 3 ^ 40 * 5459346 * 2
def baseEnd_5459346 : Nat := 103824761377803796939553

theorem tailTrace_5459346 : CollatzResearch.WordTrace tailWord_5459346 prefixEnd_5459346 103824761377803796939553 := by
  unfold tailWord_5459346
  simp only [CollatzResearch.WordTrace]
  refine ⟨49779676719932324727795473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132745804586486199274121261 49779676719932324727795473)
  ·
    refine ⟨37334757539949243545846605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49779676719932324727795473 37334757539949243545846605)
    ·
      refine ⟨14000534077480966329692477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37334757539949243545846605 14000534077480966329692477)
      ·
        refine ⟨5250200279055362373634679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14000534077480966329692477 5250200279055362373634679)
        ·
          refine ⟨7875300418583043560452019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5250200279055362373634679 7875300418583043560452019)
          ·
            refine ⟨11812950627874565340678029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7875300418583043560452019 11812950627874565340678029)
            ·
              refine ⟨4429856485452962002754261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11812950627874565340678029 4429856485452962002754261)
              ·
                refine ⟨103824761377803796939553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4429856485452962002754261 103824761377803796939553)
                ·
                  rfl

theorem cell23_5459346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 7].length) (baseStart_5459346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459346 prefixEnd_5459346 := by exact prefixLift 5459346
  have htrace : WordTrace (prefixWord ++ tailWord_5459346) baseStart_5459346 baseEnd_5459346 := by
    simpa [prefixWord, tailWord_5459346, baseEnd_5459346] using wordTrace_append hprefix tailTrace_5459346
  have hstable : (prefixWord ++ tailWord_5459346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459346).length < 2 ^ (prefixWord ++ tailWord_5459346).sum := by decide
  have hdescent : baseEnd_5459346 < baseStart_5459346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459349 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 3, 3, 2]
def baseStart_5459349 : Nat := 118140960795 + 5459349 * 2 ^ 59
def prefixEnd_5459349 : Nat := 4983230072969 + 3 ^ 40 * 5459349 * 2
def baseEnd_5459349 : Nat := 2803270097642666005630417

theorem tailTrace_5459349 : CollatzResearch.WordTrace tailWord_5459349 prefixEnd_5459349 2803270097642666005630417 := by
  unfold tailWord_5459349
  simp only [CollatzResearch.WordTrace]
  refine ⟨199118816298718430423541101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132745877532478953615694067 199118816298718430423541101)
  ·
    refine ⟨74669556112019411408827913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199118816298718430423541101 74669556112019411408827913)
    ·
      refine ⟨56002167084014558556620935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74669556112019411408827913 56002167084014558556620935)
      ·
        refine ⟨84003250626021837834931403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56002167084014558556620935 84003250626021837834931403)
        ·
          refine ⟨126004875939032756752397105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84003250626021837834931403 126004875939032756752397105)
          ·
            refine ⟨94503656954274567564297829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126004875939032756752397105 94503656954274567564297829)
            ·
              refine ⟨17719435678926481418305843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94503656954274567564297829 17719435678926481418305843)
              ·
                refine ⟨26579153518389722127458765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17719435678926481418305843 26579153518389722127458765)
                ·
                  refine ⟨9967182569396145797797037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26579153518389722127458765 9967182569396145797797037)
                  ·
                    refine ⟨3737693463523554674173889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9967182569396145797797037 3737693463523554674173889)
                    ·
                      refine ⟨2803270097642666005630417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3737693463523554674173889 2803270097642666005630417)
                      ·
                        rfl

theorem cell23_5459349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_5459349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459349 prefixEnd_5459349 := by exact prefixLift 5459349
  have htrace : WordTrace (prefixWord ++ tailWord_5459349) baseStart_5459349 baseEnd_5459349 := by
    simpa [prefixWord, tailWord_5459349, baseEnd_5459349] using wordTrace_append hprefix tailTrace_5459349
  have hstable : (prefixWord ++ tailWord_5459349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459349).length < 2 ^ (prefixWord ++ tailWord_5459349).sum := by decide
  have hdescent : baseEnd_5459349 < baseStart_5459349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459373 : List Nat := [1, 5, 2, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_5459373 : Nat := 118140960795 + 5459373 * 2 ^ 59
def prefixEnd_5459373 : Nat := 4983230072969 + 3 ^ 40 * 5459373 * 2
def baseEnd_5459373 : Nat := 2803282421178373911730307

theorem tailTrace_5459373 : CollatzResearch.WordTrace tailWord_5459373 prefixEnd_5459373 2803282421178373911730307 := by
  unfold tailWord_5459373
  simp only [CollatzResearch.WordTrace]
  refine ⟨199119691650631482522414773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132746461100420988348276515 199119691650631482522414773)
  ·
    refine ⟨18667471092246701486476385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199119691650631482522414773 18667471092246701486476385)
    ·
      refine ⟨14000603319185026114857289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18667471092246701486476385 14000603319185026114857289)
      ·
        refine ⟨10500452489388769586142967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14000603319185026114857289 10500452489388769586142967)
        ·
          refine ⟨15750678734083154379214451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10500452489388769586142967 15750678734083154379214451)
          ·
            refine ⟨23626018101124731568821677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15750678734083154379214451 23626018101124731568821677)
            ·
              refine ⟨8859756787921774338308129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23626018101124731568821677 8859756787921774338308129)
              ·
                refine ⟨6644817590941330753731097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8859756787921774338308129 6644817590941330753731097)
                ·
                  refine ⟨4983613193205998065298323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6644817590941330753731097 4983613193205998065298323)
                  ·
                    refine ⟨7475419789808997097947485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4983613193205998065298323 7475419789808997097947485)
                    ·
                      refine ⟨2803282421178373911730307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7475419789808997097947485 2803282421178373911730307)
                      ·
                        rfl

theorem cell23_5459373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_5459373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459373 prefixEnd_5459373 := by exact prefixLift 5459373
  have htrace : WordTrace (prefixWord ++ tailWord_5459373) baseStart_5459373 baseEnd_5459373 := by
    simpa [prefixWord, tailWord_5459373, baseEnd_5459373] using wordTrace_append hprefix tailTrace_5459373
  have hstable : (prefixWord ++ tailWord_5459373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459373).length < 2 ^ (prefixWord ++ tailWord_5459373).sum := by decide
  have hdescent : baseEnd_5459373 < baseStart_5459373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459392 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 4]
def baseStart_5459392 : Nat := 118140960795 + 5459392 * 2 ^ 59
def prefixEnd_5459392 : Nat := 4983230072969 + 3 ^ 40 * 5459392 * 2
def baseEnd_5459392 : Nat := 2803292177310809337392719

theorem tailTrace_5459392 : CollatzResearch.WordTrace tailWord_5459392 prefixEnd_5459392 2803292177310809337392719 := by
  unfold tailWord_5459392
  simp only [CollatzResearch.WordTrace]
  refine ⟨99560192318781324383678215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132746923091708432511570953 99560192318781324383678215)
  ·
    refine ⟨149340288478171986575517323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99560192318781324383678215 149340288478171986575517323)
    ·
      refine ⟨224010432717257979863275985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149340288478171986575517323 224010432717257979863275985)
      ·
        refine ⟨168007824537943484897456989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224010432717257979863275985 168007824537943484897456989)
        ·
          refine ⟨63002934201728806836546371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168007824537943484897456989 63002934201728806836546371)
          ·
            refine ⟨94504401302593210254819557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63002934201728806836546371 94504401302593210254819557)
            ·
              refine ⟨17719575244236226922778667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94504401302593210254819557 17719575244236226922778667)
              ·
                refine ⟨26579362866354340384168001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17719575244236226922778667 26579362866354340384168001)
                ·
                  refine ⟨19934522149765755288126001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26579362866354340384168001 19934522149765755288126001)
                  ·
                    refine ⟨14950891612324316466094501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19934522149765755288126001 14950891612324316466094501)
                    ·
                      refine ⟨2803292177310809337392719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14950891612324316466094501 2803292177310809337392719)
                      ·
                        rfl

theorem cell23_5459392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_5459392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459392 prefixEnd_5459392 := by exact prefixLift 5459392
  have htrace : WordTrace (prefixWord ++ tailWord_5459392) baseStart_5459392 baseEnd_5459392 := by
    simpa [prefixWord, tailWord_5459392, baseEnd_5459392] using wordTrace_append hprefix tailTrace_5459392
  have hstable : (prefixWord ++ tailWord_5459392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459392).length < 2 ^ (prefixWord ++ tailWord_5459392).sum := by decide
  have hdescent : baseEnd_5459392 < baseStart_5459392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459402 : List Nat := [3, 1, 2, 1, 2, 3, 2, 2, 7]
def baseStart_5459402 : Nat := 118140960795 + 5459402 * 2 ^ 59
def prefixEnd_5459402 : Nat := 4983230072969 + 3 ^ 40 * 5459402 * 2
def baseEnd_5459402 : Nat := 311477479124150477585297

theorem tailTrace_5459402 : CollatzResearch.WordTrace tailWord_5459402 prefixEnd_5459402 311477479124150477585297 := by
  unfold tailWord_5459402
  simp only [CollatzResearch.WordTrace]
  refine ⟨49780187341881605118805115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132747166245017613650146973 49780187341881605118805115)
  ·
    refine ⟨74670281012822407678207673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49780187341881605118805115 74670281012822407678207673)
    ·
      refine ⟨56002710759616805758655755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74670281012822407678207673 56002710759616805758655755)
      ·
        refine ⟨84004066139425208637983633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56002710759616805758655755 84004066139425208637983633)
        ·
          refine ⟨63003049604568906478487725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84004066139425208637983633 63003049604568906478487725)
          ·
            refine ⟨23626143601713339929432897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63003049604568906478487725 23626143601713339929432897)
            ·
              refine ⟨17719607701285004947074673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23626143601713339929432897 17719607701285004947074673)
              ·
                refine ⟨13289705775963753710306005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17719607701285004947074673 13289705775963753710306005)
                ·
                  refine ⟨311477479124150477585297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13289705775963753710306005 311477479124150477585297)
                  ·
                    rfl

theorem cell23_5459402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 2, 2, 7].length) (baseStart_5459402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459402 prefixEnd_5459402 := by exact prefixLift 5459402
  have htrace : WordTrace (prefixWord ++ tailWord_5459402) baseStart_5459402 baseEnd_5459402 := by
    simpa [prefixWord, tailWord_5459402, baseEnd_5459402] using wordTrace_append hprefix tailTrace_5459402
  have hstable : (prefixWord ++ tailWord_5459402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459402).length < 2 ^ (prefixWord ++ tailWord_5459402).sum := by decide
  have hdescent : baseEnd_5459402 < baseStart_5459402 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459452 : List Nat := [2, 2, 2, 1, 2, 1, 2, 1, 3, 3, 4]
def baseStart_5459452 : Nat := 118140960795 + 5459452 * 2 ^ 59
def prefixEnd_5459452 : Nat := 4983230072969 + 3 ^ 40 * 5459452 * 2
def baseEnd_5459452 : Nat := 2803322986150079102642443

theorem tailTrace_5459452 : CollatzResearch.WordTrace tailWord_5459452 prefixEnd_5459452 2803322986150079102642443 := by
  unfold tailWord_5459452
  simp only [CollatzResearch.WordTrace]
  refine ⟨99561286508672639507270305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132748382011563519343027073 99561286508672639507270305)
  ·
    refine ⟨74670964881504479630452729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99561286508672639507270305 74670964881504479630452729)
    ·
      refine ⟨56003223661128359722839547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74670964881504479630452729 56003223661128359722839547)
      ·
        refine ⟨84004835491692539584259321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56003223661128359722839547 84004835491692539584259321)
        ·
          refine ⟨63003626618769404688194491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84004835491692539584259321 63003626618769404688194491)
          ·
            refine ⟨94505439928154107032291737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63003626618769404688194491 94505439928154107032291737)
            ·
              refine ⟨70879079946115580274218803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94505439928154107032291737 70879079946115580274218803)
              ·
                refine ⟨106318619919173370411328205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70879079946115580274218803 106318619919173370411328205)
                ·
                  refine ⟨39869482469690013904248077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106318619919173370411328205 39869482469690013904248077)
                  ·
                    refine ⟨14951055926133755214093029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39869482469690013904248077 14951055926133755214093029)
                    ·
                      refine ⟨2803322986150079102642443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14951055926133755214093029 2803322986150079102642443)
                      ·
                        rfl

theorem cell23_5459452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_5459452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459452 prefixEnd_5459452 := by exact prefixLift 5459452
  have htrace : WordTrace (prefixWord ++ tailWord_5459452) baseStart_5459452 baseEnd_5459452 := by
    simpa [prefixWord, tailWord_5459452, baseEnd_5459452] using wordTrace_append hprefix tailTrace_5459452
  have hstable : (prefixWord ++ tailWord_5459452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459452).length < 2 ^ (prefixWord ++ tailWord_5459452).sum := by decide
  have hdescent : baseEnd_5459452 < baseStart_5459452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459482 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_5459482 : Nat := 118140960795 + 5459482 * 2 ^ 59
def prefixEnd_5459482 : Nat := 4983230072969 + 3 ^ 40 * 5459482 * 2
def baseEnd_5459482 : Nat := 2803338390569713985267305

theorem tailTrace_5459482 : CollatzResearch.WordTrace tailWord_5459482 prefixEnd_5459482 2803338390569713985267305 := by
  unfold tailWord_5459482
  simp only [CollatzResearch.WordTrace]
  refine ⟨49780916801809148534533175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132749111471491062758755133 49780916801809148534533175)
  ·
    refine ⟨74671375202713722801799763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49780916801809148534533175 74671375202713722801799763)
    ·
      refine ⟨112007062804070584202699645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74671375202713722801799763 112007062804070584202699645)
      ·
        refine ⟨42002648551526469076012367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112007062804070584202699645 42002648551526469076012367)
        ·
          refine ⟨63003972827289703614018551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42002648551526469076012367 63003972827289703614018551)
          ·
            refine ⟨94505959240934555421027827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63003972827289703614018551 94505959240934555421027827)
            ·
              refine ⟨141758938861401833131541741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94505959240934555421027827 141758938861401833131541741)
              ·
                refine ⟨53159602073025687424328153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141758938861401833131541741 53159602073025687424328153)
                ·
                  refine ⟨39869701554769265568246115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53159602073025687424328153 39869701554769265568246115)
                  ·
                    refine ⟨59804552332153898352369173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39869701554769265568246115 59804552332153898352369173)
                    ·
                      refine ⟨2803338390569713985267305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59804552332153898352369173 2803338390569713985267305)
                      ·
                        rfl

theorem cell23_5459482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_5459482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459482 prefixEnd_5459482 := by exact prefixLift 5459482
  have htrace : WordTrace (prefixWord ++ tailWord_5459482) baseStart_5459482 baseEnd_5459482 := by
    simpa [prefixWord, tailWord_5459482, baseEnd_5459482] using wordTrace_append hprefix tailTrace_5459482
  have hstable : (prefixWord ++ tailWord_5459482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459482).length < 2 ^ (prefixWord ++ tailWord_5459482).sum := by decide
  have hdescent : baseEnd_5459482 < baseStart_5459482 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459509 : List Nat := [1, 3, 3, 1, 1, 3, 2, 3, 6]
def baseStart_5459509 : Nat := 118140960795 + 5459509 * 2 ^ 59
def prefixEnd_5459509 : Nat := 4983230072969 + 3 ^ 40 * 5459509 * 2
def baseEnd_5459509 : Nat := 311483583838598375514409

theorem tailTrace_5459509 : CollatzResearch.WordTrace tailWord_5459509 prefixEnd_5459509 311483583838598375514409 := by
  unfold tailWord_5459509
  simp only [CollatzResearch.WordTrace]
  refine ⟨199124651978138777749365581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132749767985425851832910387 199124651978138777749365581)
  ·
    refine ⟨74671744491802041656012093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199124651978138777749365581 74671744491802041656012093)
    ·
      refine ⟨28001904184425765621004535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74671744491802041656012093 28001904184425765621004535)
      ·
        refine ⟨42002856276638648431506803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28001904184425765621004535 42002856276638648431506803)
        ·
          refine ⟨63004284414957972647260205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42002856276638648431506803 63004284414957972647260205)
          ·
            refine ⟨23626606655609239742722577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63004284414957972647260205 23626606655609239742722577)
            ·
              refine ⟨17719954991706929807041933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23626606655609239742722577 17719954991706929807041933)
              ·
                refine ⟨6644983121890098677640725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17719954991706929807041933 6644983121890098677640725)
                ·
                  refine ⟨311483583838598375514409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6644983121890098677640725 311483583838598375514409)
                  ·
                    rfl

theorem cell23_5459509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 2, 3, 6].length) (baseStart_5459509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459509 prefixEnd_5459509 := by exact prefixLift 5459509
  have htrace : WordTrace (prefixWord ++ tailWord_5459509) baseStart_5459509 baseEnd_5459509 := by
    simpa [prefixWord, tailWord_5459509, baseEnd_5459509] using wordTrace_append hprefix tailTrace_5459509
  have hstable : (prefixWord ++ tailWord_5459509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459509).length < 2 ^ (prefixWord ++ tailWord_5459509).sum := by decide
  have hdescent : baseEnd_5459509 < baseStart_5459509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459546 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2]
def baseStart_5459546 : Nat := 118140960795 + 5459546 * 2 ^ 59
def prefixEnd_5459546 : Nat := 4983230072969 + 3 ^ 40 * 5459546 * 2
def baseEnd_5459546 : Nat := 2803371253331601734867011

theorem tailTrace_5459546 : CollatzResearch.WordTrace tailWord_5459546 prefixEnd_5459546 2803371253331601734867011 := by
  unfold tailWord_5459546
  simp only [CollatzResearch.WordTrace]
  refine ⟨49781500369751183267115623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132750667652669822045641661 49781500369751183267115623)
  ·
    refine ⟨74672250554626774900673435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49781500369751183267115623 74672250554626774900673435)
    ·
      refine ⟨112008375831940162351010153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74672250554626774900673435 112008375831940162351010153)
      ·
        refine ⟨84006281873955121763257615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112008375831940162351010153 84006281873955121763257615)
        ·
          refine ⟨126009422810932682644886423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84006281873955121763257615 126009422810932682644886423)
          ·
            refine ⟨189014134216399023967329635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126009422810932682644886423 189014134216399023967329635)
            ·
              refine ⟨283521201324598535950994453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189014134216399023967329635 283521201324598535950994453)
              ·
                refine ⟨13290056312090556372702865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 283521201324598535950994453 13290056312090556372702865)
                ·
                  refine ⟨9967542234067917279527149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13290056312090556372702865 9967542234067917279527149)
                  ·
                    refine ⟨3737828337775468979822681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9967542234067917279527149 3737828337775468979822681)
                    ·
                      refine ⟨2803371253331601734867011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3737828337775468979822681 2803371253331601734867011)
                      ·
                        rfl

theorem cell23_5459546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_5459546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459546 prefixEnd_5459546 := by exact prefixLift 5459546
  have htrace : WordTrace (prefixWord ++ tailWord_5459546) baseStart_5459546 baseEnd_5459546 := by
    simpa [prefixWord, tailWord_5459546, baseEnd_5459546] using wordTrace_append hprefix tailTrace_5459546
  have hstable : (prefixWord ++ tailWord_5459546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459546).length < 2 ^ (prefixWord ++ tailWord_5459546).sum := by decide
  have hdescent : baseEnd_5459546 < baseStart_5459546 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459553 : List Nat := [1, 2, 3, 1, 1, 3, 1, 6, 1, 1, 3]
def baseStart_5459553 : Nat := 118140960795 + 5459553 * 2 ^ 59
def prefixEnd_5459553 : Nat := 4983230072969 + 3 ^ 40 * 5459553 * 2
def baseEnd_5459553 : Nat := 2803374847696183207479479

theorem tailTrace_5459553 : CollatzResearch.WordTrace tailWord_5459553 prefixEnd_5459553 2803374847696183207479479 := by
  unfold tailWord_5459553
  simp only [CollatzResearch.WordTrace]
  refine ⟨199126256789979373263967313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132750837859986248842644875 199126256789979373263967313)
  ·
    refine ⟨149344692592484529947975485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199126256789979373263967313 149344692592484529947975485)
    ·
      refine ⟨56004259722181698730490807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149344692592484529947975485 56004259722181698730490807)
      ·
        refine ⟨84006389583272548095736211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56004259722181698730490807 84006389583272548095736211)
        ·
          refine ⟨126009584374908822143604317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84006389583272548095736211 126009584374908822143604317)
          ·
            refine ⟨47253594140590808303851619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126009584374908822143604317 47253594140590808303851619)
            ·
              refine ⟨70880391210886212455777429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47253594140590808303851619 70880391210886212455777429)
              ·
                refine ⟨3322518338010291208864567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70880391210886212455777429 3322518338010291208864567)
                ·
                  refine ⟨4983777507015436813296851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3322518338010291208864567 4983777507015436813296851)
                  ·
                    refine ⟨7475666260523155219945277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4983777507015436813296851 7475666260523155219945277)
                    ·
                      refine ⟨2803374847696183207479479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7475666260523155219945277 2803374847696183207479479)
                      ·
                        rfl

theorem cell23_5459553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 6, 1, 1, 3].length) (baseStart_5459553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459553 prefixEnd_5459553 := by exact prefixLift 5459553
  have htrace : WordTrace (prefixWord ++ tailWord_5459553) baseStart_5459553 baseEnd_5459553 := by
    simpa [prefixWord, tailWord_5459553, baseEnd_5459553] using wordTrace_append hprefix tailTrace_5459553
  have hstable : (prefixWord ++ tailWord_5459553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459553).length < 2 ^ (prefixWord ++ tailWord_5459553).sum := by decide
  have hdescent : baseEnd_5459553 < baseStart_5459553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459559 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_5459559 : Nat := 118140960795 + 5459559 * 2 ^ 59
def prefixEnd_5459559 : Nat := 4983230072969 + 3 ^ 40 * 5459559 * 2
def baseEnd_5459559 : Nat := 2803377928580110184004451

theorem tailTrace_5459559 : CollatzResearch.WordTrace tailWord_5459559 prefixEnd_5459559 2803377928580110184004451 := by
  unfold tailWord_5459559
  simp only [CollatzResearch.WordTrace]
  refine ⟨199126475627957636288685731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132750983751971757525790487 199126475627957636288685731)
  ·
    refine ⟨298689713441936454433028597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199126475627957636288685731 298689713441936454433028597)
    ·
      refine ⟨28002160635181542603096431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 298689713441936454433028597 28002160635181542603096431)
      ·
        refine ⟨42003240952772313904644647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28002160635181542603096431 42003240952772313904644647)
        ·
          refine ⟨63004861429158470856966971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42003240952772313904644647 63004861429158470856966971)
          ·
            refine ⟨94507292143737706285450457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63004861429158470856966971 94507292143737706285450457)
            ·
              refine ⟨70880469107803279714087843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94507292143737706285450457 70880469107803279714087843)
              ·
                refine ⟨106320703661704919571131765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70880469107803279714087843 106320703661704919571131765)
                ·
                  refine ⟨9967565968284836209793603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106320703661704919571131765 9967565968284836209793603)
                  ·
                    refine ⟨14951348952427254314690405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9967565968284836209793603 14951348952427254314690405)
                    ·
                      refine ⟨2803377928580110184004451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14951348952427254314690405 2803377928580110184004451)
                      ·
                        rfl

theorem cell23_5459559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_5459559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459559 prefixEnd_5459559 := by exact prefixLift 5459559
  have htrace : WordTrace (prefixWord ++ tailWord_5459559) baseStart_5459559 baseEnd_5459559 := by
    simpa [prefixWord, tailWord_5459559, baseEnd_5459559] using wordTrace_append hprefix tailTrace_5459559
  have hstable : (prefixWord ++ tailWord_5459559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459559).length < 2 ^ (prefixWord ++ tailWord_5459559).sum := by decide
  have hdescent : baseEnd_5459559 < baseStart_5459559 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459573 : List Nat := [1, 3, 4, 2, 1, 2, 2, 2, 1, 5]
def baseStart_5459573 : Nat := 118140960795 + 5459573 * 2 ^ 59
def prefixEnd_5459573 : Nat := 4983230072969 + 3 ^ 40 * 5459573 * 2
def baseEnd_5459573 : Nat := 934461705769757709743129

theorem tailTrace_5459573 : CollatzResearch.WordTrace tailWord_5459573 prefixEnd_5459573 934461705769757709743129 := by
  unfold tailWord_5459573
  simp only [CollatzResearch.WordTrace]
  refine ⟨199126986249906916679695373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132751324166604611119796915 199126986249906916679695373)
  ·
    refine ⟨74672619843715093754885765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199126986249906916679695373 74672619843715093754885765)
    ·
      refine ⟨14001116220696580079041081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74672619843715093754885765 14001116220696580079041081)
      ·
        refine ⟨10500837165522435059280811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14001116220696580079041081 10500837165522435059280811)
        ·
          refine ⟨15751255748283652588921217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10500837165522435059280811 15751255748283652588921217)
          ·
            refine ⟨11813441811212739441690913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15751255748283652588921217 11813441811212739441690913)
            ·
              refine ⟨8860081358409554581268185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11813441811212739441690913 8860081358409554581268185)
              ·
                refine ⟨6645061018807165935951139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8860081358409554581268185 6645061018807165935951139)
                ·
                  refine ⟨9967591528210748903926709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6645061018807165935951139 9967591528210748903926709)
                  ·
                    refine ⟨934461705769757709743129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9967591528210748903926709 934461705769757709743129)
                    ·
                      rfl

theorem cell23_5459573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_5459573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459573 prefixEnd_5459573 := by exact prefixLift 5459573
  have htrace : WordTrace (prefixWord ++ tailWord_5459573) baseStart_5459573 baseEnd_5459573 := by
    simpa [prefixWord, tailWord_5459573, baseEnd_5459573] using wordTrace_append hprefix tailTrace_5459573
  have hstable : (prefixWord ++ tailWord_5459573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459573).length < 2 ^ (prefixWord ++ tailWord_5459573).sum := by decide
  have hdescent : baseEnd_5459573 < baseStart_5459573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459589 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_5459589 : Nat := 118140960795 + 5459589 * 2 ^ 59
def prefixEnd_5459589 : Nat := 4983230072969 + 3 ^ 40 * 5459589 * 2
def baseEnd_5459589 : Nat := 2803393332999745066629313

theorem tailTrace_5459589 : CollatzResearch.WordTrace tailWord_5459589 prefixEnd_5459589 2803393332999745066629313 := by
  unfold tailWord_5459589
  simp only [CollatzResearch.WordTrace]
  refine ⟨199127569817848951412277821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132751713211899300941518547 199127569817848951412277821)
  ·
    refine ⟨74672838681693356779604183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199127569817848951412277821 74672838681693356779604183)
    ·
      refine ⟨112009258022540035169406275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74672838681693356779604183 112009258022540035169406275)
      ·
        refine ⟨168013887033810052754109413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112009258022540035169406275 168013887033810052754109413)
        ·
          refine ⟨31502603818839384891395515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168013887033810052754109413 31502603818839384891395515)
          ·
            refine ⟨47253905728259077337093273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31502603818839384891395515 47253905728259077337093273)
            ·
              refine ⟨35440429296194308002819955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47253905728259077337093273 35440429296194308002819955)
              ·
                refine ⟨53160643944291462004229933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35440429296194308002819955 53160643944291462004229933)
                ·
                  refine ⟨19935241479109298251586225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53160643944291462004229933 19935241479109298251586225)
                  ·
                    refine ⟨14951431109331973688689669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19935241479109298251586225 14951431109331973688689669)
                    ·
                      refine ⟨2803393332999745066629313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14951431109331973688689669 2803393332999745066629313)
                      ·
                        rfl

theorem cell23_5459589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_5459589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459589 prefixEnd_5459589 := by exact prefixLift 5459589
  have htrace : WordTrace (prefixWord ++ tailWord_5459589) baseStart_5459589 baseEnd_5459589 := by
    simpa [prefixWord, tailWord_5459589, baseEnd_5459589] using wordTrace_append hprefix tailTrace_5459589
  have hstable : (prefixWord ++ tailWord_5459589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459589).length < 2 ^ (prefixWord ++ tailWord_5459589).sum := by decide
  have hdescent : baseEnd_5459589 < baseStart_5459589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459596 : List Nat := [2, 2, 1, 2, 1, 1, 3, 5, 1, 2, 3]
def baseStart_5459596 : Nat := 118140960795 + 5459596 * 2 ^ 59
def prefixEnd_5459596 : Nat := 4983230072969 + 3 ^ 40 * 5459596 * 2
def baseEnd_5459596 : Nat := 2803396927364326539241781

theorem tailTrace_5459596 : CollatzResearch.WordTrace tailWord_5459596 prefixEnd_5459596 2803396927364326539241781 := by
  unfold tailWord_5459596
  simp only [CollatzResearch.WordTrace]
  refine ⟨99563912564411795803891321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132751883419215727738521761 99563912564411795803891321)
  ·
    refine ⟨74672934423308846852918491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99563912564411795803891321 74672934423308846852918491)
    ·
      refine ⟨112009401634963270279377737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74672934423308846852918491 112009401634963270279377737)
      ·
        refine ⟨84007051226222452709533303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112009401634963270279377737 84007051226222452709533303)
        ·
          refine ⟨126010576839333679064299955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84007051226222452709533303 126010576839333679064299955)
          ·
            refine ⟨189015865259000518596449933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126010576839333679064299955 189015865259000518596449933)
            ·
              refine ⟨70880949472125194473668725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189015865259000518596449933 70880949472125194473668725)
              ·
                refine ⟨6645089013011736981906443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70880949472125194473668725 6645089013011736981906443)
                ·
                  refine ⟨9967633519517605472859665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6645089013011736981906443 9967633519517605472859665)
                  ·
                    refine ⟨7475725139638204104644749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9967633519517605472859665 7475725139638204104644749)
                    ·
                      refine ⟨2803396927364326539241781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7475725139638204104644749 2803396927364326539241781)
                      ·
                        rfl

theorem cell23_5459596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 5, 1, 2, 3].length) (baseStart_5459596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459596 prefixEnd_5459596 := by exact prefixLift 5459596
  have htrace : WordTrace (prefixWord ++ tailWord_5459596) baseStart_5459596 baseEnd_5459596 := by
    simpa [prefixWord, tailWord_5459596, baseEnd_5459596] using wordTrace_append hprefix tailTrace_5459596
  have hstable : (prefixWord ++ tailWord_5459596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459596).length < 2 ^ (prefixWord ++ tailWord_5459596).sum := by decide
  have hdescent : baseEnd_5459596 < baseStart_5459596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459604 : List Nat := [2, 4, 2, 2, 2, 1, 3, 2, 1, 1, 3]
def baseStart_5459604 : Nat := 118140960795 + 5459604 * 2 ^ 59
def prefixEnd_5459604 : Nat := 4983230072969 + 3 ^ 40 * 5459604 * 2
def baseEnd_5459604 : Nat := 2803401035209562507941745

theorem tailTrace_5459604 : CollatzResearch.WordTrace tailWord_5459604 prefixEnd_5459604 2803401035209562507941745 := by
  unfold tailWord_5459604
  simp only [CollatzResearch.WordTrace]
  refine ⟨99564058456397304487036933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132752077941863072649382577 99564058456397304487036933)
  ·
    refine ⟨18668260960574494591319425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99564058456397304487036933 18668260960574494591319425)
    ·
      refine ⟨14001195720430870943489569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18668260960574494591319425 14001195720430870943489569)
      ·
        refine ⟨10500896790323153207617177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14001195720430870943489569 10500896790323153207617177)
        ·
          refine ⟨7875672592742364905712883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10500896790323153207617177 7875672592742364905712883)
          ·
            refine ⟨11813508889113547358569325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7875672592742364905712883 11813508889113547358569325)
            ·
              refine ⟨4430065833417580259463497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11813508889113547358569325 4430065833417580259463497)
              ·
                refine ⟨3322549375063185194597623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4430065833417580259463497 3322549375063185194597623)
                ·
                  refine ⟨4983824062594777791896435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3322549375063185194597623 4983824062594777791896435)
                  ·
                    refine ⟨7475736093892166687844653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4983824062594777791896435 7475736093892166687844653)
                    ·
                      refine ⟨2803401035209562507941745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7475736093892166687844653 2803401035209562507941745)
                      ·
                        rfl

theorem cell23_5459604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_5459604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459604 prefixEnd_5459604 := by exact prefixLift 5459604
  have htrace : WordTrace (prefixWord ++ tailWord_5459604) baseStart_5459604 baseEnd_5459604 := by
    simpa [prefixWord, tailWord_5459604, baseEnd_5459604] using wordTrace_append hprefix tailTrace_5459604
  have hstable : (prefixWord ++ tailWord_5459604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459604).length < 2 ^ (prefixWord ++ tailWord_5459604).sum := by decide
  have hdescent : baseEnd_5459604 < baseStart_5459604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459609 : List Nat := [1, 2, 1, 2, 1, 2, 2, 1, 5, 3, 3]
def baseStart_5459609 : Nat := 118140960795 + 5459609 * 2 ^ 59
def prefixEnd_5459609 : Nat := 4983230072969 + 3 ^ 40 * 5459609 * 2
def baseEnd_5459609 : Nat := 2803403602612834988379221

theorem tailTrace_5459609 : CollatzResearch.WordTrace tailWord_5459609 prefixEnd_5459609 2803403602612834988379221 := by
  unfold tailWord_5459609
  simp only [CollatzResearch.WordTrace]
  refine ⟨199128299277776494828005881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132752199518517663218670587 199128299277776494828005881)
  ·
    refine ⟨149346224458332371121004411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199128299277776494828005881 149346224458332371121004411)
    ·
      refine ⟨224019336687498556681506617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149346224458332371121004411 224019336687498556681506617)
      ·
        refine ⟨168014502515623917511129963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224019336687498556681506617 168014502515623917511129963)
        ·
          refine ⟨252021753773435876266694945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168014502515623917511129963 252021753773435876266694945)
          ·
            refine ⟨189016315330076907200021209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252021753773435876266694945 189016315330076907200021209)
            ·
              refine ⟨141762236497557680400015907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189016315330076907200021209 141762236497557680400015907)
              ·
                refine ⟨212643354746336520600023861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141762236497557680400015907 212643354746336520600023861)
                ·
                  refine ⟨19935314507469048806252237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 212643354746336520600023861 19935314507469048806252237)
                  ·
                    refine ⟨7475742940300893302344589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19935314507469048806252237 7475742940300893302344589)
                    ·
                      refine ⟨2803403602612834988379221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7475742940300893302344589 2803403602612834988379221)
                      ·
                        rfl

theorem cell23_5459609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_5459609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459609 prefixEnd_5459609 := by exact prefixLift 5459609
  have htrace : WordTrace (prefixWord ++ tailWord_5459609) baseStart_5459609 baseEnd_5459609 := by
    simpa [prefixWord, tailWord_5459609, baseEnd_5459609] using wordTrace_append hprefix tailTrace_5459609
  have hstable : (prefixWord ++ tailWord_5459609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459609).length < 2 ^ (prefixWord ++ tailWord_5459609).sum := by decide
  have hdescent : baseEnd_5459609 < baseStart_5459609 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459620 : List Nat := [2, 3, 1, 2, 2, 4, 2, 1, 2, 4]
def baseStart_5459620 : Nat := 118140960795 + 5459620 * 2 ^ 59
def prefixEnd_5459620 : Nat := 4983230072969 + 3 ^ 40 * 5459620 * 2
def baseEnd_5459620 : Nat := 934469750300011481780557

theorem tailTrace_5459620 : CollatzResearch.WordTrace tailWord_5459620 prefixEnd_5459620 934469750300011481780557 := by
  unfold tailWord_5459620
  simp only [CollatzResearch.WordTrace]
  refine ⟨99564350240368321853328157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132752466987157762471104209 99564350240368321853328157)
  ·
    refine ⟨37336631340138120694998059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99564350240368321853328157 37336631340138120694998059)
    ·
      refine ⟨56004947010207181042497089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37336631340138120694998059 56004947010207181042497089)
      ·
        refine ⟨42003710257655385781872817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56004947010207181042497089 42003710257655385781872817)
        ·
          refine ⟨31502782693241539336404613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42003710257655385781872817 31502782693241539336404613)
          ·
            refine ⟨5906771754982788625575865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31502782693241539336404613 5906771754982788625575865)
            ·
              refine ⟨4430078816237091469181899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5906771754982788625575865 4430078816237091469181899)
              ·
                refine ⟨6645118224355637203772849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4430078816237091469181899 6645118224355637203772849)
                ·
                  refine ⟨4983838668266727902829637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6645118224355637203772849 4983838668266727902829637)
                  ·
                    refine ⟨934469750300011481780557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4983838668266727902829637 934469750300011481780557)
                    ·
                      rfl

theorem cell23_5459620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_5459620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459620 prefixEnd_5459620 := by exact prefixLift 5459620
  have htrace : WordTrace (prefixWord ++ tailWord_5459620) baseStart_5459620 baseEnd_5459620 := by
    simpa [prefixWord, tailWord_5459620, baseEnd_5459620] using wordTrace_append hprefix tailTrace_5459620
  have hstable : (prefixWord ++ tailWord_5459620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459620).length < 2 ^ (prefixWord ++ tailWord_5459620).sum := by decide
  have hdescent : baseEnd_5459620 < baseStart_5459620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459624 : List Nat := [2, 1, 7, 1, 2, 1, 1, 2, 1, 5]
def baseStart_5459624 : Nat := 118140960795 + 5459624 * 2 ^ 59
def prefixEnd_5459624 : Nat := 4983230072969 + 3 ^ 40 * 5459624 * 2
def baseEnd_5459624 : Nat := 934470434940884143230551

theorem tailTrace_5459624 : CollatzResearch.WordTrace tailWord_5459624 prefixEnd_5459624 934470434940884143230551 := by
  unfold tailWord_5459624
  simp only [CollatzResearch.WordTrace]
  refine ⟨99564423186361076194900963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132752564248481434926534617 99564423186361076194900963)
  ·
    refine ⟨149346634779541614292351445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99564423186361076194900963 149346634779541614292351445)
    ·
      refine ⟨3500311752645506584976987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 149346634779541614292351445 3500311752645506584976987)
      ·
        refine ⟨5250467628968259877465481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3500311752645506584976987 5250467628968259877465481)
        ·
          refine ⟨3937850721726194908099111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5250467628968259877465481 3937850721726194908099111)
          ·
            refine ⟨5906776082589292362148667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3937850721726194908099111 5906776082589292362148667)
            ·
              refine ⟨8860164123883938543223001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5906776082589292362148667 8860164123883938543223001)
              ·
                refine ⟨6645123092912953907417251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8860164123883938543223001 6645123092912953907417251)
                ·
                  refine ⟨9967684639369430861125877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6645123092912953907417251 9967684639369430861125877)
                  ·
                    refine ⟨934470434940884143230551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9967684639369430861125877 934470434940884143230551)
                    ·
                      rfl

theorem cell23_5459624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_5459624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459624 prefixEnd_5459624 := by exact prefixLift 5459624
  have htrace : WordTrace (prefixWord ++ tailWord_5459624) baseStart_5459624 baseEnd_5459624 := by
    simpa [prefixWord, tailWord_5459624, baseEnd_5459624] using wordTrace_append hprefix tailTrace_5459624
  have hstable : (prefixWord ++ tailWord_5459624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459624).length < 2 ^ (prefixWord ++ tailWord_5459624).sum := by decide
  have hdescent : baseEnd_5459624 < baseStart_5459624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459630 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_5459630 : Nat := 118140960795 + 5459630 * 2 ^ 59
def prefixEnd_5459630 : Nat := 4983230072969 + 3 ^ 40 * 5459630 * 2
def baseEnd_5459630 : Nat := 2803414385706579406216625

theorem tailTrace_5459630 : CollatzResearch.WordTrace tailWord_5459630 prefixEnd_5459630 2803414385706579406216625 := by
  unfold tailWord_5459630
  simp only [CollatzResearch.WordTrace]
  refine ⟨24891133151337551926815043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132752710140466943609680229 24891133151337551926815043)
  ·
    refine ⟨37336699727006327890222565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24891133151337551926815043 37336699727006327890222565)
    ·
      refine ⟨7000631198813686479416731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37336699727006327890222565 7000631198813686479416731)
      ·
        refine ⟨10500946798220529719125097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7000631198813686479416731 10500946798220529719125097)
        ·
          refine ⟨7875710098665397289343823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10500946798220529719125097 7875710098665397289343823)
          ·
            refine ⟨11813565147998095934015735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7875710098665397289343823 11813565147998095934015735)
            ·
              refine ⟨17720347721997143901023603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11813565147998095934015735 17720347721997143901023603)
              ·
                refine ⟨26580521582995715851535405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17720347721997143901023603 26580521582995715851535405)
                ·
                  refine ⟨9967695593623393444325777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26580521582995715851535405 9967695593623393444325777)
                  ·
                    refine ⟨7475771695217545083244333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9967695593623393444325777 7475771695217545083244333)
                    ·
                      refine ⟨2803414385706579406216625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7475771695217545083244333 2803414385706579406216625)
                      ·
                        rfl

theorem cell23_5459630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_5459630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459630 prefixEnd_5459630 := by exact prefixLift 5459630
  have htrace : WordTrace (prefixWord ++ tailWord_5459630) baseStart_5459630 baseEnd_5459630 := by
    simpa [prefixWord, tailWord_5459630, baseEnd_5459630] using wordTrace_append hprefix tailTrace_5459630
  have hstable : (prefixWord ++ tailWord_5459630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459630).length < 2 ^ (prefixWord ++ tailWord_5459630).sum := by decide
  have hdescent : baseEnd_5459630 < baseStart_5459630 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459650 : List Nat := [3, 5, 1, 2, 2, 10]
def baseStart_5459650 : Nat := 118140960795 + 5459650 * 2 ^ 59
def prefixEnd_5459650 : Nat := 4983230072969 + 3 ^ 40 * 5459650 * 2
def baseEnd_5459650 : Nat := 11536726976624153613031

theorem tailTrace_5459650 : CollatzResearch.WordTrace tailWord_5459650 prefixEnd_5459650 11536726976624153613031 := by
  unfold tailWord_5459650
  simp only [CollatzResearch.WordTrace]
  refine ⟨49782448667656989707562101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132753196447085305886832269 49782448667656989707562101)
  ·
    refine ⟨4667104562592842785083947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49782448667656989707562101 4667104562592842785083947)
    ·
      refine ⟨7000656843889264177625921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4667104562592842785083947 7000656843889264177625921)
      ·
        refine ⟨5250492632916948133219441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7000656843889264177625921 5250492632916948133219441)
        ·
          refine ⟨3937869474687711099914581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5250492632916948133219441 3937869474687711099914581)
          ·
            refine ⟨11536726976624153613031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3937869474687711099914581 11536726976624153613031)
            ·
              rfl

theorem cell23_5459650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 10].length) (baseStart_5459650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459650 prefixEnd_5459650 := by exact prefixLift 5459650
  have htrace : WordTrace (prefixWord ++ tailWord_5459650) baseStart_5459650 baseEnd_5459650 := by
    simpa [prefixWord, tailWord_5459650, baseEnd_5459650] using wordTrace_append hprefix tailTrace_5459650
  have hstable : (prefixWord ++ tailWord_5459650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459650).length < 2 ^ (prefixWord ++ tailWord_5459650).sum := by decide
  have hdescent : baseEnd_5459650 < baseStart_5459650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459661 : List Nat := [1, 6, 2, 1, 1, 1, 4, 2, 1, 2, 2]
def baseStart_5459661 : Nat := 118140960795 + 5459661 * 2 ^ 59
def prefixEnd_5459661 : Nat := 4983230072969 + 3 ^ 40 * 5459661 * 2
def baseEnd_5459661 : Nat := 2803430303606868784928983

theorem tailTrace_5459661 : CollatzResearch.WordTrace tailWord_5459661 prefixEnd_5459661 2803430303606868784928983 := by
  unfold tailWord_5459661
  simp only [CollatzResearch.WordTrace]
  refine ⟨199130195873588107708898837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132753463915725405139265891 199130195873588107708898837)
  ·
    refine ⟨9334227931574442548854633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 199130195873588107708898837 9334227931574442548854633)
    ·
      refine ⟨7000670948680831911640975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9334227931574442548854633 7000670948680831911640975)
      ·
        refine ⟨10501006423021247867461463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7000670948680831911640975 10501006423021247867461463)
        ·
          refine ⟨15751509634531871801192195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10501006423021247867461463 15751509634531871801192195)
          ·
            refine ⟨23627264451797807701788293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15751509634531871801192195 23627264451797807701788293)
            ·
              refine ⟨4430112084712088944085305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23627264451797807701788293 4430112084712088944085305)
              ·
                refine ⟨3322584063534066708063979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4430112084712088944085305 3322584063534066708063979)
                ·
                  refine ⟨4983876095301100062095969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3322584063534066708063979 4983876095301100062095969)
                  ·
                    refine ⟨3737907071475825046571977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4983876095301100062095969 3737907071475825046571977)
                    ·
                      refine ⟨2803430303606868784928983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3737907071475825046571977 2803430303606868784928983)
                      ·
                        rfl

theorem cell23_5459661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_5459661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459661 prefixEnd_5459661 := by exact prefixLift 5459661
  have htrace : WordTrace (prefixWord ++ tailWord_5459661) baseStart_5459661 baseEnd_5459661 := by
    simpa [prefixWord, tailWord_5459661, baseEnd_5459661] using wordTrace_append hprefix tailTrace_5459661
  have hstable : (prefixWord ++ tailWord_5459661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459661).length < 2 ^ (prefixWord ++ tailWord_5459661).sum := by decide
  have hdescent : baseEnd_5459661 < baseStart_5459661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459666 : List Nat := [3, 2, 2, 2, 2, 1, 1, 1, 2, 3, 4]
def baseStart_5459666 : Nat := 118140960795 + 5459666 * 2 ^ 59
def prefixEnd_5459666 : Nat := 4983230072969 + 3 ^ 40 * 5459666 * 2
def baseEnd_5459666 : Nat := 2803432871010141265366459

theorem tailTrace_5459666 : CollatzResearch.WordTrace tailWord_5459666 prefixEnd_5459666 2803432871010141265366459 := by
  unfold tailWord_5459666
  simp only [CollatzResearch.WordTrace]
  refine ⟨49782594559642498390707713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132753585492379995708553901 49782594559642498390707713)
  ·
    refine ⟨37336945919731873793030785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49782594559642498390707713 37336945919731873793030785)
    ·
      refine ⟨28002709439798905344773089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37336945919731873793030785 28002709439798905344773089)
      ·
        refine ⟨21002032079849179008579817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28002709439798905344773089 21002032079849179008579817)
        ·
          refine ⟨15751524059886884256434863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21002032079849179008579817 15751524059886884256434863)
          ·
            refine ⟨23627286089830326384652295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15751524059886884256434863 23627286089830326384652295)
            ·
              refine ⟨35440929134745489576978443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23627286089830326384652295 35440929134745489576978443)
              ·
                refine ⟨53161393702118234365467665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35440929134745489576978443 53161393702118234365467665)
                ·
                  refine ⟨39871045276588675774100749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53161393702118234365467665 39871045276588675774100749)
                  ·
                    refine ⟨14951641978720753415287781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39871045276588675774100749 14951641978720753415287781)
                    ·
                      refine ⟨2803432871010141265366459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14951641978720753415287781 2803432871010141265366459)
                      ·
                        rfl

theorem cell23_5459666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_5459666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459666 prefixEnd_5459666 := by exact prefixLift 5459666
  have htrace : WordTrace (prefixWord ++ tailWord_5459666) baseStart_5459666 baseEnd_5459666 := by
    simpa [prefixWord, tailWord_5459666, baseEnd_5459666] using wordTrace_append hprefix tailTrace_5459666
  have hstable : (prefixWord ++ tailWord_5459666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459666).length < 2 ^ (prefixWord ++ tailWord_5459666).sum := by decide
  have hdescent : baseEnd_5459666 < baseStart_5459666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459729 : List Nat := [1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_5459729 : Nat := 118140960795 + 5459729 * 2 ^ 59
def prefixEnd_5459729 : Nat := 4983230072969 + 3 ^ 40 * 5459729 * 2
def baseEnd_5459729 : Nat := 2803465220291374518878669

theorem tailTrace_5459729 : CollatzResearch.WordTrace tailWord_5459729 prefixEnd_5459729 2803465220291374518878669 := by
  unfold tailWord_5459729
  simp only [CollatzResearch.WordTrace]
  refine ⟨199132676037341755322374241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132755117358227836881582827 199132676037341755322374241)
  ·
    refine ⟨149349507028006316491780681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199132676037341755322374241 149349507028006316491780681)
    ·
      refine ⟨112012130271004737368835511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149349507028006316491780681 112012130271004737368835511)
      ·
        refine ⟨168018195406507106053253267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112012130271004737368835511 168018195406507106053253267)
        ·
          refine ⟨252027293109760659079879901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168018195406507106053253267 252027293109760659079879901)
          ·
            refine ⟨94510234916160247154954963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252027293109760659079879901 94510234916160247154954963)
            ·
              refine ⟨141765352374240370732432445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94510234916160247154954963 141765352374240370732432445)
              ·
                refine ⟨53162007140340139024662167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141765352374240370732432445 53162007140340139024662167)
                ·
                  refine ⟨79743010710510208536993251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53162007140340139024662167 79743010710510208536993251)
                  ·
                    refine ⟨119614516065765312805489877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79743010710510208536993251 119614516065765312805489877)
                    ·
                      refine ⟨2803465220291374518878669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119614516065765312805489877 2803465220291374518878669)
                      ·
                        rfl

theorem cell23_5459729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_5459729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459729 prefixEnd_5459729 := by exact prefixLift 5459729
  have htrace : WordTrace (prefixWord ++ tailWord_5459729) baseStart_5459729 baseEnd_5459729 := by
    simpa [prefixWord, tailWord_5459729, baseEnd_5459729] using wordTrace_append hprefix tailTrace_5459729
  have hstable : (prefixWord ++ tailWord_5459729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459729).length < 2 ^ (prefixWord ++ tailWord_5459729).sum := by decide
  have hdescent : baseEnd_5459729 < baseStart_5459729 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459756 : List Nat := [2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 4]
def baseStart_5459756 : Nat := 118140960795 + 5459756 * 2 ^ 59
def prefixEnd_5459756 : Nat := 4983230072969 + 3 ^ 40 * 5459756 * 2
def baseEnd_5459756 : Nat := 2803479084269045913241045

theorem tailTrace_5459756 : CollatzResearch.WordTrace tailWord_5459756 prefixEnd_5459756 2803479084269045913241045 := by
  unfold tailWord_5459756
  simp only [CollatzResearch.WordTrace]
  refine ⟨99566830404121969466803561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132755773872162625955738081 99566830404121969466803561)
  ·
    refine ⟨74675122803091477100102671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99566830404121969466803561 74675122803091477100102671)
    ·
      refine ⟨112012684204637215650154007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74675122803091477100102671 112012684204637215650154007)
      ·
        refine ⟨168019026306955823475231011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112012684204637215650154007 168019026306955823475231011)
        ·
          refine ⟨252028539460433735212846517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168019026306955823475231011 252028539460433735212846517)
          ·
            refine ⟨23627675574415662676204361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 252028539460433735212846517 23627675574415662676204361)
            ·
              refine ⟨17720756680811747007153271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23627675574415662676204361 17720756680811747007153271)
              ·
                refine ⟨26581135021217620510729907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17720756680811747007153271 26581135021217620510729907)
                ·
                  refine ⟨39871702531826430766094861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26581135021217620510729907 39871702531826430766094861)
                  ·
                    refine ⟨14951888449434911537285573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39871702531826430766094861 14951888449434911537285573)
                    ·
                      refine ⟨2803479084269045913241045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14951888449434911537285573 2803479084269045913241045)
                      ·
                        rfl

theorem cell23_5459756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 4].length) (baseStart_5459756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459756 prefixEnd_5459756 := by exact prefixLift 5459756
  have htrace : WordTrace (prefixWord ++ tailWord_5459756) baseStart_5459756 baseEnd_5459756 := by
    simpa [prefixWord, tailWord_5459756, baseEnd_5459756] using wordTrace_append hprefix tailTrace_5459756
  have hstable : (prefixWord ++ tailWord_5459756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459756).length < 2 ^ (prefixWord ++ tailWord_5459756).sum := by decide
  have hdescent : baseEnd_5459756 < baseStart_5459756 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459773 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_5459773 : Nat := 118140960795 + 5459773 * 2 ^ 59
def prefixEnd_5459773 : Nat := 4983230072969 + 3 ^ 40 * 5459773 * 2
def baseEnd_5459773 : Nat := 2803487813440172346728467

theorem tailTrace_5459773 : CollatzResearch.WordTrace tailWord_5459773 prefixEnd_5459773 2803487813440172346728467 := by
  unfold tailWord_5459773
  simp only [CollatzResearch.WordTrace]
  refine ⟨199134280849182350836975973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132756187232788233891317315 199134280849182350836975973)
  ·
    refine ⟨37337677659221690781932995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199134280849182350836975973 37337677659221690781932995)
    ·
      refine ⟨56006516488832536172899493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37337677659221690781932995 56006516488832536172899493)
      ·
        refine ⟨10501221841656100532418655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56006516488832536172899493 10501221841656100532418655)
        ·
          refine ⟨15751832762484150798627983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10501221841656100532418655 15751832762484150798627983)
          ·
            refine ⟨23627749143726226197941975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15751832762484150798627983 23627749143726226197941975)
            ·
              refine ⟨35441623715589339296912963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23627749143726226197941975 35441623715589339296912963)
              ·
                refine ⟨53162435573384008945369445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35441623715589339296912963 53162435573384008945369445)
                ·
                  refine ⟨9967956670009501677256771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53162435573384008945369445 9967956670009501677256771)
                  ·
                    refine ⟨14951935005014252515885157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9967956670009501677256771 14951935005014252515885157)
                    ·
                      refine ⟨2803487813440172346728467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14951935005014252515885157 2803487813440172346728467)
                      ·
                        rfl

theorem cell23_5459773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_5459773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459773 prefixEnd_5459773 := by exact prefixLift 5459773
  have htrace : WordTrace (prefixWord ++ tailWord_5459773) baseStart_5459773 baseEnd_5459773 := by
    simpa [prefixWord, tailWord_5459773, baseEnd_5459773] using wordTrace_append hprefix tailTrace_5459773
  have hstable : (prefixWord ++ tailWord_5459773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459773).length < 2 ^ (prefixWord ++ tailWord_5459773).sum := by decide
  have hdescent : baseEnd_5459773 < baseStart_5459773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459783 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 3, 4]
def baseStart_5459783 : Nat := 118140960795 + 5459783 * 2 ^ 59
def prefixEnd_5459783 : Nat := 4983230072969 + 3 ^ 40 * 5459783 * 2
def baseEnd_5459783 : Nat := 934497649415572435867807

theorem tailTrace_5459783 : CollatzResearch.WordTrace tailWord_5459783 prefixEnd_5459783 934497649415572435867807 := by
  unfold tailWord_5459783
  simp only [CollatzResearch.WordTrace]
  refine ⟨199134645579146122544840003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132756430386097415029893335 199134645579146122544840003)
  ·
    refine ⟨298701968368719183817260005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199134645579146122544840003 298701968368719183817260005)
    ·
      refine ⟨56006619069134846965736251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 298701968368719183817260005 56006619069134846965736251)
      ·
        refine ⟨84009928603702270448604377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56006619069134846965736251 84009928603702270448604377)
        ·
          refine ⟨63007446452776702836453283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84009928603702270448604377 63007446452776702836453283)
          ·
            refine ⟨94511169679165054254679925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63007446452776702836453283 94511169679165054254679925)
            ·
              refine ⟨8860422157421723836376243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94511169679165054254679925 8860422157421723836376243)
              ·
                refine ⟨13290633236132585754564365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8860422157421723836376243 13290633236132585754564365)
                ·
                  refine ⟨4983987463549719657961637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13290633236132585754564365 4983987463549719657961637)
                  ·
                    refine ⟨934497649415572435867807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4983987463549719657961637 934497649415572435867807)
                    ·
                      rfl

theorem cell23_5459783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_5459783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459783 prefixEnd_5459783 := by exact prefixLift 5459783
  have htrace : WordTrace (prefixWord ++ tailWord_5459783) baseStart_5459783 baseEnd_5459783 := by
    simpa [prefixWord, tailWord_5459783, baseEnd_5459783] using wordTrace_append hprefix tailTrace_5459783
  have hstable : (prefixWord ++ tailWord_5459783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459783).length < 2 ^ (prefixWord ++ tailWord_5459783).sum := by decide
  have hdescent : baseEnd_5459783 < baseStart_5459783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459810 : List Nat := [3, 3, 2, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_5459810 : Nat := 118140960795 + 5459810 * 2 ^ 59
def prefixEnd_5459810 : Nat := 4983230072969 + 3 ^ 40 * 5459810 * 2
def baseEnd_5459810 : Nat := 2803506812224388701965797

theorem tailTrace_5459810 : CollatzResearch.WordTrace tailWord_5459810 prefixEnd_5459810 2803506812224388701965797 := by
  unfold tailWord_5459810
  simp only [CollatzResearch.WordTrace]
  refine ⟨49783907587512076539018221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132757086900032204104048589 49783907587512076539018221)
  ·
    refine ⟨18668965345317028702131833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49783907587512076539018221 18668965345317028702131833)
    ·
      refine ⟨14001724008987771526598875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18668965345317028702131833 14001724008987771526598875)
      ·
        refine ⟨21002586013481657289898313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14001724008987771526598875 21002586013481657289898313)
        ·
          refine ⟨15751939510111242967423735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21002586013481657289898313 15751939510111242967423735)
          ·
            refine ⟨23627909265166864451135603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15751939510111242967423735 23627909265166864451135603)
            ·
              refine ⟨35441863897750296676703405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23627909265166864451135603 35441863897750296676703405)
              ·
                refine ⟨13290698961656361253763777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35441863897750296676703405 13290698961656361253763777)
                ·
                  refine ⟨9968024221242270940322833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13290698961656361253763777 9968024221242270940322833)
                  ·
                    refine ⟨7476018165931703205242125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9968024221242270940322833 7476018165931703205242125)
                    ·
                      refine ⟨2803506812224388701965797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7476018165931703205242125 2803506812224388701965797)
                      ·
                        rfl

theorem cell23_5459810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_5459810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459810 prefixEnd_5459810 := by exact prefixLift 5459810
  have htrace : WordTrace (prefixWord ++ tailWord_5459810) baseStart_5459810 baseEnd_5459810 := by
    simpa [prefixWord, tailWord_5459810, baseEnd_5459810] using wordTrace_append hprefix tailTrace_5459810
  have hstable : (prefixWord ++ tailWord_5459810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459810).length < 2 ^ (prefixWord ++ tailWord_5459810).sum := by decide
  have hdescent : baseEnd_5459810 < baseStart_5459810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459856 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 1, 6]
def baseStart_5459856 : Nat := 118140960795 + 5459856 * 2 ^ 59
def prefixEnd_5459856 : Nat := 4983230072969 + 3 ^ 40 * 5459856 * 2
def baseEnd_5459856 : Nat := 934510144111498507330195

theorem tailTrace_5459856 : CollatzResearch.WordTrace tailWord_5459856 prefixEnd_5459856 934510144111498507330195 := by
  unfold tailWord_5459856
  simp only [CollatzResearch.WordTrace]
  refine ⟨99568654053940828006123711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132758205405254437341498281 99568654053940828006123711)
  ·
    refine ⟨149352981080911242009185567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99568654053940828006123711 149352981080911242009185567)
    ·
      refine ⟨224029471621366863013778351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149352981080911242009185567 224029471621366863013778351)
      ·
        refine ⟨336044207432050294520667527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224029471621366863013778351 336044207432050294520667527)
        ·
          refine ⟨504066311148075441781001291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336044207432050294520667527 504066311148075441781001291)
          ·
            refine ⟨756099466722113162671501937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504066311148075441781001291 756099466722113162671501937)
            ·
              refine ⟨567074600041584872003626453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 756099466722113162671501937 567074600041584872003626453)
              ·
                refine ⟨13290810938474645437584995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 567074600041584872003626453 13290810938474645437584995)
                ·
                  refine ⟨19936216407711968156377493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13290810938474645437584995 19936216407711968156377493)
                  ·
                    refine ⟨934510144111498507330195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19936216407711968156377493 934510144111498507330195)
                    ·
                      rfl

theorem cell23_5459856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 1, 6].length) (baseStart_5459856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459856 prefixEnd_5459856 := by exact prefixLift 5459856
  have htrace : WordTrace (prefixWord ++ tailWord_5459856) baseStart_5459856 baseEnd_5459856 := by
    simpa [prefixWord, tailWord_5459856, baseEnd_5459856] using wordTrace_append hprefix tailTrace_5459856
  have hstable : (prefixWord ++ tailWord_5459856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459856).length < 2 ^ (prefixWord ++ tailWord_5459856).sum := by decide
  have hdescent : baseEnd_5459856 < baseStart_5459856 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459863 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 4]
def baseStart_5459863 : Nat := 118140960795 + 5459863 * 2 ^ 59
def prefixEnd_5459863 : Nat := 4983230072969 + 3 ^ 40 * 5459863 * 2
def baseEnd_5459863 : Nat := 2803534026699076994603053

theorem tailTrace_5459863 : CollatzResearch.WordTrace tailWord_5459863 prefixEnd_5459863 2803534026699076994603053 := by
  unfold tailWord_5459863
  simp only [CollatzResearch.WordTrace]
  refine ⟨199137563418856296207752243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132758375612570864138501495 199137563418856296207752243)
  ·
    refine ⟨298706345128284444311628365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199137563418856296207752243 298706345128284444311628365)
    ·
      refine ⟨112014879423106666616860637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298706345128284444311628365 112014879423106666616860637)
      ·
        refine ⟨42005579783664999981322739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112014879423106666616860637 42005579783664999981322739)
        ·
          refine ⟨63008369675497499971984109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42005579783664999981322739 63008369675497499971984109)
          ·
            refine ⟨23628138628311562489494041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63008369675497499971984109 23628138628311562489494041)
            ·
              refine ⟨17721103971233671867120531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23628138628311562489494041 17721103971233671867120531)
              ·
                refine ⟨26581655956850507800680797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17721103971233671867120531 26581655956850507800680797)
                ·
                  refine ⟨9968120983818940425255299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26581655956850507800680797 9968120983818940425255299)
                  ·
                    refine ⟨14952181475728410637882949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9968120983818940425255299 14952181475728410637882949)
                    ·
                      refine ⟨2803534026699076994603053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14952181475728410637882949 2803534026699076994603053)
                      ·
                        rfl

theorem cell23_5459863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_5459863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459863 prefixEnd_5459863 := by exact prefixLift 5459863
  have htrace : WordTrace (prefixWord ++ tailWord_5459863) baseStart_5459863 baseEnd_5459863 := by
    simpa [prefixWord, tailWord_5459863, baseEnd_5459863] using wordTrace_append hprefix tailTrace_5459863
  have hstable : (prefixWord ++ tailWord_5459863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459863).length < 2 ^ (prefixWord ++ tailWord_5459863).sum := by decide
  have hdescent : baseEnd_5459863 < baseStart_5459863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459897 : List Nat := [1, 2, 1, 4, 2, 1, 4, 1, 3, 2, 2]
def baseStart_5459897 : Nat := 118140960795 + 5459897 * 2 ^ 59
def prefixEnd_5459897 : Nat := 4983230072969 + 3 ^ 40 * 5459897 * 2
def baseEnd_5459897 : Nat := 2803551485041329861577897

theorem tailTrace_5459897 : CollatzResearch.WordTrace tailWord_5459897 prefixEnd_5459897 2803551485041329861577897 := by
  unfold tailWord_5459897
  simp only [CollatzResearch.WordTrace]
  refine ⟨199138803500733120014489945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132759202333822080009659963 199138803500733120014489945)
  ·
    refine ⟨149354102625549840010867459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199138803500733120014489945 149354102625549840010867459)
    ·
      refine ⟨224031153938324760016301189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149354102625549840010867459 224031153938324760016301189)
      ·
        refine ⟨42005841363435892503056473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224031153938324760016301189 42005841363435892503056473)
        ·
          refine ⟨31504381022576919377292355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42005841363435892503056473 31504381022576919377292355)
          ·
            refine ⟨47256571533865379065938533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31504381022576919377292355 47256571533865379065938533)
            ·
              refine ⟨8860607162599758574863475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47256571533865379065938533 8860607162599758574863475)
              ·
                refine ⟨13290910743899637862295213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8860607162599758574863475 13290910743899637862295213)
                ·
                  refine ⟨4984091528962364198360705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13290910743899637862295213 4984091528962364198360705)
                  ·
                    refine ⟨3738068646721773148770529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4984091528962364198360705 3738068646721773148770529)
                    ·
                      refine ⟨2803551485041329861577897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738068646721773148770529 2803551485041329861577897)
                      ·
                        rfl

theorem cell23_5459897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 4, 1, 3, 2, 2].length) (baseStart_5459897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459897 prefixEnd_5459897 := by exact prefixLift 5459897
  have htrace : WordTrace (prefixWord ++ tailWord_5459897) baseStart_5459897 baseEnd_5459897 := by
    simpa [prefixWord, tailWord_5459897, baseEnd_5459897] using wordTrace_append hprefix tailTrace_5459897
  have hstable : (prefixWord ++ tailWord_5459897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459897).length < 2 ^ (prefixWord ++ tailWord_5459897).sum := by decide
  have hdescent : baseEnd_5459897 < baseStart_5459897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459936 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 8]
def baseStart_5459936 : Nat := 118140960795 + 5459936 * 2 ^ 59
def prefixEnd_5459936 : Nat := 4983230072969 + 3 ^ 40 * 5459936 * 2
def baseEnd_5459936 : Nat := 2803571510786855208990217

theorem tailTrace_5459936 : CollatzResearch.WordTrace tailWord_5459936 prefixEnd_5459936 2803571510786855208990217 := by
  unfold tailWord_5459936
  simp only [CollatzResearch.WordTrace]
  refine ⟨99570112973795914837579831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132760150631727886450106441 99570112973795914837579831)
  ·
    refine ⟨149355169460693872256369747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99570112973795914837579831 149355169460693872256369747)
    ·
      refine ⟨224032754191040808384554621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149355169460693872256369747 224032754191040808384554621)
      ·
        refine ⟨84012282821640303144207983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224032754191040808384554621 84012282821640303144207983)
        ·
          refine ⟨126018424232460454716311975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84012282821640303144207983 126018424232460454716311975)
          ·
            refine ⟨189027636348690682074467963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126018424232460454716311975 189027636348690682074467963)
            ·
              refine ⟨283541454523036023111701945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189027636348690682074467963 283541454523036023111701945)
              ·
                refine ⟨212656090892277017333776459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283541454523036023111701945 212656090892277017333776459)
                ·
                  refine ⟨318984136338415526000664689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212656090892277017333776459 318984136338415526000664689)
                  ·
                    refine ⟨239238102253811644500498517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 318984136338415526000664689 239238102253811644500498517)
                    ·
                      refine ⟨2803571510786855208990217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 239238102253811644500498517 2803571510786855208990217)
                      ·
                        rfl

theorem cell23_5459936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_5459936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459936 prefixEnd_5459936 := by exact prefixLift 5459936
  have htrace : WordTrace (prefixWord ++ tailWord_5459936) baseStart_5459936 baseEnd_5459936 := by
    simpa [prefixWord, tailWord_5459936, baseEnd_5459936] using wordTrace_append hprefix tailTrace_5459936
  have hstable : (prefixWord ++ tailWord_5459936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459936).length < 2 ^ (prefixWord ++ tailWord_5459936).sum := by decide
  have hdescent : baseEnd_5459936 < baseStart_5459936 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459973 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_5459973 : Nat := 118140960795 + 5459973 * 2 ^ 59
def prefixEnd_5459973 : Nat := 4983230072969 + 3 ^ 40 * 5459973 * 2
def baseEnd_5459973 : Nat := 2803590509571071564227547

theorem tailTrace_5459973 : CollatzResearch.WordTrace tailWord_5459973 prefixEnd_5459973 2803590509571071564227547 := by
  unfold tailWord_5459973
  simp only [CollatzResearch.WordTrace]
  refine ⟨199141575448457784994256573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132761050298971856662837715 199141575448457784994256573)
  ·
    refine ⟨74678090793171669372846215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199141575448457784994256573 74678090793171669372846215)
    ·
      refine ⟨112017136189757504059269323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74678090793171669372846215 112017136189757504059269323)
      ·
        refine ⟨168025704284636256088903985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112017136189757504059269323 168025704284636256088903985)
        ·
          refine ⟨126019278213477192066677989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168025704284636256088903985 126019278213477192066677989)
          ·
            refine ⟨23628614665026973512502123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126019278213477192066677989 23628614665026973512502123)
            ·
              refine ⟨35442921997540460268753185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23628614665026973512502123 35442921997540460268753185)
              ·
                refine ⟨26582191498155345201564889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35442921997540460268753185 26582191498155345201564889)
                ·
                  refine ⟨19936643623616508901173667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26582191498155345201564889 19936643623616508901173667)
                  ·
                    refine ⟨29904965435424763351760501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19936643623616508901173667 29904965435424763351760501)
                    ·
                      refine ⟨2803590509571071564227547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29904965435424763351760501 2803590509571071564227547)
                      ·
                        rfl

theorem cell23_5459973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_5459973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459973 prefixEnd_5459973 := by exact prefixLift 5459973
  have htrace : WordTrace (prefixWord ++ tailWord_5459973) baseStart_5459973 baseEnd_5459973 := by
    simpa [prefixWord, tailWord_5459973, baseEnd_5459973] using wordTrace_append hprefix tailTrace_5459973
  have hstable : (prefixWord ++ tailWord_5459973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459973).length < 2 ^ (prefixWord ++ tailWord_5459973).sum := by decide
  have hdescent : baseEnd_5459973 < baseStart_5459973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459981 : List Nat := [1, 7, 1, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_5459981 : Nat := 118140960795 + 5459981 * 2 ^ 59
def prefixEnd_5459981 : Nat := 4983230072969 + 3 ^ 40 * 5459981 * 2
def baseEnd_5459981 : Nat := 2803594617416307532927511

theorem tailTrace_5459981 : CollatzResearch.WordTrace tailWord_5459981 prefixEnd_5459981 2803594617416307532927511 := by
  unfold tailWord_5459981
  simp only [CollatzResearch.WordTrace]
  refine ⟨199141867232428802360547797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132761244821619201573698531 199141867232428802360547797)
  ·
    refine ⟨4667387513260050055325339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 199141867232428802360547797 4667387513260050055325339)
    ·
      refine ⟨7001081269890075082988009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4667387513260050055325339 7001081269890075082988009)
      ·
        refine ⟨5250810952417556312241007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7001081269890075082988009 5250810952417556312241007)
        ·
          refine ⟨7876216428626334468361511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5250810952417556312241007 7876216428626334468361511)
          ·
            refine ⟨11814324642939501702542267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7876216428626334468361511 11814324642939501702542267)
            ·
              refine ⟨17721486964409252553813401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11814324642939501702542267 17721486964409252553813401)
              ·
                refine ⟨13291115223306939415360051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17721486964409252553813401 13291115223306939415360051)
                ·
                  refine ⟨19936672834960409123040077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13291115223306939415360051 19936672834960409123040077)
                  ·
                    refine ⟨7476252313110153421140029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19936672834960409123040077 7476252313110153421140029)
                    ·
                      refine ⟨2803594617416307532927511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7476252313110153421140029 2803594617416307532927511)
                      ·
                        rfl

theorem cell23_5459981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_5459981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459981 prefixEnd_5459981 := by exact prefixLift 5459981
  have htrace : WordTrace (prefixWord ++ tailWord_5459981) baseStart_5459981 baseEnd_5459981 := by
    simpa [prefixWord, tailWord_5459981, baseEnd_5459981] using wordTrace_append hprefix tailTrace_5459981
  have hstable : (prefixWord ++ tailWord_5459981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459981).length < 2 ^ (prefixWord ++ tailWord_5459981).sum := by decide
  have hdescent : baseEnd_5459981 < baseStart_5459981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5459991 : List Nat := [1, 1, 3, 5, 2, 1, 3, 1, 1, 3, 2]
def baseStart_5459991 : Nat := 118140960795 + 5459991 * 2 ^ 59
def prefixEnd_5459991 : Nat := 4983230072969 + 3 ^ 40 * 5459991 * 2
def baseEnd_5459991 : Nat := 2803599752222852493802465

theorem tailTrace_5459991 : CollatzResearch.WordTrace tailWord_5459991 prefixEnd_5459991 2803599752222852493802465 := by
  unfold tailWord_5459991
  simp only [CollatzResearch.WordTrace]
  refine ⟨199142231962392574068411827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132761487974928382712274551 199142231962392574068411827)
  ·
    refine ⟨298713347943588861102617741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199142231962392574068411827 298713347943588861102617741)
    ·
      refine ⟨112017505478845822913481653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298713347943588861102617741 112017505478845822913481653)
      ·
        refine ⟨10501641138641795898138905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112017505478845822913481653 10501641138641795898138905)
        ·
          refine ⟨7876230853981346923604179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10501641138641795898138905 7876230853981346923604179)
          ·
            refine ⟨11814346280972020385406269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7876230853981346923604179 11814346280972020385406269)
            ·
              refine ⟨4430379855364507644527351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11814346280972020385406269 4430379855364507644527351)
              ·
                refine ⟨6645569783046761466791027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4430379855364507644527351 6645569783046761466791027)
                ·
                  refine ⟨9968354674570142200186541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6645569783046761466791027 9968354674570142200186541)
                  ·
                    refine ⟨3738133002963803325069953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9968354674570142200186541 3738133002963803325069953)
                    ·
                      refine ⟨2803599752222852493802465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738133002963803325069953 2803599752222852493802465)
                      ·
                        rfl

theorem cell23_5459991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 1, 3, 2].length) (baseStart_5459991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5459991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5459991 prefixEnd_5459991 := by exact prefixLift 5459991
  have htrace : WordTrace (prefixWord ++ tailWord_5459991) baseStart_5459991 baseEnd_5459991 := by
    simpa [prefixWord, tailWord_5459991, baseEnd_5459991] using wordTrace_append hprefix tailTrace_5459991
  have hstable : (prefixWord ++ tailWord_5459991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5459991).length < 2 ^ (prefixWord ++ tailWord_5459991).sum := by decide
  have hdescent : baseEnd_5459991 < baseStart_5459991 := by decide
  rcases family_descends (prefixWord ++ tailWord_5459991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460023 : List Nat := [1, 1, 3, 1, 2, 2, 2, 2, 4, 5]
def baseStart_5460023 : Nat := 118140960795 + 5460023 * 2 ^ 59
def prefixEnd_5460023 : Nat := 4983230072969 + 3 ^ 40 * 5460023 * 2
def baseEnd_5460023 : Nat := 934538727867932122867439

theorem tailTrace_5460023 : CollatzResearch.WordTrace tailWord_5460023 prefixEnd_5460023 934538727867932122867439 := by
  unfold tailWord_5460023
  simp only [CollatzResearch.WordTrace]
  refine ⟨199143399098276643533576723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132762266065517762355717815 199143399098276643533576723)
  ·
    refine ⟨298715098647414965300365085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199143399098276643533576723 298715098647414965300365085)
    ·
      refine ⟨112018161992780611987636907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298715098647414965300365085 112018161992780611987636907)
      ·
        refine ⟨168027242989170917981455361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112018161992780611987636907 168027242989170917981455361)
        ·
          refine ⟨126020432241878188486091521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168027242989170917981455361 126020432241878188486091521)
          ·
            refine ⟨94515324181408641364568641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126020432241878188486091521 94515324181408641364568641)
            ·
              refine ⟨70886493136056481023426481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94515324181408641364568641 70886493136056481023426481)
              ·
                refine ⟨53164869852042360767569861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70886493136056481023426481 53164869852042360767569861)
                ·
                  refine ⟨9968413097257942643919349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53164869852042360767569861 9968413097257942643919349)
                  ·
                    refine ⟨934538727867932122867439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9968413097257942643919349 934538727867932122867439)
                    ·
                      rfl

theorem cell23_5460023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_5460023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460023 prefixEnd_5460023 := by exact prefixLift 5460023
  have htrace : WordTrace (prefixWord ++ tailWord_5460023) baseStart_5460023 baseEnd_5460023 := by
    simpa [prefixWord, tailWord_5460023, baseEnd_5460023] using wordTrace_append hprefix tailTrace_5460023
  have hstable : (prefixWord ++ tailWord_5460023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460023).length < 2 ^ (prefixWord ++ tailWord_5460023).sum := by decide
  have hdescent : baseEnd_5460023 < baseStart_5460023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460043 : List Nat := [1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 4]
def baseStart_5460043 : Nat := 118140960795 + 5460043 * 2 ^ 59
def prefixEnd_5460043 : Nat := 4983230072969 + 3 ^ 40 * 5460043 * 2
def baseEnd_5460043 : Nat := 2803626453216886290352225

theorem tailTrace_5460043 : CollatzResearch.WordTrace tailWord_5460043 prefixEnd_5460043 2803626453216886290352225 := by
  unfold tailWord_5460043
  simp only [CollatzResearch.WordTrace]
  refine ⟨199144128558204186949304783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132762752372136124632869855 199144128558204186949304783)
  ·
    refine ⟨298716192837306280423957175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199144128558204186949304783 298716192837306280423957175)
    ·
      refine ⟨448074289255959420635935763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298716192837306280423957175 448074289255959420635935763)
      ·
        refine ⟨672111433883939130953903645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448074289255959420635935763 672111433883939130953903645)
        ·
          refine ⟨252041787706477174107713867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 672111433883939130953903645 252041787706477174107713867)
          ·
            refine ⟨378062681559715761161570801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252041787706477174107713867 378062681559715761161570801)
            ·
              refine ⟨283547011169786820871178101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378062681559715761161570801 283547011169786820871178101)
              ·
                refine ⟨26582532297167514456672947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 283547011169786820871178101 26582532297167514456672947)
                ·
                  refine ⟨39873798445751271685009421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26582532297167514456672947 39873798445751271685009421)
                  ·
                    refine ⟨14952674417156726881878533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39873798445751271685009421 14952674417156726881878533)
                    ·
                      refine ⟨2803626453216886290352225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14952674417156726881878533 2803626453216886290352225)
                      ·
                        rfl

theorem cell23_5460043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 4].length) (baseStart_5460043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460043 prefixEnd_5460043 := by exact prefixLift 5460043
  have htrace : WordTrace (prefixWord ++ tailWord_5460043) baseStart_5460043 baseEnd_5460043 := by
    simpa [prefixWord, tailWord_5460043, baseEnd_5460043] using wordTrace_append hprefix tailTrace_5460043
  have hstable : (prefixWord ++ tailWord_5460043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460043).length < 2 ^ (prefixWord ++ tailWord_5460043).sum := by decide
  have hdescent : baseEnd_5460043 < baseStart_5460043 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460054 : List Nat := [5, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3]
def baseStart_5460054 : Nat := 118140960795 + 5460054 * 2 ^ 59
def prefixEnd_5460054 : Nat := 4983230072969 + 3 ^ 40 * 5460054 * 2
def baseEnd_5460054 : Nat := 2803632101504085747314675

theorem tailTrace_5460054 : CollatzResearch.WordTrace tailWord_5460054 prefixEnd_5460054 2803632101504085747314675 := by
  unfold tailWord_5460054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12446533110072770989247201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132763019840776223885303477 12446533110072770989247201)
  ·
    refine ⟨9334899832554578241935401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12446533110072770989247201 9334899832554578241935401)
    ·
      refine ⟨7001174874415933681451551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9334899832554578241935401 7001174874415933681451551)
      ·
        refine ⟨10501762311623900522177327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7001174874415933681451551 10501762311623900522177327)
        ·
          refine ⟨15752643467435850783265991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10501762311623900522177327 15752643467435850783265991)
          ·
            refine ⟨23628965201153776174898987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15752643467435850783265991 23628965201153776174898987)
            ·
              refine ⟨35443447801730664262348481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23628965201153776174898987 35443447801730664262348481)
              ·
                refine ⟨26582585851297998196761361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35443447801730664262348481 26582585851297998196761361)
                ·
                  refine ⟨19936939388473498647571021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26582585851297998196761361 19936939388473498647571021)
                  ·
                    refine ⟨7476352270677561992839133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19936939388473498647571021 7476352270677561992839133)
                    ·
                      refine ⟨2803632101504085747314675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7476352270677561992839133 2803632101504085747314675)
                      ·
                        rfl

theorem cell23_5460054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_5460054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460054 prefixEnd_5460054 := by exact prefixLift 5460054
  have htrace : WordTrace (prefixWord ++ tailWord_5460054) baseStart_5460054 baseEnd_5460054 := by
    simpa [prefixWord, tailWord_5460054, baseEnd_5460054] using wordTrace_append hprefix tailTrace_5460054
  have hstable : (prefixWord ++ tailWord_5460054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460054).length < 2 ^ (prefixWord ++ tailWord_5460054).sum := by decide
  have hdescent : baseEnd_5460054 < baseStart_5460054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460073 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 6]
def baseStart_5460073 : Nat := 118140960795 + 5460073 * 2 ^ 59
def prefixEnd_5460073 : Nat := 4983230072969 + 3 ^ 40 * 5460073 * 2
def baseEnd_5460073 : Nat := 2803641857636521172977087

theorem tailTrace_5460073 : CollatzResearch.WordTrace tailWord_5460073 prefixEnd_5460073 2803641857636521172977087 := by
  unfold tailWord_5460073
  simp only [CollatzResearch.WordTrace]
  refine ⟨199145222748095502072896873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132763481832063668048597915 199145222748095502072896873)
  ·
    refine ⟨149358917061071626554672655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199145222748095502072896873 149358917061071626554672655)
    ·
      refine ⟨224038375591607439832008983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149358917061071626554672655 224038375591607439832008983)
      ·
        refine ⟨336057563387411159748013475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224038375591607439832008983 336057563387411159748013475)
        ·
          refine ⟨504086345081116739622020213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336057563387411159748013475 504086345081116739622020213)
          ·
            refine ⟨47258094851354694339564395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 504086345081116739622020213 47258094851354694339564395)
            ·
              refine ⟨70887142277032041509346593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47258094851354694339564395 70887142277032041509346593)
              ·
                refine ⟨53165356707774031132009945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70887142277032041509346593 53165356707774031132009945)
                ·
                  refine ⟨39874017530830523349007459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53165356707774031132009945 39874017530830523349007459)
                  ·
                    refine ⟨59811026296245785023511189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39874017530830523349007459 59811026296245785023511189)
                    ·
                      refine ⟨2803641857636521172977087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59811026296245785023511189 2803641857636521172977087)
                      ·
                        rfl

theorem cell23_5460073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_5460073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460073 prefixEnd_5460073 := by exact prefixLift 5460073
  have htrace : WordTrace (prefixWord ++ tailWord_5460073) baseStart_5460073 baseEnd_5460073 := by
    simpa [prefixWord, tailWord_5460073, baseEnd_5460073] using wordTrace_append hprefix tailTrace_5460073
  have hstable : (prefixWord ++ tailWord_5460073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460073).length < 2 ^ (prefixWord ++ tailWord_5460073).sum := by decide
  have hdescent : baseEnd_5460073 < baseStart_5460073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460077 : List Nat := [1, 5, 1, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_5460077 : Nat := 118140960795 + 5460077 * 2 ^ 59
def prefixEnd_5460077 : Nat := 4983230072969 + 3 ^ 40 * 5460077 * 2
def baseEnd_5460077 : Nat := 2803643911559139157327069

theorem tailTrace_5460077 : CollatzResearch.WordTrace tailWord_5460077 prefixEnd_5460077 2803643911559139157327069 := by
  unfold tailWord_5460077
  simp only [CollatzResearch.WordTrace]
  refine ⟨199145368640081010756042485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132763579093387340504028323 199145368640081010756042485)
  ·
    refine ⟨18669878310007594758378983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199145368640081010756042485 18669878310007594758378983)
    ·
      refine ⟨28004817465011392137568475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18669878310007594758378983 28004817465011392137568475)
      ·
        refine ⟨42007226197517088206352713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28004817465011392137568475 42007226197517088206352713)
        ·
          refine ⟨31505419648137816154764535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42007226197517088206352713 31505419648137816154764535)
          ·
            refine ⟨47258129472206724232146803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31505419648137816154764535 47258129472206724232146803)
            ·
              refine ⟨70887194208310086348220205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47258129472206724232146803 70887194208310086348220205)
              ·
                refine ⟨26582697828116282380582577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70887194208310086348220205 26582697828116282380582577)
                ·
                  refine ⟨19937023371087211785436933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26582697828116282380582577 19937023371087211785436933)
                  ·
                    refine ⟨3738191882078852209769425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19937023371087211785436933 3738191882078852209769425)
                    ·
                      refine ⟨2803643911559139157327069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738191882078852209769425 2803643911559139157327069)
                      ·
                        rfl

theorem cell23_5460077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_5460077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460077 prefixEnd_5460077 := by exact prefixLift 5460077
  have htrace : WordTrace (prefixWord ++ tailWord_5460077) baseStart_5460077 baseEnd_5460077 := by
    simpa [prefixWord, tailWord_5460077, baseEnd_5460077] using wordTrace_append hprefix tailTrace_5460077
  have hstable : (prefixWord ++ tailWord_5460077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460077).length < 2 ^ (prefixWord ++ tailWord_5460077).sum := by decide
  have hdescent : baseEnd_5460077 < baseStart_5460077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460080 : List Nat := [2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 3]
def baseStart_5460080 : Nat := 118140960795 + 5460080 * 2 ^ 59
def prefixEnd_5460080 : Nat := 4983230072969 + 3 ^ 40 * 5460080 * 2
def baseEnd_5460080 : Nat := 2803645452001102645589555

theorem tailTrace_5460080 : CollatzResearch.WordTrace tailWord_5460080 prefixEnd_5460080 2803645452001102645589555 := by
  unfold tailWord_5460080
  simp only [CollatzResearch.WordTrace]
  refine ⟨99572739029535071134200847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132763652039380094845601129 99572739029535071134200847)
  ·
    refine ⟨149359108544302606701301271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99572739029535071134200847 149359108544302606701301271)
    ·
      refine ⟨224038662816453910051951907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149359108544302606701301271 224038662816453910051951907)
      ·
        refine ⟨336057994224680865077927861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224038662816453910051951907 336057994224680865077927861)
        ·
          refine ⟨31505436958563831101055737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 336057994224680865077927861 31505436958563831101055737)
          ·
            refine ⟨23629077718922873325791803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31505436958563831101055737 23629077718922873325791803)
            ·
              refine ⟨35443616578384309988687705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23629077718922873325791803 35443616578384309988687705)
              ·
                refine ⟨26582712433788232491515779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35443616578384309988687705 26582712433788232491515779)
                ·
                  refine ⟨39874068650682348737273669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26582712433788232491515779 39874068650682348737273669)
                  ·
                    refine ⟨7476387872002940388238813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39874068650682348737273669 7476387872002940388238813)
                    ·
                      refine ⟨2803645452001102645589555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7476387872002940388238813 2803645452001102645589555)
                      ·
                        rfl

theorem cell23_5460080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 3].length) (baseStart_5460080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460080 prefixEnd_5460080 := by exact prefixLift 5460080
  have htrace : WordTrace (prefixWord ++ tailWord_5460080) baseStart_5460080 baseEnd_5460080 := by
    simpa [prefixWord, tailWord_5460080, baseEnd_5460080] using wordTrace_append hprefix tailTrace_5460080
  have hstable : (prefixWord ++ tailWord_5460080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460080).length < 2 ^ (prefixWord ++ tailWord_5460080).sum := by decide
  have hdescent : baseEnd_5460080 < baseStart_5460080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460118 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 1, 2, 5]
def baseStart_5460118 : Nat := 118140960795 + 5460118 * 2 ^ 59
def prefixEnd_5460118 : Nat := 4983230072969 + 3 ^ 40 * 5460118 * 2
def baseEnd_5460118 : Nat := 2803664964265973496914381

theorem tailTrace_5460118 : CollatzResearch.WordTrace tailWord_5460118 prefixEnd_5460118 2803664964265973496914381 := by
  unfold tailWord_5460118
  simp only [CollatzResearch.WordTrace]
  refine ⟨12446679002058279672392813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132764576021954983172190005 12446679002058279672392813)
  ·
    refine ⟨4667504625771854877147305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12446679002058279672392813 4667504625771854877147305)
    ·
      refine ⟨3500628469328891157860479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4667504625771854877147305 3500628469328891157860479)
      ·
        refine ⟨5250942703993336736790719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3500628469328891157860479 5250942703993336736790719)
        ·
          refine ⟨7876414055990005105186079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5250942703993336736790719 7876414055990005105186079)
          ·
            refine ⟨11814621083985007657779119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7876414055990005105186079 11814621083985007657779119)
            ·
              refine ⟨17721931625977511486668679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11814621083985007657779119 17721931625977511486668679)
              ·
                refine ⟨26582897438966267230003019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17721931625977511486668679 26582897438966267230003019)
                ·
                  refine ⟨39874346158449400845004529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26582897438966267230003019 39874346158449400845004529)
                  ·
                    refine ⟨29905759618837050633753397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39874346158449400845004529 29905759618837050633753397)
                    ·
                      refine ⟨2803664964265973496914381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29905759618837050633753397 2803664964265973496914381)
                      ·
                        rfl

theorem cell23_5460118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_5460118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460118 prefixEnd_5460118 := by exact prefixLift 5460118
  have htrace : WordTrace (prefixWord ++ tailWord_5460118) baseStart_5460118 baseEnd_5460118 := by
    simpa [prefixWord, tailWord_5460118, baseEnd_5460118] using wordTrace_append hprefix tailTrace_5460118
  have hstable : (prefixWord ++ tailWord_5460118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460118).length < 2 ^ (prefixWord ++ tailWord_5460118).sum := by decide
  have hdescent : baseEnd_5460118 < baseStart_5460118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460123 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 5]
def baseStart_5460123 : Nat := 118140960795 + 5460123 * 2 ^ 59
def prefixEnd_5460123 : Nat := 4983230072969 + 3 ^ 40 * 5460123 * 2
def baseEnd_5460123 : Nat := 2803667531669245977351857

theorem tailTrace_5460123 : CollatzResearch.WordTrace tailWord_5460123 prefixEnd_5460123 2803667531669245977351857 := by
  unfold tailWord_5460123
  simp only [CollatzResearch.WordTrace]
  refine ⟨199147046397914360612217023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132764697598609573741478015 199147046397914360612217023)
  ·
    refine ⟨298720569596871540918325535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199147046397914360612217023 298720569596871540918325535)
    ·
      refine ⟨448080854395307311377488303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298720569596871540918325535 448080854395307311377488303)
      ·
        refine ⟨672121281592960967066232455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448080854395307311377488303 672121281592960967066232455)
        ·
          refine ⟨1008181922389441450599348683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672121281592960967066232455 1008181922389441450599348683)
          ·
            refine ⟨1512272883584162175899023025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008181922389441450599348683 1512272883584162175899023025)
            ·
              refine ⟨1134204662688121631924267269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1512272883584162175899023025 1134204662688121631924267269)
              ·
                refine ⟨212663374254022805985800113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1134204662688121631924267269 212663374254022805985800113)
                ·
                  refine ⟨159497530690517104489350085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212663374254022805985800113 159497530690517104489350085)
                  ·
                    refine ⟨29905787004471957091753141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159497530690517104489350085 29905787004471957091753141)
                    ·
                      refine ⟨2803667531669245977351857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29905787004471957091753141 2803667531669245977351857)
                      ·
                        rfl

theorem cell23_5460123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 5].length) (baseStart_5460123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460123 prefixEnd_5460123 := by exact prefixLift 5460123
  have htrace : WordTrace (prefixWord ++ tailWord_5460123) baseStart_5460123 baseEnd_5460123 := by
    simpa [prefixWord, tailWord_5460123, baseEnd_5460123] using wordTrace_append hprefix tailTrace_5460123
  have hstable : (prefixWord ++ tailWord_5460123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460123).length < 2 ^ (prefixWord ++ tailWord_5460123).sum := by decide
  have hdescent : baseEnd_5460123 < baseStart_5460123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460160 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 3, 6]
def baseStart_5460160 : Nat := 118140960795 + 5460160 * 2 ^ 59
def prefixEnd_5460160 : Nat := 4983230072969 + 3 ^ 40 * 5460160 * 2
def baseEnd_5460160 : Nat := 934562176817820777529729

theorem tailTrace_5460160 : CollatzResearch.WordTrace tailWord_5460160 prefixEnd_5460160 934562176817820777529729 := by
  unfold tailWord_5460160
  simp only [CollatzResearch.WordTrace]
  refine ⟨99574197949390157965656967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132765597265853543954209289 99574197949390157965656967)
  ·
    refine ⟨149361296924085236948485451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99574197949390157965656967 149361296924085236948485451)
    ·
      refine ⟨224041945386127855422728177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149361296924085236948485451 224041945386127855422728177)
      ·
        refine ⟨168031459039595891567046133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224041945386127855422728177 168031459039595891567046133)
        ·
          refine ⟨15752949284962114834410575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168031459039595891567046133 15752949284962114834410575)
          ·
            refine ⟨23629423927443172251615863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15752949284962114834410575 23629423927443172251615863)
            ·
              refine ⟨35444135891164758377423795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23629423927443172251615863 35444135891164758377423795)
              ·
                refine ⟨53166203836747137566135693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35444135891164758377423795 53166203836747137566135693)
                ·
                  refine ⟨19937326438780176587300885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53166203836747137566135693 19937326438780176587300885)
                  ·
                    refine ⟨934562176817820777529729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19937326438780176587300885 934562176817820777529729)
                    ·
                      rfl

theorem cell23_5460160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 3, 6].length) (baseStart_5460160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460160 prefixEnd_5460160 := by exact prefixLift 5460160
  have htrace : WordTrace (prefixWord ++ tailWord_5460160) baseStart_5460160 baseEnd_5460160 := by
    simpa [prefixWord, tailWord_5460160, baseEnd_5460160] using wordTrace_append hprefix tailTrace_5460160
  have hstable : (prefixWord ++ tailWord_5460160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460160).length < 2 ^ (prefixWord ++ tailWord_5460160).sum := by decide
  have hdescent : baseEnd_5460160 < baseStart_5460160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460177 : List Nat := [1, 2, 2, 1, 2, 2, 3, 4, 2, 4]
def baseStart_5460177 : Nat := 118140960795 + 5460177 * 2 ^ 59
def prefixEnd_5460177 : Nat := 4983230072969 + 3 ^ 40 * 5460177 * 2
def baseEnd_5460177 : Nat := 934565086541529588692203

theorem tailTrace_5460177 : CollatzResearch.WordTrace tailWord_5460177 prefixEnd_5460177 934565086541529588692203 := by
  unfold tailWord_5460177
  simp only [CollatzResearch.WordTrace]
  refine ⟨199149015939718727834682785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132766010626479151889788523 199149015939718727834682785)
  ·
    refine ⟨149361761954789045876012089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199149015939718727834682785 149361761954789045876012089)
    ·
      refine ⟨112021321466091784407009067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149361761954789045876012089 112021321466091784407009067)
      ·
        refine ⟨168031982199137676610513601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112021321466091784407009067 168031982199137676610513601)
        ·
          refine ⟨126023986649353257457885201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168031982199137676610513601 126023986649353257457885201)
          ·
            refine ⟨94517989987014943093413901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126023986649353257457885201 94517989987014943093413901)
            ·
              refine ⟨35444246245130603660030213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94517989987014943093413901 35444246245130603660030213)
              ·
                refine ⟨6645796170961988186255665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35444246245130603660030213 6645796170961988186255665)
                ·
                  refine ⟨4984347128221491139691749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6645796170961988186255665 4984347128221491139691749)
                  ·
                    refine ⟨934565086541529588692203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4984347128221491139691749 934565086541529588692203)
                    ·
                      rfl

theorem cell23_5460177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_5460177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460177 prefixEnd_5460177 := by exact prefixLift 5460177
  have htrace : WordTrace (prefixWord ++ tailWord_5460177) baseStart_5460177 baseEnd_5460177 := by
    simpa [prefixWord, tailWord_5460177, baseEnd_5460177] using wordTrace_append hprefix tailTrace_5460177
  have hstable : (prefixWord ++ tailWord_5460177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460177).length < 2 ^ (prefixWord ++ tailWord_5460177).sum := by decide
  have hdescent : baseEnd_5460177 < baseStart_5460177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460178 : List Nat := [3, 2, 2, 2, 1, 2, 4, 2, 1, 1, 3]
def baseStart_5460178 : Nat := 118140960795 + 5460178 * 2 ^ 59
def prefixEnd_5460178 : Nat := 4983230072969 + 3 ^ 40 * 5460178 * 2
def baseEnd_5460178 : Nat := 2803695773105243262164105

theorem tailTrace_5460178 : CollatzResearch.WordTrace tailWord_5460178 prefixEnd_5460178 2803695773105243262164105 := by
  unfold tailWord_5460178
  simp only [CollatzResearch.WordTrace]
  refine ⟨49787263103178776251367297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132766034941810070003646125 49787263103178776251367297)
  ·
    refine ⟨37340447327384082188525473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49787263103178776251367297 37340447327384082188525473)
    ·
      refine ⟨28005335495538061641394105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37340447327384082188525473 28005335495538061641394105)
      ·
        refine ⟨21004001621653546231045579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28005335495538061641394105 21004001621653546231045579)
        ·
          refine ⟨31506002432480319346568369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21004001621653546231045579 31506002432480319346568369)
          ·
            refine ⟨23629501824360239509926277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31506002432480319346568369 23629501824360239509926277)
            ·
              refine ⟨4430531592067544908111177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23629501824360239509926277 4430531592067544908111177)
              ·
                refine ⟨3322898694050658681083383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4430531592067544908111177 3322898694050658681083383)
                ·
                  refine ⟨4984348041075988021625075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3322898694050658681083383 4984348041075988021625075)
                  ·
                    refine ⟨7476522061613982032437613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4984348041075988021625075 7476522061613982032437613)
                    ·
                      refine ⟨2803695773105243262164105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7476522061613982032437613 2803695773105243262164105)
                      ·
                        rfl

theorem cell23_5460178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 4, 2, 1, 1, 3].length) (baseStart_5460178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460178 prefixEnd_5460178 := by exact prefixLift 5460178
  have htrace : WordTrace (prefixWord ++ tailWord_5460178) baseStart_5460178 baseEnd_5460178 := by
    simpa [prefixWord, tailWord_5460178, baseEnd_5460178] using wordTrace_append hprefix tailTrace_5460178
  have hstable : (prefixWord ++ tailWord_5460178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460178).length < 2 ^ (prefixWord ++ tailWord_5460178).sum := by decide
  have hdescent : baseEnd_5460178 < baseStart_5460178 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460197 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 1, 2, 4]
def baseStart_5460197 : Nat := 118140960795 + 5460197 * 2 ^ 59
def prefixEnd_5460197 : Nat := 4983230072969 + 3 ^ 40 * 5460197 * 2
def baseEnd_5460197 : Nat := 2803705529237678687826517

theorem tailTrace_5460197 : CollatzResearch.WordTrace tailWord_5460197 prefixEnd_5460197 2803705529237678687826517 := by
  unfold tailWord_5460197
  simp only [CollatzResearch.WordTrace]
  refine ⟨199149745399646271250410845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132766496933097514166940563 199149745399646271250410845)
  ·
    refine ⟨74681154524867351718904067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199149745399646271250410845 74681154524867351718904067)
    ·
      refine ⟨112021731787301027578356101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74681154524867351718904067 112021731787301027578356101)
      ·
        refine ⟨21004074710118942670941769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112021731787301027578356101 21004074710118942670941769)
        ·
          refine ⟨15753056032589207003206327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21004074710118942670941769 15753056032589207003206327)
          ·
            refine ⟨23629584048883810504809491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15753056032589207003206327 23629584048883810504809491)
            ·
              refine ⟨35444376073325715757214237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23629584048883810504809491 35444376073325715757214237)
              ·
                refine ⟨13291641027497143408955339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35444376073325715757214237 13291641027497143408955339)
                ·
                  refine ⟨19937461541245715113433009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13291641027497143408955339 19937461541245715113433009)
                  ·
                    refine ⟨14953096155934286335074757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19937461541245715113433009 14953096155934286335074757)
                    ·
                      refine ⟨2803705529237678687826517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14953096155934286335074757 2803705529237678687826517)
                      ·
                        rfl

theorem cell23_5460197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_5460197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460197 prefixEnd_5460197 := by exact prefixLift 5460197
  have htrace : WordTrace (prefixWord ++ tailWord_5460197) baseStart_5460197 baseEnd_5460197 := by
    simpa [prefixWord, tailWord_5460197, baseEnd_5460197] using wordTrace_append hprefix tailTrace_5460197
  have hstable : (prefixWord ++ tailWord_5460197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460197).length < 2 ^ (prefixWord ++ tailWord_5460197).sum := by decide
  have hdescent : baseEnd_5460197 < baseStart_5460197 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460207 : List Nat := [1, 1, 2, 1, 6, 2, 3, 7]
def baseStart_5460207 : Nat := 118140960795 + 5460207 * 2 ^ 59
def prefixEnd_5460207 : Nat := 4983230072969 + 3 ^ 40 * 5460207 * 2
def baseEnd_5460207 : Nat := 103841135705341616618573

theorem tailTrace_5460207 : CollatzResearch.WordTrace tailWord_5460207 prefixEnd_5460207 103841135705341616618573 := by
  unfold tailWord_5460207
  simp only [CollatzResearch.WordTrace]
  refine ⟨199150110129610042958274875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132766740086406695305516583 199150110129610042958274875)
  ·
    refine ⟨298725165194415064437412313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199150110129610042958274875 298725165194415064437412313)
    ·
      refine ⟨224043873895811298328059235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298725165194415064437412313 224043873895811298328059235)
      ·
        refine ⟨336065810843716947492088853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224043873895811298328059235 336065810843716947492088853)
        ·
          refine ⟨15753084883299231913691665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 336065810843716947492088853 15753084883299231913691665)
          ·
            refine ⟨11814813662474423935268749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15753084883299231913691665 11814813662474423935268749)
            ·
              refine ⟨4430555123427908975725781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11814813662474423935268749 4430555123427908975725781)
              ·
                refine ⟨103841135705341616618573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4430555123427908975725781 103841135705341616618573)
                ·
                  rfl

theorem cell23_5460207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 3, 7].length) (baseStart_5460207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460207 prefixEnd_5460207 := by exact prefixLift 5460207
  have htrace : WordTrace (prefixWord ++ tailWord_5460207) baseStart_5460207 baseEnd_5460207 := by
    simpa [prefixWord, tailWord_5460207, baseEnd_5460207] using wordTrace_append hprefix tailTrace_5460207
  have hstable : (prefixWord ++ tailWord_5460207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460207).length < 2 ^ (prefixWord ++ tailWord_5460207).sum := by decide
  have hdescent : baseEnd_5460207 < baseStart_5460207 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460218 : List Nat := [3, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2]
def baseStart_5460218 : Nat := 118140960795 + 5460218 * 2 ^ 59
def prefixEnd_5460218 : Nat := 4983230072969 + 3 ^ 40 * 5460218 * 2
def baseEnd_5460218 : Nat := 2803716312331423105663921

theorem tailTrace_5460218 : CollatzResearch.WordTrace tailWord_5460218 prefixEnd_5460218 2803716312331423105663921 := by
  unfold tailWord_5460218
  simp only [CollatzResearch.WordTrace]
  refine ⟨49787627833142547959231327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132767007555046794557950205 49787627833142547959231327)
  ·
    refine ⟨74681441749713821938846991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49787627833142547959231327 74681441749713821938846991)
    ·
      refine ⟨112022162624570732908270487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74681441749713821938846991 112022162624570732908270487)
      ·
        refine ⟨168033243936856099362405731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112022162624570732908270487 168033243936856099362405731)
        ·
          refine ⟨252049865905284149043608597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168033243936856099362405731 252049865905284149043608597)
          ·
            refine ⟨11814837464310194486419153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 252049865905284149043608597 11814837464310194486419153)
            ·
              refine ⟨8861128098232645864814365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11814837464310194486419153 8861128098232645864814365)
              ·
                refine ⟨3322923036837242199305387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8861128098232645864814365 3322923036837242199305387)
                ·
                  refine ⟨4984384555255863298958081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3322923036837242199305387 4984384555255863298958081)
                  ·
                    refine ⟨3738288416441897474218561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4984384555255863298958081 3738288416441897474218561)
                    ·
                      refine ⟨2803716312331423105663921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738288416441897474218561 2803716312331423105663921)
                      ·
                        rfl

theorem cell23_5460218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 2, 3, 1, 2, 2].length) (baseStart_5460218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460218 prefixEnd_5460218 := by exact prefixLift 5460218
  have htrace : WordTrace (prefixWord ++ tailWord_5460218) baseStart_5460218 baseEnd_5460218 := by
    simpa [prefixWord, tailWord_5460218, baseEnd_5460218] using wordTrace_append hprefix tailTrace_5460218
  have hstable : (prefixWord ++ tailWord_5460218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460218).length < 2 ^ (prefixWord ++ tailWord_5460218).sum := by decide
  have hdescent : baseEnd_5460218 < baseStart_5460218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460228 : List Nat := [2, 3, 2, 2, 4, 1, 1, 2, 2, 4]
def baseStart_5460228 : Nat := 118140960795 + 5460228 * 2 ^ 59
def prefixEnd_5460228 : Nat := 4983230072969 + 3 ^ 40 * 5460228 * 2
def baseEnd_5460228 : Nat := 934573815712656022179625

theorem tailTrace_5460228 : CollatzResearch.WordTrace tailWord_5460228 prefixEnd_5460228 934573815712656022179625 := by
  unfold tailWord_5460228
  simp only [CollatzResearch.WordTrace]
  refine ⟨99575438031266981772394669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132767250708355975696526225 99575438031266981772394669)
  ·
    refine ⟨37340789261725118164648001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99575438031266981772394669 37340789261725118164648001)
    ·
      refine ⟨28005591946293838623486001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37340789261725118164648001 28005591946293838623486001)
      ·
        refine ⟨21004193959720378967614501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28005591946293838623486001 21004193959720378967614501)
        ·
          refine ⟨3938286367447571056427719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21004193959720378967614501 3938286367447571056427719)
          ·
            refine ⟨5907429551171356584641579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3938286367447571056427719 5907429551171356584641579)
            ·
              refine ⟨8861144326757034876962369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5907429551171356584641579 8861144326757034876962369)
              ·
                refine ⟨6645858245067776157721777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8861144326757034876962369 6645858245067776157721777)
                ·
                  refine ⟨4984393683800832118291333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6645858245067776157721777 4984393683800832118291333)
                  ·
                    refine ⟨934573815712656022179625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4984393683800832118291333 934573815712656022179625)
                    ·
                      rfl

theorem cell23_5460228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_5460228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460228 prefixEnd_5460228 := by exact prefixLift 5460228
  have htrace : WordTrace (prefixWord ++ tailWord_5460228) baseStart_5460228 baseEnd_5460228 := by
    simpa [prefixWord, tailWord_5460228, baseEnd_5460228] using wordTrace_append hprefix tailTrace_5460228
  have hstable : (prefixWord ++ tailWord_5460228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460228).length < 2 ^ (prefixWord ++ tailWord_5460228).sum := by decide
  have hdescent : baseEnd_5460228 < baseStart_5460228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460269 : List Nat := [1, 5, 3, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_5460269 : Nat := 118140960795 + 5460269 * 2 ^ 59
def prefixEnd_5460269 : Nat := 4983230072969 + 3 ^ 40 * 5460269 * 2
def baseEnd_5460269 : Nat := 2803742499844802406126187

theorem tailTrace_5460269 : CollatzResearch.WordTrace tailWord_5460269 prefixEnd_5460269 2803742499844802406126187 := by
  unfold tailWord_5460269
  simp only [CollatzResearch.WordTrace]
  refine ⟨199152371455385427547031861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132768247636923618364687907 199152371455385427547031861)
  ·
    refine ⟨18670534823942383832534237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199152371455385427547031861 18670534823942383832534237)
    ·
      refine ⟨7001450558978393937200339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18670534823942383832534237 7001450558978393937200339)
      ·
        refine ⟨10502175838467590905800509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7001450558978393937200339 10502175838467590905800509)
        ·
          refine ⟨3938315939425346589675191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10502175838467590905800509 3938315939425346589675191)
          ·
            refine ⟨5907473909138019884512787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3938315939425346589675191 5907473909138019884512787)
            ·
              refine ⟨8861210863707029826769181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5907473909138019884512787 8861210863707029826769181)
              ·
                refine ⟨3322954073890136185038443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8861210863707029826769181 3322954073890136185038443)
                ·
                  refine ⟨4984431110835204277557665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3322954073890136185038443 4984431110835204277557665)
                  ·
                    refine ⟨3738323333126403208168249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4984431110835204277557665 3738323333126403208168249)
                    ·
                      refine ⟨2803742499844802406126187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738323333126403208168249 2803742499844802406126187)
                      ·
                        rfl

theorem cell23_5460269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_5460269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460269 prefixEnd_5460269 := by exact prefixLift 5460269
  have htrace : WordTrace (prefixWord ++ tailWord_5460269) baseStart_5460269 baseEnd_5460269 := by
    simpa [prefixWord, tailWord_5460269, baseEnd_5460269] using wordTrace_append hprefix tailTrace_5460269
  have hstable : (prefixWord ++ tailWord_5460269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460269).length < 2 ^ (prefixWord ++ tailWord_5460269).sum := by decide
  have hdescent : baseEnd_5460269 < baseStart_5460269 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460277 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_5460277 : Nat := 118140960795 + 5460277 * 2 ^ 59
def prefixEnd_5460277 : Nat := 4983230072969 + 3 ^ 40 * 5460277 * 2
def baseEnd_5460277 : Nat := 2803746607690038374826149

theorem tailTrace_5460277 : CollatzResearch.WordTrace tailWord_5460277 prefixEnd_5460277 2803746607690038374826149 := by
  unfold tailWord_5460277
  simp only [CollatzResearch.WordTrace]
  refine ⟨199152663239356444913323085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132768442159570963275548723 199152663239356444913323085)
  ·
    refine ⟨74682248714758666842496157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199152663239356444913323085 74682248714758666842496157)
    ·
      refine ⟨28005843268034500065936059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74682248714758666842496157 28005843268034500065936059)
      ·
        refine ⟨42008764902051750098904089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28005843268034500065936059 42008764902051750098904089)
        ·
          refine ⟨31506573676538812574178067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42008764902051750098904089 31506573676538812574178067)
          ·
            refine ⟨47259860514808218861267101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31506573676538812574178067 47259860514808218861267101)
            ·
              refine ⟨17722447693053082072975163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47259860514808218861267101 17722447693053082072975163)
              ·
                refine ⟨26583671539579623109462745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17722447693053082072975163 26583671539579623109462745)
                ·
                  refine ⟨19937753654684717332097059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26583671539579623109462745 19937753654684717332097059)
                  ·
                    refine ⟨29906630482027075998145589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19937753654684717332097059 29906630482027075998145589)
                    ·
                      refine ⟨2803746607690038374826149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29906630482027075998145589 2803746607690038374826149)
                      ·
                        rfl

theorem cell23_5460277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_5460277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460277 prefixEnd_5460277 := by exact prefixLift 5460277
  have htrace : WordTrace (prefixWord ++ tailWord_5460277) baseStart_5460277 baseEnd_5460277 := by
    simpa [prefixWord, tailWord_5460277, baseEnd_5460277] using wordTrace_append hprefix tailTrace_5460277
  have hstable : (prefixWord ++ tailWord_5460277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460277).length < 2 ^ (prefixWord ++ tailWord_5460277).sum := by decide
  have hdescent : baseEnd_5460277 < baseStart_5460277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460280 : List Nat := [2, 1, 2, 1, 3, 1, 2, 2, 9]
def baseStart_5460280 : Nat := 118140960795 + 5460280 * 2 ^ 59
def prefixEnd_5460280 : Nat := 4983230072969 + 3 ^ 40 * 5460280 * 2
def baseEnd_5460280 : Nat := 311527572014666873676515

theorem tailTrace_5460280 : CollatzResearch.WordTrace tailWord_5460280 prefixEnd_5460280 311527572014666873676515 := by
  unfold tailWord_5460280
  simp only [CollatzResearch.WordTrace]
  refine ⟨99576386329172788212841147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132768515105563717617121529 99576386329172788212841147)
  ·
    refine ⟨149364579493759182319261721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99576386329172788212841147 149364579493759182319261721)
    ·
      refine ⟨112023434620319386739446291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149364579493759182319261721 112023434620319386739446291)
      ·
        refine ⟨168035151930479080109169437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112023434620319386739446291 168035151930479080109169437)
        ·
          refine ⟨63013181973929655040938539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168035151930479080109169437 63013181973929655040938539)
          ·
            refine ⟨94519772960894482561407809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63013181973929655040938539 94519772960894482561407809)
            ·
              refine ⟨70889829720670861921055857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94519772960894482561407809 70889829720670861921055857)
              ·
                refine ⟨53167372290503146440791893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70889829720670861921055857 53167372290503146440791893)
                ·
                  refine ⟨311527572014666873676515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53167372290503146440791893 311527572014666873676515)
                  ·
                    rfl

theorem cell23_5460280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 2, 9].length) (baseStart_5460280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460280 prefixEnd_5460280 := by exact prefixLift 5460280
  have htrace : WordTrace (prefixWord ++ tailWord_5460280) baseStart_5460280 baseEnd_5460280 := by
    simpa [prefixWord, tailWord_5460280, baseEnd_5460280] using wordTrace_append hprefix tailTrace_5460280
  have hstable : (prefixWord ++ tailWord_5460280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460280).length < 2 ^ (prefixWord ++ tailWord_5460280).sum := by decide
  have hdescent : baseEnd_5460280 < baseStart_5460280 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460308 : List Nat := [2, 4, 1, 1, 2, 3, 1, 3, 2, 2, 2]
def baseStart_5460308 : Nat := 118140960795 + 5460308 * 2 ^ 59
def prefixEnd_5460308 : Nat := 4983230072969 + 3 ^ 40 * 5460308 * 2
def baseEnd_5460308 : Nat := 2803762525590327753538507

theorem tailTrace_5460308 : CollatzResearch.WordTrace tailWord_5460308 prefixEnd_5460308 2803762525590327753538507 := by
  unfold tailWord_5460308
  simp only [CollatzResearch.WordTrace]
  refine ⟨99576896951122068603850789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132769195934829424805134385 99576896951122068603850789)
  ·
    refine ⟨18670668178335387863222023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99576896951122068603850789 18670668178335387863222023)
    ·
      refine ⟨28006002267503081794833035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18670668178335387863222023 28006002267503081794833035)
      ·
        refine ⟨42009003401254622692249553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28006002267503081794833035 42009003401254622692249553)
        ·
          refine ⟨31506752550940967019187165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42009003401254622692249553 31506752550940967019187165)
          ·
            refine ⟨11815032206602862632195187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31506752550940967019187165 11815032206602862632195187)
            ·
              refine ⟨17722548309904293948292781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11815032206602862632195187 17722548309904293948292781)
              ·
                refine ⟨6645955616214110230609793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17722548309904293948292781 6645955616214110230609793)
                ·
                  refine ⟨4984466712160582672957345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6645955616214110230609793 4984466712160582672957345)
                  ·
                    refine ⟨3738350034120437004718009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4984466712160582672957345 3738350034120437004718009)
                    ·
                      refine ⟨2803762525590327753538507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738350034120437004718009 2803762525590327753538507)
                      ·
                        rfl

theorem cell23_5460308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 1, 3, 2, 2, 2].length) (baseStart_5460308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460308 prefixEnd_5460308 := by exact prefixLift 5460308
  have htrace : WordTrace (prefixWord ++ tailWord_5460308) baseStart_5460308 baseEnd_5460308 := by
    simpa [prefixWord, tailWord_5460308, baseEnd_5460308] using wordTrace_append hprefix tailTrace_5460308
  have hstable : (prefixWord ++ tailWord_5460308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460308).length < 2 ^ (prefixWord ++ tailWord_5460308).sum := by decide
  have hdescent : baseEnd_5460308 < baseStart_5460308 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460342 : List Nat := [5, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2]
def baseStart_5460342 : Nat := 118140960795 + 5460342 * 2 ^ 59
def prefixEnd_5460342 : Nat := 4983230072969 + 3 ^ 40 * 5460342 * 2
def baseEnd_5460342 : Nat := 2803779983932580620513351

theorem tailTrace_5460342 : CollatzResearch.WordTrace tailWord_5460342 prefixEnd_5460342 2803779983932580620513351 := by
  unfold tailWord_5460342
  simp only [CollatzResearch.WordTrace]
  refine ⟨12447189624007560063402455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132770022656080640676292853 12447189624007560063402455)
  ·
    refine ⟨18670784436011340095103683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12447189624007560063402455 18670784436011340095103683)
    ·
      refine ⟨28006176654017010142655525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18670784436011340095103683 28006176654017010142655525)
      ·
        refine ⟨5251158122628189401747911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28006176654017010142655525 5251158122628189401747911)
        ·
          refine ⟨7876737183942284102621867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5251158122628189401747911 7876737183942284102621867)
          ·
            refine ⟨11815105775913426153932801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7876737183942284102621867 11815105775913426153932801)
            ·
              refine ⟨8861329331935069615449601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11815105775913426153932801 8861329331935069615449601)
              ·
                refine ⟨6645996998951302211587201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8861329331935069615449601 6645996998951302211587201)
                ·
                  refine ⟨4984497749213476658690401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6645996998951302211587201 4984497749213476658690401)
                  ·
                    refine ⟨3738373311910107494017801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4984497749213476658690401 3738373311910107494017801)
                    ·
                      refine ⟨2803779983932580620513351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738373311910107494017801 2803779983932580620513351)
                      ·
                        rfl

theorem cell23_5460342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_5460342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460342 prefixEnd_5460342 := by exact prefixLift 5460342
  have htrace : WordTrace (prefixWord ++ tailWord_5460342) baseStart_5460342 baseEnd_5460342 := by
    simpa [prefixWord, tailWord_5460342, baseEnd_5460342] using wordTrace_append hprefix tailTrace_5460342
  have hstable : (prefixWord ++ tailWord_5460342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460342).length < 2 ^ (prefixWord ++ tailWord_5460342).sum := by decide
  have hdescent : baseEnd_5460342 < baseStart_5460342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460364 : List Nat := [2, 2, 1, 2, 1, 4, 1, 1, 1, 6, 2]
def baseStart_5460364 : Nat := 118140960795 + 5460364 * 2 ^ 59
def prefixEnd_5460364 : Nat := 4983230072969 + 3 ^ 40 * 5460364 * 2
def baseEnd_5460364 : Nat := 2803791280506979534438249

theorem tailTrace_5460364 : CollatzResearch.WordTrace tailWord_5460364 prefixEnd_5460364 2803791280506979534438249 := by
  unfold tailWord_5460364
  simp only [CollatzResearch.WordTrace]
  refine ⟨99577918195020629385870073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132770557593360839181160097 99577918195020629385870073)
  ·
    refine ⟨74683438646265472039402555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99577918195020629385870073 74683438646265472039402555)
    ·
      refine ⟨112025157969398208059103833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74683438646265472039402555 112025157969398208059103833)
      ·
        refine ⟨84018868477048656044327875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112025157969398208059103833 84018868477048656044327875)
        ·
          refine ⟨126028302715572984066491813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84018868477048656044327875 126028302715572984066491813)
          ·
            refine ⟨23630306759169934512467215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126028302715572984066491813 23630306759169934512467215)
            ·
              refine ⟨35445460138754901768700823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23630306759169934512467215 35445460138754901768700823)
              ·
                refine ⟨53168190208132352653051235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35445460138754901768700823 53168190208132352653051235)
                ·
                  refine ⟨79752285312198528979576853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53168190208132352653051235 79752285312198528979576853)
                  ·
                    refine ⟨3738388374009306045917665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79752285312198528979576853 3738388374009306045917665)
                    ·
                      refine ⟨2803791280506979534438249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738388374009306045917665 2803791280506979534438249)
                      ·
                        rfl

theorem cell23_5460364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 1, 6, 2].length) (baseStart_5460364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460364 prefixEnd_5460364 := by exact prefixLift 5460364
  have htrace : WordTrace (prefixWord ++ tailWord_5460364) baseStart_5460364 baseEnd_5460364 := by
    simpa [prefixWord, tailWord_5460364, baseEnd_5460364] using wordTrace_append hprefix tailTrace_5460364
  have hstable : (prefixWord ++ tailWord_5460364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460364).length < 2 ^ (prefixWord ++ tailWord_5460364).sum := by decide
  have hdescent : baseEnd_5460364 < baseStart_5460364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460384 : List Nat := [2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 3]
def baseStart_5460384 : Nat := 118140960795 + 5460384 * 2 ^ 59
def prefixEnd_5460384 : Nat := 4983230072969 + 3 ^ 40 * 5460384 * 2
def baseEnd_5460384 : Nat := 2803801550120069456188157

theorem tailTrace_5460384 : CollatzResearch.WordTrace tailWord_5460384 prefixEnd_5460384 2803801550120069456188157 := by
  unfold tailWord_5460384
  simp only [CollatzResearch.WordTrace]
  refine ⟨99578282924984401093734103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132771043899979201458312137 99578282924984401093734103)
  ·
    refine ⟨149367424387476601640601155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99578282924984401093734103 149367424387476601640601155)
    ·
      refine ⟨224051136581214902460901733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149367424387476601640601155 224051136581214902460901733)
      ·
        refine ⟨42009588108977794211419075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224051136581214902460901733 42009588108977794211419075)
        ·
          refine ⟨63014382163466691317128613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42009588108977794211419075 63014382163466691317128613)
          ·
            refine ⟨11815196655650004621961615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63014382163466691317128613 11815196655650004621961615)
            ·
              refine ⟨17722794983475006932942423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11815196655650004621961615 17722794983475006932942423)
              ·
                refine ⟨26584192475212510399413635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17722794983475006932942423 26584192475212510399413635)
                ·
                  refine ⟨39876288712818765599120453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26584192475212510399413635 39876288712818765599120453)
                  ·
                    refine ⟨7476804133653518549835085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39876288712818765599120453 7476804133653518549835085)
                    ·
                      refine ⟨2803801550120069456188157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7476804133653518549835085 2803801550120069456188157)
                      ·
                        rfl

theorem cell23_5460384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_5460384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460384 prefixEnd_5460384 := by exact prefixLift 5460384
  have htrace : WordTrace (prefixWord ++ tailWord_5460384) baseStart_5460384 baseEnd_5460384 := by
    simpa [prefixWord, tailWord_5460384, baseEnd_5460384] using wordTrace_append hprefix tailTrace_5460384
  have hstable : (prefixWord ++ tailWord_5460384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460384).length < 2 ^ (prefixWord ++ tailWord_5460384).sum := by decide
  have hdescent : baseEnd_5460384 < baseStart_5460384 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460407 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_5460407 : Nat := 118140960795 + 5460407 * 2 ^ 59
def prefixEnd_5460407 : Nat := 4983230072969 + 3 ^ 40 * 5460407 * 2
def baseEnd_5460407 : Nat := 2803813360175122866200551

theorem tailTrace_5460407 : CollatzResearch.WordTrace tailWord_5460407 prefixEnd_5460407 2803813360175122866200551 := by
  unfold tailWord_5460407
  simp only [CollatzResearch.WordTrace]
  refine ⟨199157404728885477115555475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132771603152590318077036983 199157404728885477115555475)
  ·
    refine ⟨298736107093328215673333213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199157404728885477115555475 298736107093328215673333213)
    ·
      refine ⟨112026040159998080877499955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298736107093328215673333213 112026040159998080877499955)
      ·
        refine ⟨168039060239997121316249933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112026040159998080877499955 168039060239997121316249933)
        ·
          refine ⟨63014647589998920493593725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168039060239997121316249933 63014647589998920493593725)
          ·
            refine ⟨23630492846249595185097647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63014647589998920493593725 23630492846249595185097647)
            ·
              refine ⟨35445739269374392777646471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23630492846249595185097647 35445739269374392777646471)
              ·
                refine ⟨53168608904061589166469707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35445739269374392777646471 53168608904061589166469707)
                ·
                  refine ⟨79752913356092383749704561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53168608904061589166469707 79752913356092383749704561)
                  ·
                    refine ⟨59814685017069287812278421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79752913356092383749704561 59814685017069287812278421)
                    ·
                      refine ⟨2803813360175122866200551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59814685017069287812278421 2803813360175122866200551)
                      ·
                        rfl

theorem cell23_5460407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_5460407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460407 prefixEnd_5460407 := by exact prefixLift 5460407
  have htrace : WordTrace (prefixWord ++ tailWord_5460407) baseStart_5460407 baseEnd_5460407 := by
    simpa [prefixWord, tailWord_5460407, baseEnd_5460407] using wordTrace_append hprefix tailTrace_5460407
  have hstable : (prefixWord ++ tailWord_5460407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460407).length < 2 ^ (prefixWord ++ tailWord_5460407).sum := by decide
  have hdescent : baseEnd_5460407 < baseStart_5460407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460441 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 2, 3, 2]
def baseStart_5460441 : Nat := 118140960795 + 5460441 * 2 ^ 59
def prefixEnd_5460441 : Nat := 4983230072969 + 3 ^ 40 * 5460441 * 2
def baseEnd_5460441 : Nat := 2803830818517375733175395

theorem tailTrace_5460441 : CollatzResearch.WordTrace tailWord_5460441 prefixEnd_5460441 2803830818517375733175395 := by
  unfold tailWord_5460441
  simp only [CollatzResearch.WordTrace]
  refine ⟨199158644810762300922293177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132772429873841533948195451 199158644810762300922293177)
  ·
    refine ⟨149368983608071725691719883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199158644810762300922293177 149368983608071725691719883)
    ·
      refine ⟨224053475412107588537579825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149368983608071725691719883 224053475412107588537579825)
      ·
        refine ⟨168040106559080691403184869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224053475412107588537579825 168040106559080691403184869)
        ·
          refine ⟨31507519979827629638097163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168040106559080691403184869 31507519979827629638097163)
          ·
            refine ⟨47261279969741444457145745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31507519979827629638097163 47261279969741444457145745)
            ·
              refine ⟨35445959977306083342859309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47261279969741444457145745 35445959977306083342859309)
              ·
                refine ⟨13292234991489781253572241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35445959977306083342859309 13292234991489781253572241)
                ·
                  refine ⟨9969176243617335940179181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13292234991489781253572241 9969176243617335940179181)
                  ·
                    refine ⟨3738441091356500977567193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9969176243617335940179181 3738441091356500977567193)
                    ·
                      refine ⟨2803830818517375733175395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738441091356500977567193 2803830818517375733175395)
                      ·
                        rfl

theorem cell23_5460441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 2, 3, 2].length) (baseStart_5460441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460441 prefixEnd_5460441 := by exact prefixLift 5460441
  have htrace : WordTrace (prefixWord ++ tailWord_5460441) baseStart_5460441 baseEnd_5460441 := by
    simpa [prefixWord, tailWord_5460441, baseEnd_5460441] using wordTrace_append hprefix tailTrace_5460441
  have hstable : (prefixWord ++ tailWord_5460441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460441).length < 2 ^ (prefixWord ++ tailWord_5460441).sum := by decide
  have hdescent : baseEnd_5460441 < baseStart_5460441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460458 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_5460458 : Nat := 118140960795 + 5460458 * 2 ^ 59
def prefixEnd_5460458 : Nat := 4983230072969 + 3 ^ 40 * 5460458 * 2
def baseEnd_5460458 : Nat := 2803839547688502166662817

theorem tailTrace_5460458 : CollatzResearch.WordTrace tailWord_5460458 prefixEnd_5460458 2803839547688502166662817 := by
  unfold tailWord_5460458
  simp only [CollatzResearch.WordTrace]
  refine ⟨49789816212925178206415507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132772843234467141883774685 49789816212925178206415507)
  ·
    refine ⟨74684724319387767309623261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49789816212925178206415507 74684724319387767309623261)
    ·
      refine ⟨28006771619770412741108723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74684724319387767309623261 28006771619770412741108723)
      ·
        refine ⟨42010157429655619111663085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28006771619770412741108723 42010157429655619111663085)
        ·
          refine ⟨15753809036120857166873657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42010157429655619111663085 15753809036120857166873657)
          ·
            refine ⟨11815356777090642875155243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15753809036120857166873657 11815356777090642875155243)
            ·
              refine ⟨17723035165635964312732865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11815356777090642875155243 17723035165635964312732865)
              ·
                refine ⟨13292276374226973234549649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17723035165635964312732865 13292276374226973234549649)
                ·
                  refine ⟨9969207280670229925912237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13292276374226973234549649 9969207280670229925912237)
                  ·
                    refine ⟨3738452730251336222217089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9969207280670229925912237 3738452730251336222217089)
                    ·
                      refine ⟨2803839547688502166662817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738452730251336222217089 2803839547688502166662817)
                      ·
                        rfl

theorem cell23_5460458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_5460458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460458 prefixEnd_5460458 := by exact prefixLift 5460458
  have htrace : WordTrace (prefixWord ++ tailWord_5460458) baseStart_5460458 baseEnd_5460458 := by
    simpa [prefixWord, tailWord_5460458, baseEnd_5460458] using wordTrace_append hprefix tailTrace_5460458
  have hstable : (prefixWord ++ tailWord_5460458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460458).length < 2 ^ (prefixWord ++ tailWord_5460458).sum := by decide
  have hdescent : baseEnd_5460458 < baseStart_5460458 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460464 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 4, 4]
def baseStart_5460464 : Nat := 118140960795 + 5460464 * 2 ^ 59
def prefixEnd_5460464 : Nat := 4983230072969 + 3 ^ 40 * 5460464 * 2
def baseEnd_5460464 : Nat := 934614209524143047729263

theorem tailTrace_5460464 : CollatzResearch.WordTrace tailWord_5460464 prefixEnd_5460464 934614209524143047729263 := by
  unfold tailWord_5460464
  simp only [CollatzResearch.WordTrace]
  refine ⟨99579741844839487925190223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132772989126452650566920297 99579741844839487925190223)
  ·
    refine ⟨149369612767259231887785335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99579741844839487925190223 149369612767259231887785335)
    ·
      refine ⟨224054419150888847831678003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149369612767259231887785335 224054419150888847831678003)
      ·
        refine ⟨336081628726333271747517005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224054419150888847831678003 336081628726333271747517005)
        ·
          refine ⟨126030610772374976905318877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336081628726333271747517005 126030610772374976905318877)
          ·
            refine ⟨47261479039640616339494579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126030610772374976905318877 47261479039640616339494579)
            ·
              refine ⟨70892218559460924509241869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47261479039640616339494579 70892218559460924509241869)
              ·
                refine ⟨26584581959797846690965701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70892218559460924509241869 26584581959797846690965701)
                ·
                  refine ⟨4984609117462096254556069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26584581959797846690965701 4984609117462096254556069)
                  ·
                    refine ⟨934614209524143047729263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4984609117462096254556069 934614209524143047729263)
                    ·
                      rfl

theorem cell23_5460464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 4, 4].length) (baseStart_5460464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460464 prefixEnd_5460464 := by exact prefixLift 5460464
  have htrace : WordTrace (prefixWord ++ tailWord_5460464) baseStart_5460464 baseEnd_5460464 := by
    simpa [prefixWord, tailWord_5460464, baseEnd_5460464] using wordTrace_append hprefix tailTrace_5460464
  have hstable : (prefixWord ++ tailWord_5460464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460464).length < 2 ^ (prefixWord ++ tailWord_5460464).sum := by decide
  have hdescent : baseEnd_5460464 < baseStart_5460464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460465 : List Nat := [1, 2, 2, 2, 3, 1, 5, 2, 1, 1, 3]
def baseStart_5460465 : Nat := 118140960795 + 5460465 * 2 ^ 59
def prefixEnd_5460465 : Nat := 4983230072969 + 3 ^ 40 * 5460465 * 2
def baseEnd_5460465 : Nat := 2803843142053083639275285

theorem tailTrace_5460465 : CollatzResearch.WordTrace tailWord_5460465 prefixEnd_5460465 2803843142053083639275285 := by
  unfold tailWord_5460465
  simp only [CollatzResearch.WordTrace]
  refine ⟨199159520162675353021166849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132773013441783568680777899 199159520162675353021166849)
  ·
    refine ⟨149369640122006514765875137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199159520162675353021166849 149369640122006514765875137)
    ·
      refine ⟨112027230091504886074406353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149369640122006514765875137 112027230091504886074406353)
      ·
        refine ⟨84020422568628664555804765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112027230091504886074406353 84020422568628664555804765)
        ·
          refine ⟨31507658463235749208426787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84020422568628664555804765 31507658463235749208426787)
          ·
            refine ⟨47261487694853623812640181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31507658463235749208426787 47261487694853623812640181)
            ·
              refine ⟨4430764471392527232435017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47261487694853623812640181 4430764471392527232435017)
              ·
                refine ⟨3323073353544395424326263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4430764471392527232435017 3323073353544395424326263)
                ·
                  refine ⟨4984610030316593136489395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3323073353544395424326263 4984610030316593136489395)
                  ·
                    refine ⟨7476915045474889704734093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4984610030316593136489395 7476915045474889704734093)
                    ·
                      refine ⟨2803843142053083639275285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7476915045474889704734093 2803843142053083639275285)
                      ·
                        rfl

theorem cell23_5460465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 5, 2, 1, 1, 3].length) (baseStart_5460465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460465 prefixEnd_5460465 := by exact prefixLift 5460465
  have htrace : WordTrace (prefixWord ++ tailWord_5460465) baseStart_5460465 baseEnd_5460465 := by
    simpa [prefixWord, tailWord_5460465, baseEnd_5460465] using wordTrace_append hprefix tailTrace_5460465
  have hstable : (prefixWord ++ tailWord_5460465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460465).length < 2 ^ (prefixWord ++ tailWord_5460465).sum := by decide
  have hdescent : baseEnd_5460465 < baseStart_5460465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460467 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 6]
def baseStart_5460467 : Nat := 118140960795 + 5460467 * 2 ^ 59
def prefixEnd_5460467 : Nat := 4983230072969 + 3 ^ 40 * 5460467 * 2
def baseEnd_5460467 : Nat := 2803844169014392631450275

theorem tailTrace_5460467 : CollatzResearch.WordTrace tailWord_5460467 prefixEnd_5460467 2803844169014392631450275 := by
  unfold tailWord_5460467
  simp only [CollatzResearch.WordTrace]
  refine ⟨199159593108668107362739655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132773062072445404908493103 199159593108668107362739655)
  ·
    refine ⟨298739389663002161044109483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199159593108668107362739655 298739389663002161044109483)
    ·
      refine ⟨448109084494503241566164225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298739389663002161044109483 448109084494503241566164225)
      ·
        refine ⟨336081813370877431174623169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448109084494503241566164225 336081813370877431174623169)
        ·
          refine ⟨252061360028158073380967377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336081813370877431174623169 252061360028158073380967377)
          ·
            refine ⟨189046020021118555035725533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252061360028158073380967377 189046020021118555035725533)
            ·
              refine ⟨70892257507919458138397075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189046020021118555035725533 70892257507919458138397075)
              ·
                refine ⟨106338386261879187207595613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70892257507919458138397075 106338386261879187207595613)
                ·
                  refine ⟨39876894848204695202848355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106338386261879187207595613 39876894848204695202848355)
                  ·
                    refine ⟨59815342272307042804272533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39876894848204695202848355 59815342272307042804272533)
                    ·
                      refine ⟨2803844169014392631450275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59815342272307042804272533 2803844169014392631450275)
                      ·
                        rfl

theorem cell23_5460467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_5460467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460467 prefixEnd_5460467 := by exact prefixLift 5460467
  have htrace : WordTrace (prefixWord ++ tailWord_5460467) baseStart_5460467 baseEnd_5460467 := by
    simpa [prefixWord, tailWord_5460467, baseEnd_5460467] using wordTrace_append hprefix tailTrace_5460467
  have hstable : (prefixWord ++ tailWord_5460467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460467).length < 2 ^ (prefixWord ++ tailWord_5460467).sum := by decide
  have hdescent : baseEnd_5460467 < baseStart_5460467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460491 : List Nat := [1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 3]
def baseStart_5460491 : Nat := 118140960795 + 5460491 * 2 ^ 59
def prefixEnd_5460491 : Nat := 4983230072969 + 3 ^ 40 * 5460491 * 2
def baseEnd_5460491 : Nat := 2803856492550100537550165

theorem tailTrace_5460491 : CollatzResearch.WordTrace tailWord_5460491 prefixEnd_5460491 2803856492550100537550165 := by
  unfold tailWord_5460491
  simp only [CollatzResearch.WordTrace]
  refine ⟨199160468460581159461613327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132773645640387439641075551 199160468460581159461613327)
  ·
    refine ⟨298740702690871739192419991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199160468460581159461613327 298740702690871739192419991)
    ·
      refine ⟨448111054036307608788629987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298740702690871739192419991 448111054036307608788629987)
      ·
        refine ⟨672166581054461413182944981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448111054036307608788629987 672166581054461413182944981)
        ·
          refine ⟨15753904243463939371475273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 672166581054461413182944981 15753904243463939371475273)
          ·
            refine ⟨11815428182597954528606455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15753904243463939371475273 11815428182597954528606455)
            ·
              refine ⟨17723142273896931792909683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11815428182597954528606455 17723142273896931792909683)
              ·
                refine ⟨26584713410845397689364525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17723142273896931792909683 26584713410845397689364525)
                ·
                  refine ⟨9969267529067024133511697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26584713410845397689364525 9969267529067024133511697)
                  ·
                    refine ⟨7476950646800268100133773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9969267529067024133511697 7476950646800268100133773)
                    ·
                      refine ⟨2803856492550100537550165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7476950646800268100133773 2803856492550100537550165)
                      ·
                        rfl

theorem cell23_5460491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 3].length) (baseStart_5460491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460491 prefixEnd_5460491 := by exact prefixLift 5460491
  have htrace : WordTrace (prefixWord ++ tailWord_5460491) baseStart_5460491 baseEnd_5460491 := by
    simpa [prefixWord, tailWord_5460491, baseEnd_5460491] using wordTrace_append hprefix tailTrace_5460491
  have hstable : (prefixWord ++ tailWord_5460491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460491).length < 2 ^ (prefixWord ++ tailWord_5460491).sum := by decide
  have hdescent : baseEnd_5460491 < baseStart_5460491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460494 : List Nat := [4, 1, 1, 2, 3, 1, 2, 9]
def baseStart_5460494 : Nat := 118140960795 + 5460494 * 2 ^ 59
def prefixEnd_5460494 : Nat := 4983230072969 + 3 ^ 40 * 5460494 * 2
def baseEnd_5460494 : Nat := 103846593814520889844913

theorem tailTrace_5460494 : CollatzResearch.WordTrace tailWord_5460494 prefixEnd_5460494 103846593814520889844913 := by
  unfold tailWord_5460494
  simp only [CollatzResearch.WordTrace]
  refine ⟨24895072234946286371746567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132773718586380193982648357 24895072234946286371746567)
  ·
    refine ⟨37342608352419429557619851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24895072234946286371746567 37342608352419429557619851)
    ·
      refine ⟨56013912528629144336429777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37342608352419429557619851 56013912528629144336429777)
      ·
        refine ⟨42010434396471858252322333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56013912528629144336429777 42010434396471858252322333)
        ·
          refine ⟨15753912898676946844620875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42010434396471858252322333 15753912898676946844620875)
          ·
            refine ⟨23630869348015420266931313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15753912898676946844620875 23630869348015420266931313)
            ·
              refine ⟨17723152011011565200198485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23630869348015420266931313 17723152011011565200198485)
              ·
                refine ⟨103846593814520889844913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17723152011011565200198485 103846593814520889844913)
                ·
                  rfl

theorem cell23_5460494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 9].length) (baseStart_5460494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460494 prefixEnd_5460494 := by exact prefixLift 5460494
  have htrace : WordTrace (prefixWord ++ tailWord_5460494) baseStart_5460494 baseEnd_5460494 := by
    simpa [prefixWord, tailWord_5460494, baseEnd_5460494] using wordTrace_append hprefix tailTrace_5460494
  have hstable : (prefixWord ++ tailWord_5460494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460494).length < 2 ^ (prefixWord ++ tailWord_5460494).sum := by decide
  have hdescent : baseEnd_5460494 < baseStart_5460494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460507 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 6, 7]
def baseStart_5460507 : Nat := 118140960795 + 5460507 * 2 ^ 59
def prefixEnd_5460507 : Nat := 4983230072969 + 3 ^ 40 * 5460507 * 2
def baseEnd_5460507 : Nat := 934621569413524158316697

theorem tailTrace_5460507 : CollatzResearch.WordTrace tailWord_5460507 prefixEnd_5460507 934621569413524158316697 := by
  unfold tailWord_5460507
  simp only [CollatzResearch.WordTrace]
  refine ⟨199161052028523194194195775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132774034685682129462797183 199161052028523194194195775)
  ·
    refine ⟨298741578042784791291293663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199161052028523194194195775 298741578042784791291293663)
    ·
      refine ⟨448112367064177186936940495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298741578042784791291293663 448112367064177186936940495)
      ·
        refine ⟨672168550596265780405410743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448112367064177186936940495 672168550596265780405410743)
        ·
          refine ⟨1008252825894398670608116115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672168550596265780405410743 1008252825894398670608116115)
          ·
            refine ⟨1512379238841598005912174173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1008252825894398670608116115 1512379238841598005912174173)
            ·
              refine ⟨567142214565599252217065315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1512379238841598005912174173 567142214565599252217065315)
              ·
                refine ⟨850713321848398878325597973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 567142214565599252217065315 850713321848398878325597973)
                ·
                  refine ⟨39877186961643697421512405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 850713321848398878325597973 39877186961643697421512405)
                  ·
                    refine ⟨934621569413524158316697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39877186961643697421512405 934621569413524158316697)
                    ·
                      rfl

theorem cell23_5460507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 7].length) (baseStart_5460507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460507 prefixEnd_5460507 := by exact prefixLift 5460507
  have htrace : WordTrace (prefixWord ++ tailWord_5460507) baseStart_5460507 baseEnd_5460507 := by
    simpa [prefixWord, tailWord_5460507, baseEnd_5460507] using wordTrace_append hprefix tailTrace_5460507
  have hstable : (prefixWord ++ tailWord_5460507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460507).length < 2 ^ (prefixWord ++ tailWord_5460507).sum := by decide
  have hdescent : baseEnd_5460507 < baseStart_5460507 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460516 : List Nat := [2, 3, 1, 5, 2, 1, 2, 2, 1, 1, 3]
def baseStart_5460516 : Nat := 118140960795 + 5460516 * 2 ^ 59
def prefixEnd_5460516 : Nat := 4983230072969 + 3 ^ 40 * 5460516 * 2
def baseEnd_5460516 : Nat := 2803869329566462939737551

theorem tailTrace_5460516 : CollatzResearch.WordTrace tailWord_5460516 prefixEnd_5460516 2803869329566462939737551 := by
  unfold tailWord_5460516
  simp only [CollatzResearch.WordTrace]
  refine ⟨99580690142745294365636701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132774253523660392487515601 99580690142745294365636701)
  ·
    refine ⟨37342758803529485387113763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99580690142745294365636701 37342758803529485387113763)
    ·
      refine ⟨56014138205294228080670645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37342758803529485387113763 56014138205294228080670645)
      ·
        refine ⟨5251325456746333882562873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56014138205294228080670645 5251325456746333882562873)
        ·
          refine ⟨3938494092559750411922155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5251325456746333882562873 3938494092559750411922155)
          ·
            refine ⟨5907741138839625617883233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3938494092559750411922155 5907741138839625617883233)
            ·
              refine ⟨4430805854129719213412425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5907741138839625617883233 4430805854129719213412425)
              ·
                refine ⟨3323104390597289410059319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4430805854129719213412425 3323104390597289410059319)
                ·
                  refine ⟨4984656585895934115088979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3323104390597289410059319 4984656585895934115088979)
                  ·
                    refine ⟨7476984878843901172633469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4984656585895934115088979 7476984878843901172633469)
                    ·
                      refine ⟨2803869329566462939737551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7476984878843901172633469 2803869329566462939737551)
                      ·
                        rfl

theorem cell23_5460516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_5460516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460516 prefixEnd_5460516 := by exact prefixLift 5460516
  have htrace : WordTrace (prefixWord ++ tailWord_5460516) baseStart_5460516 baseEnd_5460516 := by
    simpa [prefixWord, tailWord_5460516, baseEnd_5460516] using wordTrace_append hprefix tailTrace_5460516
  have hstable : (prefixWord ++ tailWord_5460516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460516).length < 2 ^ (prefixWord ++ tailWord_5460516).sum := by decide
  have hdescent : baseEnd_5460516 < baseStart_5460516 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460522 : List Nat := [3, 1, 4, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_5460522 : Nat := 118140960795 + 5460522 * 2 ^ 59
def prefixEnd_5460522 : Nat := 4983230072969 + 3 ^ 40 * 5460522 * 2
def baseEnd_5460522 : Nat := 2803872410450389916262523

theorem tailTrace_5460522 : CollatzResearch.WordTrace tailWord_5460522 prefixEnd_5460522 2803872410450389916262523 := by
  unfold tailWord_5460522
  simp only [CollatzResearch.WordTrace]
  refine ⟨49790399780867212938997955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132774399415645901170661213 49790399780867212938997955)
  ·
    refine ⟨74685599671300819408496933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49790399780867212938997955 74685599671300819408496933)
    ·
      refine ⟨14003549938368903639093175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74685599671300819408496933 14003549938368903639093175)
      ·
        refine ⟨21005324907553355458639763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14003549938368903639093175 21005324907553355458639763)
        ·
          refine ⟨31507987361330033187959645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21005324907553355458639763 31507987361330033187959645)
          ·
            refine ⟨11815495260498762445484867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31507987361330033187959645 11815495260498762445484867)
            ·
              refine ⟨17723242890748143668227301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11815495260498762445484867 17723242890748143668227301)
              ·
                refine ⟨3323108042015276937792619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17723242890748143668227301 3323108042015276937792619)
                ·
                  refine ⟨4984662063022915406688929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3323108042015276937792619 4984662063022915406688929)
                  ·
                    refine ⟨3738496547267186555016697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4984662063022915406688929 3738496547267186555016697)
                    ·
                      refine ⟨2803872410450389916262523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738496547267186555016697 2803872410450389916262523)
                      ·
                        rfl

theorem cell23_5460522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_5460522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460522 prefixEnd_5460522 := by exact prefixLift 5460522
  have htrace : WordTrace (prefixWord ++ tailWord_5460522) baseStart_5460522 baseEnd_5460522 := by
    simpa [prefixWord, tailWord_5460522, baseEnd_5460522] using wordTrace_append hprefix tailTrace_5460522
  have hstable : (prefixWord ++ tailWord_5460522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460522).length < 2 ^ (prefixWord ++ tailWord_5460522).sum := by decide
  have hdescent : baseEnd_5460522 < baseStart_5460522 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460531 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 5, 3, 2]
def baseStart_5460531 : Nat := 118140960795 + 5460531 * 2 ^ 59
def prefixEnd_5460531 : Nat := 4983230072969 + 3 ^ 40 * 5460531 * 2
def baseEnd_5460531 : Nat := 2803877031776280381049981

theorem tailTrace_5460531 : CollatzResearch.WordTrace tailWord_5460531 prefixEnd_5460531 2803877031776280381049981 := by
  unfold tailWord_5460531
  simp only [CollatzResearch.WordTrace]
  refine ⟨199161927380436246293069447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132774618253624164195379631 199161927380436246293069447)
  ·
    refine ⟨298742891070654369439604171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199161927380436246293069447 298742891070654369439604171)
    ·
      refine ⟨448114336605981554159406257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298742891070654369439604171 448114336605981554159406257)
      ·
        refine ⟨336085752454486165619554693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448114336605981554159406257 336085752454486165619554693)
        ·
          refine ⟨63016078585216156053666505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 336085752454486165619554693 63016078585216156053666505)
          ·
            refine ⟨47262058938912117040249879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63016078585216156053666505 47262058938912117040249879)
            ·
              refine ⟨70893088408368175560374819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47262058938912117040249879 70893088408368175560374819)
              ·
                refine ⟨106339632612552263340562229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70893088408368175560374819 106339632612552263340562229)
                ·
                  refine ⟨9969340557426774688177709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106339632612552263340562229 9969340557426774688177709)
                  ·
                    refine ⟨3738502709035040508066641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9969340557426774688177709 3738502709035040508066641)
                    ·
                      refine ⟨2803877031776280381049981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738502709035040508066641 2803877031776280381049981)
                      ·
                        rfl

theorem cell23_5460531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 5, 3, 2].length) (baseStart_5460531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460531 prefixEnd_5460531 := by exact prefixLift 5460531
  have htrace : WordTrace (prefixWord ++ tailWord_5460531) baseStart_5460531 baseEnd_5460531 := by
    simpa [prefixWord, tailWord_5460531, baseEnd_5460531] using wordTrace_append hprefix tailTrace_5460531
  have hstable : (prefixWord ++ tailWord_5460531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460531).length < 2 ^ (prefixWord ++ tailWord_5460531).sum := by decide
  have hdescent : baseEnd_5460531 < baseStart_5460531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460538 : List Nat := [3, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3]
def baseStart_5460538 : Nat := 118140960795 + 5460538 * 2 ^ 59
def prefixEnd_5460538 : Nat := 4983230072969 + 3 ^ 40 * 5460538 * 2
def baseEnd_5460538 : Nat := 2803880626140861853662449

theorem tailTrace_5460538 : CollatzResearch.WordTrace tailWord_5460538 prefixEnd_5460538 2803880626140861853662449 := by
  unfold tailWord_5460538
  simp only [CollatzResearch.WordTrace]
  refine ⟨49790545672852721622143567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132774788460940590992382845 49790545672852721622143567)
  ·
    refine ⟨74685818509279082433215351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49790545672852721622143567 74685818509279082433215351)
    ·
      refine ⟨112028727763918623649823027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74685818509279082433215351 112028727763918623649823027)
      ·
        refine ⟨168043091645877935474734541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112028727763918623649823027 168043091645877935474734541)
        ·
          refine ⟨63016159367204225803025453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168043091645877935474734541 63016159367204225803025453)
          ·
            refine ⟨23631059762701584676134545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63016159367204225803025453 23631059762701584676134545)
            ·
              refine ⟨17723294822026188507100909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23631059762701584676134545 17723294822026188507100909)
              ·
                refine ⟨6646235558259820690162841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17723294822026188507100909 6646235558259820690162841)
                ·
                  refine ⟨4984676668694865517622131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6646235558259820690162841 4984676668694865517622131)
                  ·
                    refine ⟨7477015003042298276433197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4984676668694865517622131 7477015003042298276433197)
                    ·
                      refine ⟨2803880626140861853662449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7477015003042298276433197 2803880626140861853662449)
                      ·
                        rfl

theorem cell23_5460538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_5460538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460538 prefixEnd_5460538 := by exact prefixLift 5460538
  have htrace : WordTrace (prefixWord ++ tailWord_5460538) baseStart_5460538 baseEnd_5460538 := by
    simpa [prefixWord, tailWord_5460538, baseEnd_5460538] using wordTrace_append hprefix tailTrace_5460538
  have hstable : (prefixWord ++ tailWord_5460538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460538).length < 2 ^ (prefixWord ++ tailWord_5460538).sum := by decide
  have hdescent : baseEnd_5460538 < baseStart_5460538 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460565 : List Nat := [1, 3, 2, 2, 1, 1, 6, 1, 1, 3, 2]
def baseStart_5460565 : Nat := 118140960795 + 5460565 * 2 ^ 59
def prefixEnd_5460565 : Nat := 4983230072969 + 3 ^ 40 * 5460565 * 2
def baseEnd_5460565 : Nat := 2803894490118533248024825

theorem tailTrace_5460565 : CollatzResearch.WordTrace tailWord_5460565 prefixEnd_5460565 2803894490118533248024825 := by
  unfold tailWord_5460565
  simp only [CollatzResearch.WordTrace]
  refine ⟨199163167462313070099807149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132775444974875380066538099 199163167462313070099807149)
  ·
    refine ⟨74686187798367401287427681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199163167462313070099807149 74686187798367401287427681)
    ·
      refine ⟨56014640848775550965570761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74686187798367401287427681 56014640848775550965570761)
      ·
        refine ⟨42010980636581663224178071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56014640848775550965570761 42010980636581663224178071)
        ·
          refine ⟨63016470954872494836267107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42010980636581663224178071 63016470954872494836267107)
          ·
            refine ⟨94524706432308742254400661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63016470954872494836267107 94524706432308742254400661)
            ·
              refine ⟨4430845614014472293175031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94524706432308742254400661 4430845614014472293175031)
              ·
                refine ⟨6646268421021708439762547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4430845614014472293175031 6646268421021708439762547)
                ·
                  refine ⟨9969402631532562659643821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6646268421021708439762547 9969402631532562659643821)
                  ·
                    refine ⟨3738525986824710997366433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9969402631532562659643821 3738525986824710997366433)
                    ·
                      refine ⟨2803894490118533248024825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738525986824710997366433 2803894490118533248024825)
                      ·
                        rfl

theorem cell23_5460565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 1, 3, 2].length) (baseStart_5460565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460565 prefixEnd_5460565 := by exact prefixLift 5460565
  have htrace : WordTrace (prefixWord ++ tailWord_5460565) baseStart_5460565 baseEnd_5460565 := by
    simpa [prefixWord, tailWord_5460565, baseEnd_5460565] using wordTrace_append hprefix tailTrace_5460565
  have hstable : (prefixWord ++ tailWord_5460565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460565).length < 2 ^ (prefixWord ++ tailWord_5460565).sum := by decide
  have hdescent : baseEnd_5460565 < baseStart_5460565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460572 : List Nat := [2, 2, 4, 1, 3, 2, 1, 2, 2, 1, 3]
def baseStart_5460572 : Nat := 118140960795 + 5460572 * 2 ^ 59
def prefixEnd_5460572 : Nat := 4983230072969 + 3 ^ 40 * 5460572 * 2
def baseEnd_5460572 : Nat := 2803898084483114720637293

theorem tailTrace_5460572 : CollatzResearch.WordTrace tailWord_5460572 prefixEnd_5460572 2803898084483114720637293 := by
  unfold tailWord_5460572
  simp only [CollatzResearch.WordTrace]
  refine ⟨99581711386643855147655985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132775615182191806863541313 99581711386643855147655985)
  ·
    refine ⟨74686283539982891360741989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99581711386643855147655985 74686283539982891360741989)
    ·
      refine ⟨14003678163746792130139123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74686283539982891360741989 14003678163746792130139123)
      ·
        refine ⟨21005517245620188195208685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14003678163746792130139123 21005517245620188195208685)
        ·
          refine ⟨7877068967107570573203257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21005517245620188195208685 7877068967107570573203257)
          ·
            refine ⟨5907801725330677929902443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7877068967107570573203257 5907801725330677929902443)
            ·
              refine ⟨8861702587996016894853665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5907801725330677929902443 8861702587996016894853665)
              ·
                refine ⟨6646276940997012671140249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8861702587996016894853665 6646276940997012671140249)
                ·
                  refine ⟨4984707705747759503355187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6646276940997012671140249 4984707705747759503355187)
                  ·
                    refine ⟨7477061558621639255032781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4984707705747759503355187 7477061558621639255032781)
                    ·
                      refine ⟨2803898084483114720637293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7477061558621639255032781 2803898084483114720637293)
                      ·
                        rfl

theorem cell23_5460572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_5460572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460572 prefixEnd_5460572 := by exact prefixLift 5460572
  have htrace : WordTrace (prefixWord ++ tailWord_5460572) baseStart_5460572 baseEnd_5460572 := by
    simpa [prefixWord, tailWord_5460572, baseEnd_5460572] using wordTrace_append hprefix tailTrace_5460572
  have hstable : (prefixWord ++ tailWord_5460572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460572).length < 2 ^ (prefixWord ++ tailWord_5460572).sum := by decide
  have hdescent : baseEnd_5460572 < baseStart_5460572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460631 : List Nat := [1, 1, 3, 3, 2, 1, 3, 2, 2, 5]
def baseStart_5460631 : Nat := 118140960795 + 5460631 * 2 ^ 59
def prefixEnd_5460631 : Nat := 4983230072969 + 3 ^ 40 * 5460631 * 2
def baseEnd_5460631 : Nat := 934642793280576663266507

theorem tailTrace_5460631 : CollatzResearch.WordTrace tailWord_5460631 prefixEnd_5460631 934642793280576663266507 := by
  unfold tailWord_5460631
  simp only [CollatzResearch.WordTrace]
  refine ⟨199165574680073963371709747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132777049786715975581139831 199165574680073963371709747)
  ·
    refine ⟨298748362020110945057564621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199165574680073963371709747 298748362020110945057564621)
    ·
      refine ⟨112030635757541604396586733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298748362020110945057564621 112030635757541604396586733)
      ·
        refine ⟨42011488409078101648720025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112030635757541604396586733 42011488409078101648720025)
        ·
          refine ⟨31508616306808576236540019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42011488409078101648720025 31508616306808576236540019)
          ·
            refine ⟨47262924460212864354810029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31508616306808576236540019 47262924460212864354810029)
            ·
              refine ⟨17723596672579824133053761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47262924460212864354810029 17723596672579824133053761)
              ·
                refine ⟨13292697504434868099790321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17723596672579824133053761 13292697504434868099790321)
                ·
                  refine ⟨9969523128326151074842741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13292697504434868099790321 9969523128326151074842741)
                  ·
                    refine ⟨934642793280576663266507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9969523128326151074842741 934642793280576663266507)
                    ·
                      rfl

theorem cell23_5460631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_5460631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460631 prefixEnd_5460631 := by exact prefixLift 5460631
  have htrace : WordTrace (prefixWord ++ tailWord_5460631) baseStart_5460631 baseEnd_5460631 := by
    simpa [prefixWord, tailWord_5460631, baseEnd_5460631] using wordTrace_append hprefix tailTrace_5460631
  have hstable : (prefixWord ++ tailWord_5460631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460631).length < 2 ^ (prefixWord ++ tailWord_5460631).sum := by decide
  have hdescent : baseEnd_5460631 < baseStart_5460631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460664 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 3, 3, 6]
def baseStart_5460664 : Nat := 118140960795 + 5460664 * 2 ^ 59
def prefixEnd_5460664 : Nat := 4983230072969 + 3 ^ 40 * 5460664 * 2
def baseEnd_5460664 : Nat := 2803945324703328360686869

theorem tailTrace_5460664 : CollatzResearch.WordTrace tailWord_5460664 prefixEnd_5460664 2803945324703328360686869 := by
  unfold tailWord_5460664
  simp only [CollatzResearch.WordTrace]
  refine ⟨99583389144477205003830523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132777852192636273338440697 99583389144477205003830523)
  ·
    refine ⟨149375083716715807505745785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99583389144477205003830523 149375083716715807505745785)
    ·
      refine ⟨112031312787536855629309339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149375083716715807505745785 112031312787536855629309339)
      ·
        refine ⟨168046969181305283443964009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112031312787536855629309339 168046969181305283443964009)
        ·
          refine ⟨126035226885978962582973007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168046969181305283443964009 126035226885978962582973007)
          ·
            refine ⟨189052840328968443874459511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126035226885978962582973007 189052840328968443874459511)
            ·
              refine ⟨283579260493452665811689267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189052840328968443874459511 283579260493452665811689267)
              ·
                refine ⟨425368890740178998717533901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283579260493452665811689267 425368890740178998717533901)
                ·
                  refine ⟨159513334027567124519075213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 425368890740178998717533901 159513334027567124519075213)
                  ·
                    refine ⟨59817500260337671694653205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159513334027567124519075213 59817500260337671694653205)
                    ·
                      refine ⟨2803945324703328360686869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59817500260337671694653205 2803945324703328360686869)
                      ·
                        rfl

theorem cell23_5460664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_5460664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460664 prefixEnd_5460664 := by exact prefixLift 5460664
  have htrace : WordTrace (prefixWord ++ tailWord_5460664) baseStart_5460664 baseEnd_5460664 := by
    simpa [prefixWord, tailWord_5460664, baseEnd_5460664] using wordTrace_append hprefix tailTrace_5460664
  have hstable : (prefixWord ++ tailWord_5460664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460664).length < 2 ^ (prefixWord ++ tailWord_5460664).sum := by decide
  have hdescent : baseEnd_5460664 < baseStart_5460664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460668 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 2, 1, 4]
def baseStart_5460668 : Nat := 118140960795 + 5460668 * 2 ^ 59
def prefixEnd_5460668 : Nat := 4983230072969 + 3 ^ 40 * 5460668 * 2
def baseEnd_5460668 : Nat := 2803947378625946345036851

theorem tailTrace_5460668 : CollatzResearch.WordTrace tailWord_5460668 prefixEnd_5460668 2803947378625946345036851 := by
  unfold tailWord_5460668
  simp only [CollatzResearch.WordTrace]
  refine ⟨99583462090469959345403329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132777949453959945793871105 99583462090469959345403329)
  ·
    refine ⟨74687596567852469509052497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99583462090469959345403329 74687596567852469509052497)
    ·
      refine ⟨56015697425889352131789373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74687596567852469509052497 56015697425889352131789373)
      ·
        refine ⟨21005886534708507049421015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56015697425889352131789373 21005886534708507049421015)
        ·
          refine ⟨31508829802062760574131523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21005886534708507049421015 31508829802062760574131523)
          ·
            refine ⟨47263244703094140861197285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31508829802062760574131523 47263244703094140861197285)
            ·
              refine ⟨8861858381830151411474491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47263244703094140861197285 8861858381830151411474491)
              ·
                refine ⟨13292787572745227117211737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8861858381830151411474491 13292787572745227117211737)
                ·
                  refine ⟨9969590679558920337908803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13292787572745227117211737 9969590679558920337908803)
                  ·
                    refine ⟨14954386019338380506863205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9969590679558920337908803 14954386019338380506863205)
                    ·
                      refine ⟨2803947378625946345036851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14954386019338380506863205 2803947378625946345036851)
                      ·
                        rfl

theorem cell23_5460668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 2, 1, 4].length) (baseStart_5460668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460668 prefixEnd_5460668 := by exact prefixLift 5460668
  have htrace : WordTrace (prefixWord ++ tailWord_5460668) baseStart_5460668 baseEnd_5460668 := by
    simpa [prefixWord, tailWord_5460668, baseEnd_5460668] using wordTrace_append hprefix tailTrace_5460668
  have hstable : (prefixWord ++ tailWord_5460668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460668).length < 2 ^ (prefixWord ++ tailWord_5460668).sum := by decide
  have hdescent : baseEnd_5460668 < baseStart_5460668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460695 : List Nat := [1, 1, 3, 2, 1, 5, 1, 4, 1, 4]
def baseStart_5460695 : Nat := 118140960795 + 5460695 * 2 ^ 59
def prefixEnd_5460695 : Nat := 4983230072969 + 3 ^ 40 * 5460695 * 2
def baseEnd_5460695 : Nat := 934653747534539246466409

theorem tailTrace_5460695 : CollatzResearch.WordTrace tailWord_5460695 prefixEnd_5460695 934653747534539246466409 := by
  unfold tailWord_5460695
  simp only [CollatzResearch.WordTrace]
  refine ⟨199167908951842102302039539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132778605967894734868026359 199167908951842102302039539)
  ·
    refine ⟨298751863427763153453059309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199167908951842102302039539 298751863427763153453059309)
    ·
      refine ⟨112031948785411182544897241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298751863427763153453059309 112031948785411182544897241)
      ·
        refine ⟨84023961589058386908672931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112031948785411182544897241 84023961589058386908672931)
        ·
          refine ⟨126035942383587580363009397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84023961589058386908672931 126035942383587580363009397)
          ·
            refine ⟨11815869598461335659032131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126035942383587580363009397 11815869598461335659032131)
            ·
              refine ⟨17723804397692003488548197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11815869598461335659032131 17723804397692003488548197)
              ·
                refine ⟨3323213324567250654102787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17723804397692003488548197 3323213324567250654102787)
                ·
                  refine ⟨4984819986850875981154181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3323213324567250654102787 4984819986850875981154181)
                  ·
                    refine ⟨934653747534539246466409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4984819986850875981154181 934653747534539246466409)
                    ·
                      rfl

theorem cell23_5460695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 4, 1, 4].length) (baseStart_5460695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460695 prefixEnd_5460695 := by exact prefixLift 5460695
  have htrace : WordTrace (prefixWord ++ tailWord_5460695) baseStart_5460695 baseEnd_5460695 := by
    simpa [prefixWord, tailWord_5460695, baseEnd_5460695] using wordTrace_append hprefix tailTrace_5460695
  have hstable : (prefixWord ++ tailWord_5460695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460695).length < 2 ^ (prefixWord ++ tailWord_5460695).sum := by decide
  have hdescent : baseEnd_5460695 < baseStart_5460695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460721 : List Nat := [1, 2, 2, 2, 2, 2, 1, 3, 3, 5]
def baseStart_5460721 : Nat := 118140960795 + 5460721 * 2 ^ 59
def prefixEnd_5460721 : Nat := 4983230072969 + 3 ^ 40 * 5460721 * 2
def baseEnd_5460721 : Nat := 934658197700211545891369

theorem tailTrace_5460721 : CollatzResearch.WordTrace tailWord_5460721 prefixEnd_5460721 934658197700211545891369 := by
  unfold tailWord_5460721
  simp only [CollatzResearch.WordTrace]
  refine ⟨199168857249747908742486017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132779238166498605828324011 199168857249747908742486017)
  ·
    refine ⟨149376642937310931556864513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199168857249747908742486017 149376642937310931556864513)
    ·
      refine ⟨112032482202983198667648385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149376642937310931556864513 112032482202983198667648385)
      ·
        refine ⟨84024361652237399000736289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112032482202983198667648385 84024361652237399000736289)
        ·
          refine ⟨63018271239178049250552217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84024361652237399000736289 63018271239178049250552217)
          ·
            refine ⟨47263703429383536937914163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63018271239178049250552217 47263703429383536937914163)
            ·
              refine ⟨70895555144075305406871245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47263703429383536937914163 70895555144075305406871245)
              ·
                refine ⟨26585833179028239527576717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70895555144075305406871245 26585833179028239527576717)
                ·
                  refine ⟨9969687442135589822841269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26585833179028239527576717 9969687442135589822841269)
                  ·
                    refine ⟨934658197700211545891369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9969687442135589822841269 934658197700211545891369)
                    ·
                      rfl

theorem cell23_5460721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_5460721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460721 prefixEnd_5460721 := by exact prefixLift 5460721
  have htrace : WordTrace (prefixWord ++ tailWord_5460721) baseStart_5460721 baseEnd_5460721 := by
    simpa [prefixWord, tailWord_5460721, baseEnd_5460721] using wordTrace_append hprefix tailTrace_5460721
  have hstable : (prefixWord ++ tailWord_5460721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460721).length < 2 ^ (prefixWord ++ tailWord_5460721).sum := by decide
  have hdescent : baseEnd_5460721 < baseStart_5460721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460728 : List Nat := [2, 1, 2, 1, 1, 2, 5, 1, 1, 5, 2]
def baseStart_5460728 : Nat := 118140960795 + 5460728 * 2 ^ 59
def prefixEnd_5460728 : Nat := 4983230072969 + 3 ^ 40 * 5460728 * 2
def baseEnd_5460728 : Nat := 2803978187465216110286575

theorem tailTrace_5460728 : CollatzResearch.WordTrace tailWord_5460728 prefixEnd_5460728 2803978187465216110286575 := by
  unfold tailWord_5460728
  simp only [CollatzResearch.WordTrace]
  refine ⟨99584556280361274468995419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132779408373815032625327225 99584556280361274468995419)
  ·
    refine ⟨149376834420541911703493129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99584556280361274468995419 149376834420541911703493129)
    ·
      refine ⟨112032625815406433777619847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149376834420541911703493129 112032625815406433777619847)
      ·
        refine ⟨168048938723109650666429771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112032625815406433777619847 168048938723109650666429771)
        ·
          refine ⟨252073408084664475999644657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168048938723109650666429771 252073408084664475999644657)
          ·
            refine ⟨189055056063498356999733493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252073408084664475999644657 189055056063498356999733493)
            ·
              refine ⟨17723911505952970968725015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 189055056063498356999733493 17723911505952970968725015)
              ·
                refine ⟨26585867258929456453087523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17723911505952970968725015 26585867258929456453087523)
                ·
                  refine ⟨39878800888394184679631285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26585867258929456453087523 39878800888394184679631285)
                  ·
                    refine ⟨3738637583286954813715433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39878800888394184679631285 3738637583286954813715433)
                    ·
                      refine ⟨2803978187465216110286575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738637583286954813715433 2803978187465216110286575)
                      ·
                        rfl

theorem cell23_5460728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 5, 1, 1, 5, 2].length) (baseStart_5460728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460728 prefixEnd_5460728 := by exact prefixLift 5460728
  have htrace : WordTrace (prefixWord ++ tailWord_5460728) baseStart_5460728 baseEnd_5460728 := by
    simpa [prefixWord, tailWord_5460728, baseEnd_5460728] using wordTrace_append hprefix tailTrace_5460728
  have hstable : (prefixWord ++ tailWord_5460728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460728).length < 2 ^ (prefixWord ++ tailWord_5460728).sum := by decide
  have hdescent : baseEnd_5460728 < baseStart_5460728 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460761 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 2, 6, 3]
def baseStart_5460761 : Nat := 118140960795 + 5460761 * 2 ^ 59
def prefixEnd_5460761 : Nat := 4983230072969 + 3 ^ 40 * 5460761 * 2
def baseEnd_5460761 : Nat := 2803995132326814481173923

theorem tailTrace_5460761 : CollatzResearch.WordTrace tailWord_5460761 prefixEnd_5460761 2803995132326814481173923 := by
  unfold tailWord_5460761
  simp only [CollatzResearch.WordTrace]
  refine ⟨199170316169602995573942137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132780210779735330382628091 199170316169602995573942137)
  ·
    refine ⟨149377737127202246680456603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199170316169602995573942137 149377737127202246680456603)
    ·
      refine ⟨224066605690803370020684905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149377737127202246680456603 224066605690803370020684905)
      ·
        refine ⟨168049954268102527515513679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224066605690803370020684905 168049954268102527515513679)
        ·
          refine ⟨252074931402153791273270519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168049954268102527515513679 252074931402153791273270519)
          ·
            refine ⟨378112397103230686909905779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252074931402153791273270519 378112397103230686909905779)
            ·
              refine ⟨567168595654846030364858669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378112397103230686909905779 567168595654846030364858669)
              ·
                refine ⟨212688223370567261386822001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 567168595654846030364858669 212688223370567261386822001)
                ·
                  refine ⟨159516167527925446040116501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212688223370567261386822001 159516167527925446040116501)
                  ·
                    refine ⟨7477320352871505283130461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 159516167527925446040116501 7477320352871505283130461)
                    ·
                      refine ⟨2803995132326814481173923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7477320352871505283130461 2803995132326814481173923)
                      ·
                        rfl

theorem cell23_5460761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_5460761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460761 prefixEnd_5460761 := by exact prefixLift 5460761
  have htrace : WordTrace (prefixWord ++ tailWord_5460761) baseStart_5460761 baseEnd_5460761 := by
    simpa [prefixWord, tailWord_5460761, baseEnd_5460761] using wordTrace_append hprefix tailTrace_5460761
  have hstable : (prefixWord ++ tailWord_5460761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460761).length < 2 ^ (prefixWord ++ tailWord_5460761).sum := by decide
  have hdescent : baseEnd_5460761 < baseStart_5460761 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460768 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 1, 6]
def baseStart_5460768 : Nat := 118140960795 + 5460768 * 2 ^ 59
def prefixEnd_5460768 : Nat := 4983230072969 + 3 ^ 40 * 5460768 * 2
def baseEnd_5460768 : Nat := 934666242230465317928797

theorem tailTrace_5460768 : CollatzResearch.WordTrace tailWord_5460768 prefixEnd_5460768 934666242230465317928797 := by
  unfold tailWord_5460768
  simp only [CollatzResearch.WordTrace]
  refine ⟨99585285740288817884723479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132780380987051757179631305 99585285740288817884723479)
  ·
    refine ⟨149377928610433226827085219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99585285740288817884723479 149377928610433226827085219)
    ·
      refine ⟨224066892915649840240627829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149377928610433226827085219 224066892915649840240627829)
      ·
        refine ⟨21006271210842172522558859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 224066892915649840240627829 21006271210842172522558859)
        ·
          refine ⟨31509406816263258783838289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21006271210842172522558859 31509406816263258783838289)
          ·
            refine ⟨23632055112197444087878717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31509406816263258783838289 23632055112197444087878717)
            ·
              refine ⟨8862020667074041532954519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23632055112197444087878717 8862020667074041532954519)
              ·
                refine ⟨13293031000611062299431779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8862020667074041532954519 13293031000611062299431779)
                ·
                  refine ⟨19939546500916593449147669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13293031000611062299431779 19939546500916593449147669)
                  ·
                    refine ⟨934666242230465317928797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19939546500916593449147669 934666242230465317928797)
                    ·
                      rfl

theorem cell23_5460768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 1, 6].length) (baseStart_5460768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460768 prefixEnd_5460768 := by exact prefixLift 5460768
  have htrace : WordTrace (prefixWord ++ tailWord_5460768) baseStart_5460768 baseEnd_5460768 := by
    simpa [prefixWord, tailWord_5460768, baseEnd_5460768] using wordTrace_append hprefix tailTrace_5460768
  have hstable : (prefixWord ++ tailWord_5460768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460768).length < 2 ^ (prefixWord ++ tailWord_5460768).sum := by decide
  have hdescent : baseEnd_5460768 < baseStart_5460768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460841 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 6, 6]
def baseStart_5460841 : Nat := 118140960795 + 5460841 * 2 ^ 59
def prefixEnd_5460841 : Nat := 4983230072969 + 3 ^ 40 * 5460841 * 2
def baseEnd_5460841 : Nat := 934678736926391389391185

theorem tailTrace_5460841 : CollatzResearch.WordTrace tailWord_5460841 prefixEnd_5460841 934678736926391389391185 := by
  unfold tailWord_5460841
  simp only [CollatzResearch.WordTrace]
  refine ⟨199173234009313169236854377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132782156006208779491236251 199173234009313169236854377)
  ·
    refine ⟨149379925506984876927640783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199173234009313169236854377 149379925506984876927640783)
    ·
      refine ⟨224069888260477315391461175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149379925506984876927640783 224069888260477315391461175)
      ·
        refine ⟨336104832390715973087191763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224069888260477315391461175 336104832390715973087191763)
        ·
          refine ⟨504157248586073959630787645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336104832390715973087191763 504157248586073959630787645)
          ·
            refine ⟨189058968219777734861545367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 504157248586073959630787645 189058968219777734861545367)
            ·
              refine ⟨283588452329666602292318051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189058968219777734861545367 283588452329666602292318051)
              ·
                refine ⟨425382678494499903438477077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283588452329666602292318051 425382678494499903438477077)
                ·
                  refine ⟨19939813054429682973678613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 425382678494499903438477077 19939813054429682973678613)
                  ·
                    refine ⟨934678736926391389391185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19939813054429682973678613 934678736926391389391185)
                    ·
                      rfl

theorem cell23_5460841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 6].length) (baseStart_5460841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460841 prefixEnd_5460841 := by exact prefixLift 5460841
  have htrace : WordTrace (prefixWord ++ tailWord_5460841) baseStart_5460841 baseEnd_5460841 := by
    simpa [prefixWord, tailWord_5460841, baseEnd_5460841] using wordTrace_append hprefix tailTrace_5460841
  have hstable : (prefixWord ++ tailWord_5460841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460841).length < 2 ^ (prefixWord ++ tailWord_5460841).sum := by decide
  have hdescent : baseEnd_5460841 < baseStart_5460841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460886 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 3, 3, 2]
def baseStart_5460886 : Nat := 118140960795 + 5460886 * 2 ^ 59
def prefixEnd_5460886 : Nat := 4983230072969 + 3 ^ 40 * 5460886 * 2
def baseEnd_5460886 : Nat := 2804059317408626492110849

theorem tailTrace_5460886 : CollatzResearch.WordTrace tailWord_5460886 prefixEnd_5460886 2804059317408626492110849 := by
  unfold tailWord_5460886
  simp only [CollatzResearch.WordTrace]
  refine ⟨12448429705884383870140157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132783250196100094614828341 12448429705884383870140157)
  ·
    refine ⟨4668161139706643951302559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12448429705884383870140157 4668161139706643951302559)
    ·
      refine ⟨7002241709559965926953839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4668161139706643951302559 7002241709559965926953839)
      ·
        refine ⟨10503362564339948890430759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7002241709559965926953839 10503362564339948890430759)
        ·
          refine ⟨15755043846509923335646139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10503362564339948890430759 15755043846509923335646139)
          ·
            refine ⟨23632565769764885003469209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15755043846509923335646139 23632565769764885003469209)
            ·
              refine ⟨17724424327323663752601907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23632565769764885003469209 17724424327323663752601907)
              ·
                refine ⟨26586636490985495628902861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17724424327323663752601907 26586636490985495628902861)
                ·
                  refine ⟨9969988684119560860838573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26586636490985495628902861 9969988684119560860838573)
                  ·
                    refine ⟨3738745756544835322814465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9969988684119560860838573 3738745756544835322814465)
                    ·
                      refine ⟨2804059317408626492110849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738745756544835322814465 2804059317408626492110849)
                      ·
                        rfl

theorem cell23_5460886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 3, 3, 2].length) (baseStart_5460886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460886 prefixEnd_5460886 := by exact prefixLift 5460886
  have htrace : WordTrace (prefixWord ++ tailWord_5460886) baseStart_5460886 baseEnd_5460886 := by
    simpa [prefixWord, tailWord_5460886, baseEnd_5460886] using wordTrace_append hprefix tailTrace_5460886
  have hstable : (prefixWord ++ tailWord_5460886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460886).length < 2 ^ (prefixWord ++ tailWord_5460886).sum := by decide
  have hdescent : baseEnd_5460886 < baseStart_5460886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460903 : List Nat := [1, 1, 6, 1, 4, 1, 2, 1, 1, 3, 2]
def baseStart_5460903 : Nat := 118140960795 + 5460903 * 2 ^ 59
def prefixEnd_5460903 : Nat := 4983230072969 + 3 ^ 40 * 5460903 * 2
def baseEnd_5460903 : Nat := 2804068046579752925598271

theorem tailTrace_5460903 : CollatzResearch.WordTrace tailWord_5460903 prefixEnd_5460903 2804068046579752925598271 := by
  unfold tailWord_5460903
  simp only [CollatzResearch.WordTrace]
  refine ⟨199175495335088553825611363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132783663556725702550407575 199175495335088553825611363)
  ·
    refine ⟨298763243002632830738417045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199175495335088553825611363 298763243002632830738417045)
    ·
      refine ⟨14004527015748413940863299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 298763243002632830738417045 14004527015748413940863299)
      ·
        refine ⟨21006790523622620911294949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14004527015748413940863299 21006790523622620911294949)
        ·
          refine ⟨3938773223179241420867803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21006790523622620911294949 3938773223179241420867803)
          ·
            refine ⟨5908159834768862131301705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3938773223179241420867803 5908159834768862131301705)
            ·
              refine ⟨4431119876076646598476279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5908159834768862131301705 4431119876076646598476279)
              ·
                refine ⟨6646679814114969897714419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4431119876076646598476279 6646679814114969897714419)
                ·
                  refine ⟨9970019721172454846571629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6646679814114969897714419 9970019721172454846571629)
                  ·
                    refine ⟨3738757395439670567464361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9970019721172454846571629 3738757395439670567464361)
                    ·
                      refine ⟨2804068046579752925598271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738757395439670567464361 2804068046579752925598271)
                      ·
                        rfl

theorem cell23_5460903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 1, 3, 2].length) (baseStart_5460903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460903 prefixEnd_5460903 := by exact prefixLift 5460903
  have htrace : WordTrace (prefixWord ++ tailWord_5460903) baseStart_5460903 baseEnd_5460903 := by
    simpa [prefixWord, tailWord_5460903, baseEnd_5460903] using wordTrace_append hprefix tailTrace_5460903
  have hstable : (prefixWord ++ tailWord_5460903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460903).length < 2 ^ (prefixWord ++ tailWord_5460903).sum := by decide
  have hdescent : baseEnd_5460903 < baseStart_5460903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460905 : List Nat := [1, 2, 1, 1, 1, 1, 8, 3, 5]
def baseStart_5460905 : Nat := 118140960795 + 5460905 * 2 ^ 59
def prefixEnd_5460905 : Nat := 4983230072969 + 3 ^ 40 * 5460905 * 2
def baseEnd_5460905 : Nat := 311563230393451324197029

theorem tailTrace_5460905 : CollatzResearch.WordTrace tailWord_5460905 prefixEnd_5460905 311563230393451324197029 := by
  unfold tailWord_5460905
  simp only [CollatzResearch.WordTrace]
  refine ⟨199175568281081308167184169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132783712187387538778122779 199175568281081308167184169)
  ·
    refine ⟨149381676210810981125388127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199175568281081308167184169 149381676210810981125388127)
    ·
      refine ⟨224072514316216471688082191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149381676210810981125388127 224072514316216471688082191)
      ·
        refine ⟨336108771474324707532123287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224072514316216471688082191 336108771474324707532123287)
        ·
          refine ⟨504163157211487061298184931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336108771474324707532123287 504163157211487061298184931)
          ·
            refine ⟨756244735817230591947277397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504163157211487061298184931 756244735817230591947277397)
            ·
              refine ⟨8862242997858170999382157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 756244735817230591947277397 8862242997858170999382157)
              ·
                refine ⟨3323341124196814124768309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8862242997858170999382157 3323341124196814124768309)
                ·
                  refine ⟨311563230393451324197029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3323341124196814124768309 311563230393451324197029)
                  ·
                    rfl

theorem cell23_5460905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 3, 5].length) (baseStart_5460905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460905 prefixEnd_5460905 := by exact prefixLift 5460905
  have htrace : WordTrace (prefixWord ++ tailWord_5460905) baseStart_5460905 baseEnd_5460905 := by
    simpa [prefixWord, tailWord_5460905, baseEnd_5460905] using wordTrace_append hprefix tailTrace_5460905
  have hstable : (prefixWord ++ tailWord_5460905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460905).length < 2 ^ (prefixWord ++ tailWord_5460905).sum := by decide
  have hdescent : baseEnd_5460905 < baseStart_5460905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460916 : List Nat := [2, 5, 2, 1, 1, 2, 1, 1, 4, 2, 2]
def baseStart_5460916 : Nat := 118140960795 + 5460916 * 2 ^ 59
def prefixEnd_5460916 : Nat := 4983230072969 + 3 ^ 40 * 5460916 * 2
def baseEnd_5460916 : Nat := 2804074721828261374735711

theorem tailTrace_5460916 : CollatzResearch.WordTrace tailWord_5460916 prefixEnd_5460916 2804074721828261374735711 := by
  unfold tailWord_5460916
  simp only [CollatzResearch.WordTrace]
  refine ⟨99587984742020728522917301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132783979656027638030556401 99587984742020728522917301)
  ·
    refine ⟨9336373569564443299023497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99587984742020728522917301 9336373569564443299023497)
    ·
      refine ⟨7002280177173332474267623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9336373569564443299023497 7002280177173332474267623)
      ·
        refine ⟨10503420265759998711401435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7002280177173332474267623 10503420265759998711401435)
        ·
          refine ⟨15755130398639998067102153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10503420265759998711401435 15755130398639998067102153)
          ·
            refine ⟨11816347798979998550326615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15755130398639998067102153 11816347798979998550326615)
            ·
              refine ⟨17724521698469997825489923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11816347798979998550326615 17724521698469997825489923)
              ·
                refine ⟨26586782547704996738234885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17724521698469997825489923 26586782547704996738234885)
                ·
                  refine ⟨4985021727694686888419041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26586782547704996738234885 4985021727694686888419041)
                  ·
                    refine ⟨3738766295771015166314281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4985021727694686888419041 3738766295771015166314281)
                    ·
                      refine ⟨2804074721828261374735711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738766295771015166314281 2804074721828261374735711)
                      ·
                        rfl

theorem cell23_5460916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 1, 4, 2, 2].length) (baseStart_5460916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460916 prefixEnd_5460916 := by exact prefixLift 5460916
  have htrace : WordTrace (prefixWord ++ tailWord_5460916) baseStart_5460916 baseEnd_5460916 := by
    simpa [prefixWord, tailWord_5460916, baseEnd_5460916] using wordTrace_append hprefix tailTrace_5460916
  have hstable : (prefixWord ++ tailWord_5460916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460916).length < 2 ^ (prefixWord ++ tailWord_5460916).sum := by decide
  have hdescent : baseEnd_5460916 < baseStart_5460916 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460968 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 1, 3, 6]
def baseStart_5460968 : Nat := 118140960795 + 5460968 * 2 ^ 59
def prefixEnd_5460968 : Nat := 4983230072969 + 3 ^ 40 * 5460968 * 2
def baseEnd_5460968 : Nat := 2804101422822295171285471

theorem tailTrace_5460968 : CollatzResearch.WordTrace tailWord_5460968 prefixEnd_5460968 2804101422822295171285471 := by
  unfold tailWord_5460968
  simp only [CollatzResearch.WordTrace]
  refine ⟨99588933039926534963363779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132785244053235379951151705 99588933039926534963363779)
  ·
    refine ⟨149383399559889802445045669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99588933039926534963363779 149383399559889802445045669)
    ·
      refine ⟨28009387417479337958446063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149383399559889802445045669 28009387417479337958446063)
      ·
        refine ⟨42014081126219006937669095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28009387417479337958446063 42014081126219006937669095)
        ·
          refine ⟨63021121689328510406503643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42014081126219006937669095 63021121689328510406503643)
          ·
            refine ⟨94531682533992765609755465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63021121689328510406503643 94531682533992765609755465)
            ·
              refine ⟨70898761900494574207316599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94531682533992765609755465 70898761900494574207316599)
              ·
                refine ⟨106348142850741861310974899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70898761900494574207316599 106348142850741861310974899)
                ·
                  refine ⟨159522214276112791966462349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106348142850741861310974899 159522214276112791966462349)
                  ·
                    refine ⟨59820830353542296987423381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159522214276112791966462349 59820830353542296987423381)
                    ·
                      refine ⟨2804101422822295171285471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59820830353542296987423381 2804101422822295171285471)
                      ·
                        rfl

theorem cell23_5460968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_5460968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460968 prefixEnd_5460968 := by exact prefixLift 5460968
  have htrace : WordTrace (prefixWord ++ tailWord_5460968) baseStart_5460968 baseEnd_5460968 := by
    simpa [prefixWord, tailWord_5460968, baseEnd_5460968] using wordTrace_append hprefix tailTrace_5460968
  have hstable : (prefixWord ++ tailWord_5460968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460968).length < 2 ^ (prefixWord ++ tailWord_5460968).sum := by decide
  have hdescent : baseEnd_5460968 < baseStart_5460968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5460975 : List Nat := [1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 3]
def baseStart_5460975 : Nat := 118140960795 + 5460975 * 2 ^ 59
def prefixEnd_5460975 : Nat := 4983230072969 + 3 ^ 40 * 5460975 * 2
def baseEnd_5460975 : Nat := 2804105017186876643897939

theorem tailTrace_5460975 : CollatzResearch.WordTrace tailWord_5460975 prefixEnd_5460975 2804105017186876643897939 := by
  unfold tailWord_5460975
  simp only [CollatzResearch.WordTrace]
  refine ⟨199178121390827710122232379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132785414260551806748154919 199178121390827710122232379)
  ·
    refine ⟨298767182086241565183348569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199178121390827710122232379 298767182086241565183348569)
    ·
      refine ⟨224075386564681173887511427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298767182086241565183348569 224075386564681173887511427)
      ·
        refine ⟨336113079847021760831267141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224075386564681173887511427 336113079847021760831267141)
        ·
          refine ⟨63021202471316580155862589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 336113079847021760831267141 63021202471316580155862589)
          ·
            refine ⟨23632950926743717558448471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63021202471316580155862589 23632950926743717558448471)
            ·
              refine ⟨35449426390115576337672707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23632950926743717558448471 35449426390115576337672707)
              ·
                refine ⟨53174139585173364506509061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35449426390115576337672707 53174139585173364506509061)
                ·
                  refine ⟨9970151172220005844970449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53174139585173364506509061 9970151172220005844970449)
                  ·
                    refine ⟨7477613379165004383727837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9970151172220005844970449 7477613379165004383727837)
                    ·
                      refine ⟨2804105017186876643897939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7477613379165004383727837 2804105017186876643897939)
                      ·
                        rfl

theorem cell23_5460975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 3].length) (baseStart_5460975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5460975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5460975 prefixEnd_5460975 := by exact prefixLift 5460975
  have htrace : WordTrace (prefixWord ++ tailWord_5460975) baseStart_5460975 baseEnd_5460975 := by
    simpa [prefixWord, tailWord_5460975, baseEnd_5460975] using wordTrace_append hprefix tailTrace_5460975
  have hstable : (prefixWord ++ tailWord_5460975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5460975).length < 2 ^ (prefixWord ++ tailWord_5460975).sum := by decide
  have hdescent : baseEnd_5460975 < baseStart_5460975 := by decide
  rcases family_descends (prefixWord ++ tailWord_5460975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461055 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 6, 4]
def baseStart_5461055 : Nat := 118140960795 + 5461055 * 2 ^ 59
def prefixEnd_5461055 : Nat := 4983230072969 + 3 ^ 40 * 5461055 * 2
def baseEnd_5461055 : Nat := 934715365213078776965857

theorem tailTrace_5461055 : CollatzResearch.WordTrace tailWord_5461055 prefixEnd_5461055 934715365213078776965857 := by
  unfold tailWord_5461055
  simp only [CollatzResearch.WordTrace]
  refine ⟨199181039230537883785144619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132787359487025255856763079 199181039230537883785144619)
  ·
    refine ⟨298771558845806825677716929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199181039230537883785144619 298771558845806825677716929)
    ·
      refine ⟨224078669134355119258287697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 298771558845806825677716929 224078669134355119258287697)
      ·
        refine ⟨168059001850766339443715773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224078669134355119258287697 168059001850766339443715773)
        ·
          refine ⟨63022125694037377291393415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168059001850766339443715773 63022125694037377291393415)
          ·
            refine ⟨94533188541056065937090123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63022125694037377291393415 94533188541056065937090123)
            ·
              refine ⟨141799782811584098905635185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94533188541056065937090123 141799782811584098905635185)
              ·
                refine ⟨106349837108688074179226389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141799782811584098905635185 106349837108688074179226389)
                ·
                  refine ⟨4985148614469753477151237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106349837108688074179226389 4985148614469753477151237)
                  ·
                    refine ⟨934715365213078776965857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4985148614469753477151237 934715365213078776965857)
                    ·
                      rfl

theorem cell23_5461055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 4].length) (baseStart_5461055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461055 prefixEnd_5461055 := by exact prefixLift 5461055
  have htrace : WordTrace (prefixWord ++ tailWord_5461055) baseStart_5461055 baseEnd_5461055 := by
    simpa [prefixWord, tailWord_5461055, baseEnd_5461055] using wordTrace_append hprefix tailTrace_5461055
  have hstable : (prefixWord ++ tailWord_5461055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461055).length < 2 ^ (prefixWord ++ tailWord_5461055).sum := by decide
  have hdescent : baseEnd_5461055 < baseStart_5461055 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461109 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_5461109 : Nat := 118140960795 + 5461109 * 2 ^ 59
def prefixEnd_5461109 : Nat := 4983230072969 + 3 ^ 40 * 5461109 * 2
def baseEnd_5461109 : Nat := 2804173823594579119622323

theorem tailTrace_5461109 : CollatzResearch.WordTrace tailWord_5461109 prefixEnd_5461109 2804173823594579119622323 := by
  unfold tailWord_5461109
  simp only [CollatzResearch.WordTrace]
  refine ⟨199183008772342251007610381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132788672514894834005073587 199183008772342251007610381)
  ·
    refine ⟨74693628289628344127853893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199183008772342251007610381 74693628289628344127853893)
    ·
      refine ⟨14005055304305314523972605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74693628289628344127853893 14005055304305314523972605)
      ·
        refine ⟨5251895739114492946489727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14005055304305314523972605 5251895739114492946489727)
        ·
          refine ⟨7877843608671739419734591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5251895739114492946489727 7877843608671739419734591)
          ·
            refine ⟨11816765413007609129601887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7877843608671739419734591 11816765413007609129601887)
            ·
              refine ⟨17725148119511413694402831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11816765413007609129601887 17725148119511413694402831)
              ·
                refine ⟨26587722179267120541604247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17725148119511413694402831 26587722179267120541604247)
                ·
                  refine ⟨39881583268900680812406371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26587722179267120541604247 39881583268900680812406371)
                  ·
                    refine ⟨59822374903351021218609557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39881583268900680812406371 59822374903351021218609557)
                    ·
                      refine ⟨2804173823594579119622323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59822374903351021218609557 2804173823594579119622323)
                      ·
                        rfl

theorem cell23_5461109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_5461109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461109 prefixEnd_5461109 := by exact prefixLift 5461109
  have htrace : WordTrace (prefixWord ++ tailWord_5461109) baseStart_5461109 baseEnd_5461109 := by
    simpa [prefixWord, tailWord_5461109, baseEnd_5461109] using wordTrace_append hprefix tailTrace_5461109
  have hstable : (prefixWord ++ tailWord_5461109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461109).length < 2 ^ (prefixWord ++ tailWord_5461109).sum := by decide
  have hdescent : baseEnd_5461109 < baseStart_5461109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461112 : List Nat := [2, 1, 2, 1, 1, 1, 7, 1, 1, 3, 3]
def baseStart_5461112 : Nat := 118140960795 + 5461112 * 2 ^ 59
def prefixEnd_5461112 : Nat := 4983230072969 + 3 ^ 40 * 5461112 * 2
def baseEnd_5461112 : Nat := 2804175364036542607884809

theorem tailTrace_5461112 : CollatzResearch.WordTrace tailWord_5461112 prefixEnd_5461112 2804175364036542607884809 := by
  unfold tailWord_5461112
  simp only [CollatzResearch.WordTrace]
  refine ⟨99591559095665691259984795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132788745460887588346646393 99591559095665691259984795)
  ·
    refine ⟨149387338643498536889977193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99591559095665691259984795 149387338643498536889977193)
    ·
      refine ⟨112040503982623902667482895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149387338643498536889977193 112040503982623902667482895)
      ·
        refine ⟨168060755973935854001224343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112040503982623902667482895 168060755973935854001224343)
        ·
          refine ⟨252091133960903781001836515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168060755973935854001224343 252091133960903781001836515)
          ·
            refine ⟨378136700941355671502754773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252091133960903781001836515 378136700941355671502754773)
            ·
              refine ⟨8862578928313023550845815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 378136700941355671502754773 8862578928313023550845815)
              ·
                refine ⟨13293868392469535326268723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8862578928313023550845815 13293868392469535326268723)
                ·
                  refine ⟨19940802588704302989403085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13293868392469535326268723 19940802588704302989403085)
                  ·
                    refine ⟨7477800970764113621026157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19940802588704302989403085 7477800970764113621026157)
                    ·
                      refine ⟨2804175364036542607884809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7477800970764113621026157 2804175364036542607884809)
                      ·
                        rfl

theorem cell23_5461112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 7, 1, 1, 3, 3].length) (baseStart_5461112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461112 prefixEnd_5461112 := by exact prefixLift 5461112
  have htrace : WordTrace (prefixWord ++ tailWord_5461112) baseStart_5461112 baseEnd_5461112 := by
    simpa [prefixWord, tailWord_5461112, baseEnd_5461112] using wordTrace_append hprefix tailTrace_5461112
  have hstable : (prefixWord ++ tailWord_5461112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461112).length < 2 ^ (prefixWord ++ tailWord_5461112).sum := by decide
  have hdescent : baseEnd_5461112 < baseStart_5461112 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461139 : List Nat := [1, 1, 1, 2, 1, 2, 6, 3, 1, 3, 2]
def baseStart_5461139 : Nat := 118140960795 + 5461139 * 2 ^ 59
def prefixEnd_5461139 : Nat := 4983230072969 + 3 ^ 40 * 5461139 * 2
def baseEnd_5461139 : Nat := 2804189228014214002247185

theorem tailTrace_5461139 : CollatzResearch.WordTrace tailWord_5461139 prefixEnd_5461139 2804189228014214002247185 := by
  unfold tailWord_5461139
  simp only [CollatzResearch.WordTrace]
  refine ⟨199184102962233566131202471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132789401974822377420801647 199184102962233566131202471)
  ·
    refine ⟨298776154443350349196803707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199184102962233566131202471 298776154443350349196803707)
    ·
      refine ⟨448164231665025523795205561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298776154443350349196803707 448164231665025523795205561)
      ·
        refine ⟨336123173748769142846404171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448164231665025523795205561 336123173748769142846404171)
        ·
          refine ⟨504184760623153714269606257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336123173748769142846404171 504184760623153714269606257)
          ·
            refine ⟨378138570467365285702204693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 504184760623153714269606257 378138570467365285702204693)
            ·
              refine ⟨17725245490657747767290845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 378138570467365285702204693 17725245490657747767290845)
              ·
                refine ⟨6646967058996655412734067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17725245490657747767290845 6646967058996655412734067)
                ·
                  refine ⟨9970450588494983119101101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6646967058996655412734067 9970450588494983119101101)
                  ·
                    refine ⟨3738918970685618669662913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9970450588494983119101101 3738918970685618669662913)
                    ·
                      refine ⟨2804189228014214002247185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3738918970685618669662913 2804189228014214002247185)
                      ·
                        rfl

theorem cell23_5461139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 1, 3, 2].length) (baseStart_5461139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461139 prefixEnd_5461139 := by exact prefixLift 5461139
  have htrace : WordTrace (prefixWord ++ tailWord_5461139) baseStart_5461139 baseEnd_5461139 := by
    simpa [prefixWord, tailWord_5461139, baseEnd_5461139] using wordTrace_append hprefix tailTrace_5461139
  have hstable : (prefixWord ++ tailWord_5461139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461139).length < 2 ^ (prefixWord ++ tailWord_5461139).sum := by decide
  have hdescent : baseEnd_5461139 < baseStart_5461139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461175 : List Nat := [1, 1, 3, 1, 4, 1, 2, 1, 9]
def baseStart_5461175 : Nat := 118140960795 + 5461175 * 2 ^ 59
def prefixEnd_5461175 : Nat := 4983230072969 + 3 ^ 40 * 5461175 * 2
def baseEnd_5461175 : Nat := 311578634813086206821891

theorem tailTrace_5461175 : CollatzResearch.WordTrace tailWord_5461175 prefixEnd_5461175 311578634813086206821891 := by
  unfold tailWord_5461175
  simp only [CollatzResearch.WordTrace]
  refine ⟨199185415990103144279512979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132790277326735429519675319 199185415990103144279512979)
  ·
    refine ⟨298778123985154716419269469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199185415990103144279512979 298778123985154716419269469)
    ·
      refine ⟨112041796494433018657226051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298778123985154716419269469 112041796494433018657226051)
      ·
        refine ⟨168062694741649527985839077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112041796494433018657226051 168062694741649527985839077)
        ·
          refine ⟨31511755264059286497344827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168062694741649527985839077 31511755264059286497344827)
          ·
            refine ⟨47267632896088929746017241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31511755264059286497344827 47267632896088929746017241)
            ·
              refine ⟨35450724672066697309512931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47267632896088929746017241 35450724672066697309512931)
              ·
                refine ⟨53176087008100045964269397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35450724672066697309512931 53176087008100045964269397)
                ·
                  refine ⟨311578634813086206821891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53176087008100045964269397 311578634813086206821891)
                  ·
                    rfl

theorem cell23_5461175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 2, 1, 9].length) (baseStart_5461175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461175 prefixEnd_5461175 := by exact prefixLift 5461175
  have htrace : WordTrace (prefixWord ++ tailWord_5461175) baseStart_5461175 baseEnd_5461175 := by
    simpa [prefixWord, tailWord_5461175, baseEnd_5461175] using wordTrace_append hprefix tailTrace_5461175
  have hstable : (prefixWord ++ tailWord_5461175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461175).length < 2 ^ (prefixWord ++ tailWord_5461175).sum := by decide
  have hdescent : baseEnd_5461175 < baseStart_5461175 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461242 : List Nat := [3, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4]
def baseStart_5461242 : Nat := 118140960795 + 5461242 * 2 ^ 59
def prefixEnd_5461242 : Nat := 4983230072969 + 3 ^ 40 * 5461242 * 2
def baseEnd_5461242 : Nat := 2804242116521627099259211

theorem tailTrace_5461242 : CollatzResearch.WordTrace tailWord_5461242 prefixEnd_5461242 2804242116521627099259211 := by
  unfold tailWord_5461242
  simp only [CollatzResearch.WordTrace]
  refine ⟨49796964920215103680550495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132791906453906943148134653 49796964920215103680550495)
  ·
    refine ⟨74695447380322655520825743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49796964920215103680550495 74695447380322655520825743)
    ·
      refine ⟨112043171070483983281238615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74695447380322655520825743 112043171070483983281238615)
      ·
        refine ⟨168064756605725974921857923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112043171070483983281238615 168064756605725974921857923)
        ·
          refine ⟨252097134908588962382786885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168064756605725974921857923 252097134908588962382786885)
          ·
            refine ⟨47268212795360430446772541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 252097134908588962382786885 47268212795360430446772541)
            ·
              refine ⟨17725579798260161417539703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47268212795360430446772541 17725579798260161417539703)
              ·
                refine ⟨26588369697390242126309555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17725579798260161417539703 26588369697390242126309555)
                ·
                  refine ⟨39882554546085363189464333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26588369697390242126309555 39882554546085363189464333)
                  ·
                    refine ⟨14955957954782011196049125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39882554546085363189464333 14955957954782011196049125)
                    ·
                      refine ⟨2804242116521627099259211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14955957954782011196049125 2804242116521627099259211)
                      ·
                        rfl

theorem cell23_5461242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_5461242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461242 prefixEnd_5461242 := by exact prefixLift 5461242
  have htrace : WordTrace (prefixWord ++ tailWord_5461242) baseStart_5461242 baseEnd_5461242 := by
    simpa [prefixWord, tailWord_5461242, baseEnd_5461242] using wordTrace_append hprefix tailTrace_5461242
  have hstable : (prefixWord ++ tailWord_5461242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461242).length < 2 ^ (prefixWord ++ tailWord_5461242).sum := by decide
  have hdescent : baseEnd_5461242 < baseStart_5461242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461259 : List Nat := [1, 1, 1, 1, 5, 3, 1, 2, 2, 4, 2]
def baseStart_5461259 : Nat := 118140960795 + 5461259 * 2 ^ 59
def prefixEnd_5461259 : Nat := 4983230072969 + 3 ^ 40 * 5461259 * 2
def baseEnd_5461259 : Nat := 2804250845692753532746633

theorem tailTrace_5461259 : CollatzResearch.WordTrace tailWord_5461259 prefixEnd_5461259 2804250845692753532746633 := by
  unfold tailWord_5461259
  simp only [CollatzResearch.WordTrace]
  refine ⟨199188479721798826625570831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132792319814532551083713887 199188479721798826625570831)
  ·
    refine ⟨298782719582698239938356247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199188479721798826625570831 298782719582698239938356247)
    ·
      refine ⟨448174079374047359907534371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298782719582698239938356247 448174079374047359907534371)
      ·
        refine ⟨672261119061071039861301557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448174079374047359907534371 672261119061071039861301557)
        ·
          refine ⟨63024479911975409986997021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 672261119061071039861301557 63024479911975409986997021)
          ·
            refine ⟨23634179966990778745123883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63024479911975409986997021 23634179966990778745123883)
            ·
              refine ⟨35451269950486168117685825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23634179966990778745123883 35451269950486168117685825)
              ·
                refine ⟨26588452462864626088264369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35451269950486168117685825 26588452462864626088264369)
                ·
                  refine ⟨19941339347148469566198277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26588452462864626088264369 19941339347148469566198277)
                  ·
                    refine ⟨3739001127590338043662177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19941339347148469566198277 3739001127590338043662177)
                    ·
                      refine ⟨2804250845692753532746633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3739001127590338043662177 2804250845692753532746633)
                      ·
                        rfl

theorem cell23_5461259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 1, 2, 2, 4, 2].length) (baseStart_5461259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461259 prefixEnd_5461259 := by exact prefixLift 5461259
  have htrace : WordTrace (prefixWord ++ tailWord_5461259) baseStart_5461259 baseEnd_5461259 := by
    simpa [prefixWord, tailWord_5461259, baseEnd_5461259] using wordTrace_append hprefix tailTrace_5461259
  have hstable : (prefixWord ++ tailWord_5461259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461259).length < 2 ^ (prefixWord ++ tailWord_5461259).sum := by decide
  have hdescent : baseEnd_5461259 < baseStart_5461259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461292 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 3]
def baseStart_5461292 : Nat := 118140960795 + 5461292 * 2 ^ 59
def prefixEnd_5461292 : Nat := 4983230072969 + 3 ^ 40 * 5461292 * 2
def baseEnd_5461292 : Nat := 2804267790554351903633981

theorem tailTrace_5461292 : CollatzResearch.WordTrace tailWord_5461292 prefixEnd_5461292 2804267790554351903633981 := by
  unfold tailWord_5461292
  simp only [CollatzResearch.WordTrace]
  refine ⟨99594841665339636630761065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132793122220452848841014753 99594841665339636630761065)
  ·
    refine ⟨74696131249004727473070799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99594841665339636630761065 74696131249004727473070799)
    ·
      refine ⟨112044196873507091209606199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74696131249004727473070799 112044196873507091209606199)
      ·
        refine ⟨168066295310260636814409299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112044196873507091209606199 168066295310260636814409299)
        ·
          refine ⟨252099442965390955221613949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168066295310260636814409299 252099442965390955221613949)
          ·
            refine ⟨94537291112021608208105231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252099442965390955221613949 94537291112021608208105231)
            ·
              refine ⟨141805936668032412312157847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94537291112021608208105231 141805936668032412312157847)
              ·
                refine ⟨212708905002048618468236771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141805936668032412312157847 212708905002048618468236771)
                ·
                  refine ⟨319063357503072927702355157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 212708905002048618468236771 319063357503072927702355157)
                  ·
                    refine ⟨7478047441478271743023949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 319063357503072927702355157 7478047441478271743023949)
                    ·
                      refine ⟨2804267790554351903633981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7478047441478271743023949 2804267790554351903633981)
                      ·
                        rfl

theorem cell23_5461292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_5461292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461292 prefixEnd_5461292 := by exact prefixLift 5461292
  have htrace : WordTrace (prefixWord ++ tailWord_5461292) baseStart_5461292 baseEnd_5461292 := by
    simpa [prefixWord, tailWord_5461292, baseEnd_5461292] using wordTrace_append hprefix tailTrace_5461292
  have hstable : (prefixWord ++ tailWord_5461292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461292).length < 2 ^ (prefixWord ++ tailWord_5461292).sum := by decide
  have hdescent : baseEnd_5461292 < baseStart_5461292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461349 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 3, 1, 4]
def baseStart_5461349 : Nat := 118140960795 + 5461349 * 2 ^ 59
def prefixEnd_5461349 : Nat := 4983230072969 + 3 ^ 40 * 5461349 * 2
def baseEnd_5461349 : Nat := 2804297058951658180621219

theorem tailTrace_5461349 : CollatzResearch.WordTrace tailWord_5461349 prefixEnd_5461349 2804297058951658180621219 := by
  unfold tailWord_5461349
  simp only [CollatzResearch.WordTrace]
  refine ⟨199191762291472771996347101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132794508194315181330898067 199191762291472771996347101)
  ·
    refine ⟨74696910859302289498630163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199191762291472771996347101 74696910859302289498630163)
    ·
      refine ⟨112045366288953434247945245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74696910859302289498630163 112045366288953434247945245)
      ·
        refine ⟨42017012358357537842979467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112045366288953434247945245 42017012358357537842979467)
        ·
          refine ⟨63025518537536306764469201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42017012358357537842979467 63025518537536306764469201)
          ·
            refine ⟨47269138903152230073351901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63025518537536306764469201 47269138903152230073351901)
            ·
              refine ⟨17725927088682086277506963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47269138903152230073351901 17725927088682086277506963)
              ·
                refine ⟨26588890633023129416260445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17725927088682086277506963 26588890633023129416260445)
                ·
                  refine ⟨9970833987383673531097667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26588890633023129416260445 9970833987383673531097667)
                  ·
                    refine ⟨14956250981075510296646501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9970833987383673531097667 14956250981075510296646501)
                    ·
                      refine ⟨2804297058951658180621219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14956250981075510296646501 2804297058951658180621219)
                      ·
                        rfl

theorem cell23_5461349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_5461349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461349 prefixEnd_5461349 := by exact prefixLift 5461349
  have htrace : WordTrace (prefixWord ++ tailWord_5461349) baseStart_5461349 baseEnd_5461349 := by
    simpa [prefixWord, tailWord_5461349, baseEnd_5461349] using wordTrace_append hprefix tailTrace_5461349
  have hstable : (prefixWord ++ tailWord_5461349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461349).length < 2 ^ (prefixWord ++ tailWord_5461349).sum := by decide
  have hdescent : baseEnd_5461349 < baseStart_5461349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461369 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 1, 1, 5]
def baseStart_5461369 : Nat := 118140960795 + 5461369 * 2 ^ 59
def prefixEnd_5461369 : Nat := 4983230072969 + 3 ^ 40 * 5461369 * 2
def baseEnd_5461369 : Nat := 2804307328564748102371127

theorem tailTrace_5461369 : CollatzResearch.WordTrace tailWord_5461369 prefixEnd_5461369 2804307328564748102371127 := by
  unfold tailWord_5461369
  simp only [CollatzResearch.WordTrace]
  refine ⟨199192491751400315412075161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132794994500933543608050107 199192491751400315412075161)
  ·
    refine ⟨149394368813550236559056371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199192491751400315412075161 149394368813550236559056371)
    ·
      refine ⟨224091553220325354838584557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149394368813550236559056371 224091553220325354838584557)
      ·
        refine ⟨84034332457622008064469209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224091553220325354838584557 84034332457622008064469209)
        ·
          refine ⟨63025749343216506048351907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84034332457622008064469209 63025749343216506048351907)
          ·
            refine ⟨94538624014824759072527861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63025749343216506048351907 94538624014824759072527861)
            ·
              refine ⟨8862996001389821163049487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94538624014824759072527861 8862996001389821163049487)
              ·
                refine ⟨13294494002084731744574231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8862996001389821163049487 13294494002084731744574231)
                ·
                  refine ⟨19941741003127097616861347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13294494002084731744574231 19941741003127097616861347)
                  ·
                    refine ⟨29912611504690646425292021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19941741003127097616861347 29912611504690646425292021)
                    ·
                      refine ⟨2804307328564748102371127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29912611504690646425292021 2804307328564748102371127)
                      ·
                        rfl

theorem cell23_5461369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_5461369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461369 prefixEnd_5461369 := by exact prefixLift 5461369
  have htrace : WordTrace (prefixWord ++ tailWord_5461369) baseStart_5461369 baseEnd_5461369 := by
    simpa [prefixWord, tailWord_5461369, baseEnd_5461369] using wordTrace_append hprefix tailTrace_5461369
  have hstable : (prefixWord ++ tailWord_5461369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461369).length < 2 ^ (prefixWord ++ tailWord_5461369).sum := by decide
  have hdescent : baseEnd_5461369 < baseStart_5461369 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461396 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 1, 2, 4]
def baseStart_5461396 : Nat := 118140960795 + 5461396 * 2 ^ 59
def prefixEnd_5461396 : Nat := 4983230072969 + 3 ^ 40 * 5461396 * 2
def baseEnd_5461396 : Nat := 2804321192542419496733503

theorem tailTrace_5461396 : CollatzResearch.WordTrace tailWord_5461396 prefixEnd_5461396 2804321192542419496733503 := by
  unfold tailWord_5461396
  simp only [CollatzResearch.WordTrace]
  refine ⟨99596738261151249511654021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132795651014868332682205361 99596738261151249511654021)
  ·
    refine ⟨18674388423965859283435129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99596738261151249511654021 18674388423965859283435129)
    ·
      refine ⟨14005791317974394462576347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18674388423965859283435129 14005791317974394462576347)
      ·
        refine ⟨21008686976961591693864521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14005791317974394462576347 21008686976961591693864521)
        ·
          refine ⟨15756515232721193770398391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21008686976961591693864521 15756515232721193770398391)
          ·
            refine ⟨23634772849081790655597587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15756515232721193770398391 23634772849081790655597587)
            ·
              refine ⟨35452159273622685983396381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23634772849081790655597587 35452159273622685983396381)
              ·
                refine ⟨13294559727608507243773643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35452159273622685983396381 13294559727608507243773643)
                ·
                  refine ⟨19941839591412760865660465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13294559727608507243773643 19941839591412760865660465)
                  ·
                    refine ⟨14956379693559570649245349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19941839591412760865660465 14956379693559570649245349)
                    ·
                      refine ⟨2804321192542419496733503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14956379693559570649245349 2804321192542419496733503)
                      ·
                        rfl

theorem cell23_5461396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_5461396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461396 prefixEnd_5461396 := by exact prefixLift 5461396
  have htrace : WordTrace (prefixWord ++ tailWord_5461396) baseStart_5461396 baseEnd_5461396 := by
    simpa [prefixWord, tailWord_5461396, baseEnd_5461396] using wordTrace_append hprefix tailTrace_5461396
  have hstable : (prefixWord ++ tailWord_5461396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461396).length < 2 ^ (prefixWord ++ tailWord_5461396).sum := by decide
  have hdescent : baseEnd_5461396 < baseStart_5461396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461400 : List Nat := [2, 1, 2, 5, 2, 1, 1, 2, 3, 2, 2]
def baseStart_5461400 : Nat := 118140960795 + 5461400 * 2 ^ 59
def prefixEnd_5461400 : Nat := 4983230072969 + 3 ^ 40 * 5461400 * 2
def baseEnd_5461400 : Nat := 2804323246465037481083485

theorem tailTrace_5461400 : CollatzResearch.WordTrace tailWord_5461400 prefixEnd_5461400 2804323246465037481083485 := by
  unfold tailWord_5461400
  simp only [CollatzResearch.WordTrace]
  refine ⟨99596811207144003853226827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132795748276192005137635769 99596811207144003853226827)
  ·
    refine ⟨149395216810716005779840241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99596811207144003853226827 149395216810716005779840241)
    ·
      refine ⟨112046412608037004334880181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149395216810716005779840241 112046412608037004334880181)
      ·
        refine ⟨10504351182003469156395017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 112046412608037004334880181 10504351182003469156395017)
        ·
          refine ⟨7878263386502601867296263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10504351182003469156395017 7878263386502601867296263)
          ·
            refine ⟨11817395079753902800944395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7878263386502601867296263 11817395079753902800944395)
            ·
              refine ⟨17726092619630854201416593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11817395079753902800944395 17726092619630854201416593)
              ·
                refine ⟨13294569464723140651062445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17726092619630854201416593 13294569464723140651062445)
                ·
                  refine ⟨4985463549271177744148417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13294569464723140651062445 4985463549271177744148417)
                  ·
                    refine ⟨3739097661953383308111313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4985463549271177744148417 3739097661953383308111313)
                    ·
                      refine ⟨2804323246465037481083485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3739097661953383308111313 2804323246465037481083485)
                      ·
                        rfl

theorem cell23_5461400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 2, 3, 2, 2].length) (baseStart_5461400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461400 prefixEnd_5461400 := by exact prefixLift 5461400
  have htrace : WordTrace (prefixWord ++ tailWord_5461400) baseStart_5461400 baseEnd_5461400 := by
    simpa [prefixWord, tailWord_5461400, baseEnd_5461400] using wordTrace_append hprefix tailTrace_5461400
  have hstable : (prefixWord ++ tailWord_5461400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461400).length < 2 ^ (prefixWord ++ tailWord_5461400).sum := by decide
  have hdescent : baseEnd_5461400 < baseStart_5461400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461426 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2]
def baseStart_5461426 : Nat := 118140960795 + 5461426 * 2 ^ 59
def prefixEnd_5461426 : Nat := 4983230072969 + 3 ^ 40 * 5461426 * 2
def baseEnd_5461426 : Nat := 2804336596962054379358365

theorem tailTrace_5461426 : CollatzResearch.WordTrace tailWord_5461426 prefixEnd_5461426 2804336596962054379358365 := by
  unfold tailWord_5461426
  simp only [CollatzResearch.WordTrace]
  refine ⟨49798642678048453536725033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132796380474795876097933421 49798642678048453536725033)
  ·
    refine ⟨37348982008536340152543775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49798642678048453536725033 37348982008536340152543775)
    ·
      refine ⟨56023473012804510228815663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37348982008536340152543775 56023473012804510228815663)
      ·
        refine ⟨84035209519206765343223495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56023473012804510228815663 84035209519206765343223495)
        ·
          refine ⟨126052814278810148014835243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84035209519206765343223495 126052814278810148014835243)
          ·
            refine ⟨189079221418215222022252865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126052814278810148014835243 189079221418215222022252865)
            ·
              refine ⟨141809416063661416516689649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189079221418215222022252865 141809416063661416516689649)
              ·
                refine ⟨106357062047746062387517237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141809416063661416516689649 106357062047746062387517237)
                ·
                  refine ⟨9970974566976193348829741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106357062047746062387517237 9970974566976193348829741)
                  ·
                    refine ⟨3739115462616072505811153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9970974566976193348829741 3739115462616072505811153)
                    ·
                      refine ⟨2804336596962054379358365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3739115462616072505811153 2804336596962054379358365)
                      ·
                        rfl

theorem cell23_5461426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 5, 3, 2].length) (baseStart_5461426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461426 prefixEnd_5461426 := by exact prefixLift 5461426
  have htrace : WordTrace (prefixWord ++ tailWord_5461426) baseStart_5461426 baseEnd_5461426 := by
    simpa [prefixWord, tailWord_5461426, baseEnd_5461426] using wordTrace_append hprefix tailTrace_5461426
  have hstable : (prefixWord ++ tailWord_5461426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461426).length < 2 ^ (prefixWord ++ tailWord_5461426).sum := by decide
  have hdescent : baseEnd_5461426 < baseStart_5461426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461433 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 4, 1, 3]
def baseStart_5461433 : Nat := 118140960795 + 5461433 * 2 ^ 59
def prefixEnd_5461433 : Nat := 4983230072969 + 3 ^ 40 * 5461433 * 2
def baseEnd_5461433 : Nat := 2804340191326635851970833

theorem tailTrace_5461433 : CollatzResearch.WordTrace tailWord_5461433 prefixEnd_5461433 2804340191326635851970833 := by
  unfold tailWord_5461433
  simp only [CollatzResearch.WordTrace]
  refine ⟨199194826023168454342404953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132796550682112302894936635 199194826023168454342404953)
  ·
    refine ⟨149396119517376340756803715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199194826023168454342404953 149396119517376340756803715)
    ·
      refine ⟨224094179276064511135205573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149396119517376340756803715 224094179276064511135205573)
      ·
        refine ⟨42017658614262095837851045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224094179276064511135205573 42017658614262095837851045)
        ·
          refine ⟨7878310990174142969597071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42017658614262095837851045 7878310990174142969597071)
          ·
            refine ⟨11817466485261214454395607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7878310990174142969597071 11817466485261214454395607)
            ·
              refine ⟨17726199727891821681593411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11817466485261214454395607 17726199727891821681593411)
              ·
                refine ⟨26589299591837732522390117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17726199727891821681593411 26589299591837732522390117)
                ·
                  refine ⟨4985493673469574847948147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26589299591837732522390117 4985493673469574847948147)
                  ·
                    refine ⟨7478240510204362271922221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4985493673469574847948147 7478240510204362271922221)
                    ·
                      refine ⟨2804340191326635851970833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7478240510204362271922221 2804340191326635851970833)
                      ·
                        rfl

theorem cell23_5461433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_5461433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461433 prefixEnd_5461433 := by exact prefixLift 5461433
  have htrace : WordTrace (prefixWord ++ tailWord_5461433) baseStart_5461433 baseEnd_5461433 := by
    simpa [prefixWord, tailWord_5461433, baseEnd_5461433] using wordTrace_append hprefix tailTrace_5461433
  have hstable : (prefixWord ++ tailWord_5461433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461433).length < 2 ^ (prefixWord ++ tailWord_5461433).sum := by decide
  have hdescent : baseEnd_5461433 < baseStart_5461433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461450 : List Nat := [3, 1, 2, 1, 2, 4, 3, 1, 2, 1, 3]
def baseStart_5461450 : Nat := 118140960795 + 5461450 * 2 ^ 59
def prefixEnd_5461450 : Nat := 4983230072969 + 3 ^ 40 * 5461450 * 2
def baseEnd_5461450 : Nat := 2804348920497762285458255

theorem tailTrace_5461450 : CollatzResearch.WordTrace tailWord_5461450 prefixEnd_5461450 2804348920497762285458255 := by
  unfold tailWord_5461450
  simp only [CollatzResearch.WordTrace]
  refine ⟨49798861516026716561443451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132796964042737910830515869 49798861516026716561443451)
  ·
    refine ⟨74698292274040074842165177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49798861516026716561443451 74698292274040074842165177)
    ·
      refine ⟨56023719205530056131623883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74698292274040074842165177 56023719205530056131623883)
      ·
        refine ⟨84035578808295084197435825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56023719205530056131623883 84035578808295084197435825)
        ·
          refine ⟨63026684106221313148076869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84035578808295084197435825 63026684106221313148076869)
          ·
            refine ⟨11817503269916496215264413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63026684106221313148076869 11817503269916496215264413)
            ·
              refine ⟨4431563726218686080724155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11817503269916496215264413 4431563726218686080724155)
              ·
                refine ⟨6647345589328029121086233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4431563726218686080724155 6647345589328029121086233)
                ·
                  refine ⟨4985509191996021840814675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6647345589328029121086233 4985509191996021840814675)
                  ·
                    refine ⟨7478263787994032761222013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4985509191996021840814675 7478263787994032761222013)
                    ·
                      refine ⟨2804348920497762285458255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7478263787994032761222013 2804348920497762285458255)
                      ·
                        rfl

theorem cell23_5461450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 2, 1, 3].length) (baseStart_5461450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461450 prefixEnd_5461450 := by exact prefixLift 5461450
  have htrace : WordTrace (prefixWord ++ tailWord_5461450) baseStart_5461450 baseEnd_5461450 := by
    simpa [prefixWord, tailWord_5461450, baseEnd_5461450] using wordTrace_append hprefix tailTrace_5461450
  have hstable : (prefixWord ++ tailWord_5461450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461450).length < 2 ^ (prefixWord ++ tailWord_5461450).sum := by decide
  have hdescent : baseEnd_5461450 < baseStart_5461450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461473 : List Nat := [1, 2, 3, 1, 2, 3, 1, 2, 4, 2, 2]
def baseStart_5461473 : Nat := 118140960795 + 5461473 * 2 ^ 59
def prefixEnd_5461473 : Nat := 4983230072969 + 3 ^ 40 * 5461473 * 2
def baseEnd_5461473 : Nat := 2804360730552815695470649

theorem tailTrace_5461473 : CollatzResearch.WordTrace tailWord_5461473 prefixEnd_5461473 2804360730552815695470649 := by
  unfold tailWord_5461473
  simp only [CollatzResearch.WordTrace]
  refine ⟨199196284943023541173861073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132797523295349027449240715 199196284943023541173861073)
  ·
    refine ⟨149397213707267655880395805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199196284943023541173861073 149397213707267655880395805)
    ·
      refine ⟨56023955140225370955148427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149397213707267655880395805 56023955140225370955148427)
      ·
        refine ⟨84035932710338056432722641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56023955140225370955148427 84035932710338056432722641)
        ·
          refine ⟨63026949532753542324541981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84035932710338056432722641 63026949532753542324541981)
          ·
            refine ⟨23635106074782578371703243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63026949532753542324541981 23635106074782578371703243)
            ·
              refine ⟨35452659112173867557554865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23635106074782578371703243 35452659112173867557554865)
              ·
                refine ⟨26589494334130400668166149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35452659112173867557554865 26589494334130400668166149)
                ·
                  refine ⟨4985530187649450125281153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26589494334130400668166149 4985530187649450125281153)
                  ·
                    refine ⟨3739147640737087593960865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4985530187649450125281153 3739147640737087593960865)
                    ·
                      refine ⟨2804360730552815695470649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3739147640737087593960865 2804360730552815695470649)
                      ·
                        rfl

theorem cell23_5461473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 2, 2].length) (baseStart_5461473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461473 prefixEnd_5461473 := by exact prefixLift 5461473
  have htrace : WordTrace (prefixWord ++ tailWord_5461473) baseStart_5461473 baseEnd_5461473 := by
    simpa [prefixWord, tailWord_5461473, baseEnd_5461473] using wordTrace_append hprefix tailTrace_5461473
  have hstable : (prefixWord ++ tailWord_5461473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461473).length < 2 ^ (prefixWord ++ tailWord_5461473).sum := by decide
  have hdescent : baseEnd_5461473 < baseStart_5461473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461490 : List Nat := [3, 2, 1, 4, 1, 1, 2, 1, 4, 2, 2]
def baseStart_5461490 : Nat := 118140960795 + 5461490 * 2 ^ 59
def prefixEnd_5461490 : Nat := 4983230072969 + 3 ^ 40 * 5461490 * 2
def baseEnd_5461490 : Nat := 2804369459723942128958071

theorem tailTrace_5461490 : CollatzResearch.WordTrace tailWord_5461490 prefixEnd_5461490 2804369459723942128958071 := by
  unfold tailWord_5461490
  simp only [CollatzResearch.WordTrace]
  refine ⟨49799226245990488269307481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132797936655974635384819949 49799226245990488269307481)
  ·
    refine ⟨37349419684492866201980611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49799226245990488269307481 37349419684492866201980611)
    ·
      refine ⟨56024129526739299302970917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37349419684492866201980611 56024129526739299302970917)
      ·
        refine ⟨10504524286263618619307047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56024129526739299302970917 10504524286263618619307047)
        ·
          refine ⟨15756786429395427928960571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10504524286263618619307047 15756786429395427928960571)
          ·
            refine ⟨23635179644093141893440857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15756786429395427928960571 23635179644093141893440857)
            ·
              refine ⟨17726384733069856420080643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23635179644093141893440857 17726384733069856420080643)
              ·
                refine ⟨26589577099604784630120965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17726384733069856420080643 26589577099604784630120965)
                ·
                  refine ⟨4985545706175897118147681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26589577099604784630120965 4985545706175897118147681)
                  ·
                    refine ⟨3739159279631922838610761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4985545706175897118147681 3739159279631922838610761)
                    ·
                      refine ⟨2804369459723942128958071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3739159279631922838610761 2804369459723942128958071)
                      ·
                        rfl

theorem cell23_5461490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_5461490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461490 prefixEnd_5461490 := by exact prefixLift 5461490
  have htrace : WordTrace (prefixWord ++ tailWord_5461490) baseStart_5461490 baseEnd_5461490 := by
    simpa [prefixWord, tailWord_5461490, baseEnd_5461490] using wordTrace_append hprefix tailTrace_5461490
  have hstable : (prefixWord ++ tailWord_5461490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461490).length < 2 ^ (prefixWord ++ tailWord_5461490).sum := by decide
  have hdescent : baseEnd_5461490 < baseStart_5461490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461496 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 7]
def baseStart_5461496 : Nat := 118140960795 + 5461496 * 2 ^ 59
def prefixEnd_5461496 : Nat := 4983230072969 + 3 ^ 40 * 5461496 * 2
def baseEnd_5461496 : Nat := 311596948956429900609227

theorem tailTrace_5461496 : CollatzResearch.WordTrace tailWord_5461496 prefixEnd_5461496 311596948956429900609227 := by
  unfold tailWord_5461496
  simp only [CollatzResearch.WordTrace]
  refine ⟨99598561910970108050974171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132798082547960144067965561 99598561910970108050974171)
  ·
    refine ⟨149397842866455162076461257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99598561910970108050974171 149397842866455162076461257)
    ·
      refine ⟨112048382149841371557345943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149397842866455162076461257 112048382149841371557345943)
      ·
        refine ⟨168072573224762057336018915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112048382149841371557345943 168072573224762057336018915)
        ·
          refine ⟨252108859837143086004028373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168072573224762057336018915 252108859837143086004028373)
          ·
            refine ⟨5908801402433041078219415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 252108859837143086004028373 5908801402433041078219415)
            ·
              refine ⟨8863202103649561617329123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5908801402433041078219415 8863202103649561617329123)
              ·
                refine ⟨13294803155474342425993685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8863202103649561617329123 13294803155474342425993685)
                ·
                  refine ⟨311596948956429900609227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13294803155474342425993685 311596948956429900609227)
                  ·
                    rfl

theorem cell23_5461496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 7].length) (baseStart_5461496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461496 prefixEnd_5461496 := by exact prefixLift 5461496
  have htrace : WordTrace (prefixWord ++ tailWord_5461496) baseStart_5461496 baseEnd_5461496 := by
    simpa [prefixWord, tailWord_5461496, baseEnd_5461496] using wordTrace_append hprefix tailTrace_5461496
  have hstable : (prefixWord ++ tailWord_5461496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461496).length < 2 ^ (prefixWord ++ tailWord_5461496).sum := by decide
  have hdescent : baseEnd_5461496 < baseStart_5461496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461509 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 6, 5]
def baseStart_5461509 : Nat := 118140960795 + 5461509 * 2 ^ 59
def prefixEnd_5461509 : Nat := 4983230072969 + 3 ^ 40 * 5461509 * 2
def baseEnd_5461509 : Nat := 934793071952125851540161

theorem tailTrace_5461509 : CollatzResearch.WordTrace tailWord_5461509 prefixEnd_5461509 934793071952125851540161 := by
  unfold tailWord_5461509
  simp only [CollatzResearch.WordTrace]
  refine ⟨199197597970893119322171581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132798398647262079548114387 199197597970893119322171581)
  ·
    refine ⟨74699099239084919745814343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199197597970893119322171581 74699099239084919745814343)
    ·
      refine ⟨112048648858627379618721515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74699099239084919745814343 112048648858627379618721515)
      ·
        refine ⟨168072973287941069428082273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112048648858627379618721515 168072973287941069428082273)
        ·
          refine ⟨126054729965955802071061705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168072973287941069428082273 126054729965955802071061705)
          ·
            refine ⟨94541047474466851553296279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126054729965955802071061705 94541047474466851553296279)
            ·
              refine ⟨141811571211700277329944419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94541047474466851553296279 141811571211700277329944419)
              ·
                refine ⟨212717356817550415994916629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141811571211700277329944419 212717356817550415994916629)
                ·
                  refine ⟨9971126100822675749761717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 212717356817550415994916629 9971126100822675749761717)
                  ·
                    refine ⟨934793071952125851540161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9971126100822675749761717 934793071952125851540161)
                    ·
                      rfl

theorem cell23_5461509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_5461509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461509 prefixEnd_5461509 := by exact prefixLift 5461509
  have htrace : WordTrace (prefixWord ++ tailWord_5461509) baseStart_5461509 baseEnd_5461509 := by
    simpa [prefixWord, tailWord_5461509, baseEnd_5461509] using wordTrace_append hprefix tailTrace_5461509
  have hstable : (prefixWord ++ tailWord_5461509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461509).length < 2 ^ (prefixWord ++ tailWord_5461509).sum := by decide
  have hdescent : baseEnd_5461509 < baseStart_5461509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461536 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 5]
def baseStart_5461536 : Nat := 118140960795 + 5461536 * 2 ^ 59
def prefixEnd_5461536 : Nat := 4983230072969 + 3 ^ 40 * 5461536 * 2
def baseEnd_5461536 : Nat := 2804393079834048948982859

theorem tailTrace_5461536 : CollatzResearch.WordTrace tailWord_5461536 prefixEnd_5461536 2804393079834048948982859 := by
  unfold tailWord_5461536
  simp only [CollatzResearch.WordTrace]
  refine ⟨99599291370897651466702231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132799055161196868622269641 99599291370897651466702231)
  ·
    refine ⟨149398937056346477200053347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99599291370897651466702231 149398937056346477200053347)
    ·
      refine ⟨224098405584519715800080021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149398937056346477200053347 224098405584519715800080021)
      ·
        refine ⟨10504612761774361678128751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 224098405584519715800080021 10504612761774361678128751)
        ·
          refine ⟨15756919142661542517193127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10504612761774361678128751 15756919142661542517193127)
          ·
            refine ⟨23635378713992313775789691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15756919142661542517193127 23635378713992313775789691)
            ·
              refine ⟨35453068070988470663684537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23635378713992313775789691 35453068070988470663684537)
              ·
                refine ⟨26589801053241352997763403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35453068070988470663684537 26589801053241352997763403)
                ·
                  refine ⟨39884701579862029496645105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26589801053241352997763403 39884701579862029496645105)
                  ·
                    refine ⟨29913526184896522122483829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39884701579862029496645105 29913526184896522122483829)
                    ·
                      refine ⟨2804393079834048948982859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29913526184896522122483829 2804393079834048948982859)
                      ·
                        rfl

theorem cell23_5461536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_5461536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461536 prefixEnd_5461536 := by exact prefixLift 5461536
  have htrace : WordTrace (prefixWord ++ tailWord_5461536) baseStart_5461536 baseEnd_5461536 := by
    simpa [prefixWord, tailWord_5461536, baseEnd_5461536] using wordTrace_append hprefix tailTrace_5461536
  have hstable : (prefixWord ++ tailWord_5461536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461536).length < 2 ^ (prefixWord ++ tailWord_5461536).sum := by decide
  have hdescent : baseEnd_5461536 < baseStart_5461536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461603 : List Nat := [1, 1, 1, 5, 1, 5, 1, 2, 6]
def baseStart_5461603 : Nat := 118140960795 + 5461603 * 2 ^ 59
def prefixEnd_5461603 : Nat := 4983230072969 + 3 ^ 40 * 5461603 * 2
def baseEnd_5461603 : Nat := 311603053670877798538339

theorem tailTrace_5461603 : CollatzResearch.WordTrace tailWord_5461603 prefixEnd_5461603 311603053670877798538339 := by
  unfold tailWord_5461603
  simp only [CollatzResearch.WordTrace]
  refine ⟨199201026432552573376093463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132800684288368382250728975 199201026432552573376093463)
  ·
    refine ⟨298801539648828860064140195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199201026432552573376093463 298801539648828860064140195)
    ·
      refine ⟨448202309473243290096210293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298801539648828860064140195 448202309473243290096210293)
      ·
        refine ⟨42018966513116558446519715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 448202309473243290096210293 42018966513116558446519715)
        ·
          refine ⟨63028449769674837669779573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42018966513116558446519715 63028449769674837669779573)
          ·
            refine ⟨5908917165907016031541835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63028449769674837669779573 5908917165907016031541835)
            ·
              refine ⟨8863375748860524047312753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5908917165907016031541835 8863375748860524047312753)
              ·
                refine ⟨6647531811645393035484565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8863375748860524047312753 6647531811645393035484565)
                ·
                  refine ⟨311603053670877798538339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6647531811645393035484565 311603053670877798538339)
                  ·
                    rfl

theorem cell23_5461603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 2, 6].length) (baseStart_5461603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461603 prefixEnd_5461603 := by exact prefixLift 5461603
  have htrace : WordTrace (prefixWord ++ tailWord_5461603) baseStart_5461603 baseEnd_5461603 := by
    simpa [prefixWord, tailWord_5461603, baseEnd_5461603] using wordTrace_append hprefix tailTrace_5461603
  have hstable : (prefixWord ++ tailWord_5461603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461603).length < 2 ^ (prefixWord ++ tailWord_5461603).sum := by decide
  have hdescent : baseEnd_5461603 < baseStart_5461603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461633 : List Nat := [1, 2, 4, 2, 1, 2, 1, 4, 1, 5]
def baseStart_5461633 : Nat := 118140960795 + 5461633 * 2 ^ 59
def prefixEnd_5461633 : Nat := 4983230072969 + 3 ^ 40 * 5461633 * 2
def baseEnd_5461633 : Nat := 934814295819178356489971

theorem tailTrace_5461633 : CollatzResearch.WordTrace tailWord_5461633 prefixEnd_5461633 934814295819178356489971 := by
  unfold tailWord_5461633
  simp only [CollatzResearch.WordTrace]
  refine ⟨199202120622443888499685553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132801413748295925666457035 199202120622443888499685553)
  ·
    refine ⟨149401590466832916374764165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199202120622443888499685553 149401590466832916374764165)
    ·
      refine ⟨28012798212531171820268281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149401590466832916374764165 28012798212531171820268281)
      ·
        refine ⟨21009598659398378865201211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28012798212531171820268281 21009598659398378865201211)
        ·
          refine ⟨31514397989097568297801817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21009598659398378865201211 31514397989097568297801817)
          ·
            refine ⟨23635798491823176223351363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31514397989097568297801817 23635798491823176223351363)
            ·
              refine ⟨35453697737734764335027045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23635798491823176223351363 35453697737734764335027045)
              ·
                refine ⟨6647568325825268312817571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35453697737734764335027045 6647568325825268312817571)
                ·
                  refine ⟨9971352488737902469226357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6647568325825268312817571 9971352488737902469226357)
                  ·
                    refine ⟨934814295819178356489971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9971352488737902469226357 934814295819178356489971)
                    ·
                      rfl

theorem cell23_5461633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_5461633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461633 prefixEnd_5461633 := by exact prefixLift 5461633
  have htrace : WordTrace (prefixWord ++ tailWord_5461633) baseStart_5461633 baseEnd_5461633 := by
    simpa [prefixWord, tailWord_5461633, baseEnd_5461633] using wordTrace_append hprefix tailTrace_5461633
  have hstable : (prefixWord ++ tailWord_5461633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461633).length < 2 ^ (prefixWord ++ tailWord_5461633).sum := by decide
  have hdescent : baseEnd_5461633 < baseStart_5461633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461664 : List Nat := [2, 1, 1, 4, 3, 2, 3, 2, 1, 1, 3]
def baseStart_5461664 : Nat := 118140960795 + 5461664 * 2 ^ 59
def prefixEnd_5461664 : Nat := 4983230072969 + 3 ^ 40 * 5461664 * 2
def baseEnd_5461664 : Nat := 2804458805357824448182271

theorem tailTrace_5461664 : CollatzResearch.WordTrace tailWord_5461664 prefixEnd_5461664 2804458805357824448182271 := by
  unfold tailWord_5461664
  simp only [CollatzResearch.WordTrace]
  refine ⟨99601625642665790397032023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132802167523554387196042697 99601625642665790397032023)
  ·
    refine ⟨149402438463998685595548035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99601625642665790397032023 149402438463998685595548035)
    ·
      refine ⟨224103657695998028393322053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149402438463998685595548035 224103657695998028393322053)
      ·
        refine ⟨42019435817999630323747885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224103657695998028393322053 42019435817999630323747885)
        ·
          refine ⟨15757288431749861371405457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42019435817999630323747885 15757288431749861371405457)
          ·
            refine ⟨11817966323812396028554093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15757288431749861371405457 11817966323812396028554093)
            ·
              refine ⟨4431737371429648510707785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11817966323812396028554093 4431737371429648510707785)
              ·
                refine ⟨3323803028572236383030839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4431737371429648510707785 3323803028572236383030839)
                ·
                  refine ⟨4985704542858354574546259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3323803028572236383030839 4985704542858354574546259)
                  ·
                    refine ⟨7478556814287531861819389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4985704542858354574546259 7478556814287531861819389)
                    ·
                      refine ⟨2804458805357824448182271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7478556814287531861819389 2804458805357824448182271)
                      ·
                        rfl

theorem cell23_5461664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 3, 2, 1, 1, 3].length) (baseStart_5461664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461664 prefixEnd_5461664 := by exact prefixLift 5461664
  have htrace : WordTrace (prefixWord ++ tailWord_5461664) baseStart_5461664 baseEnd_5461664 := by
    simpa [prefixWord, tailWord_5461664, baseEnd_5461664] using wordTrace_append hprefix tailTrace_5461664
  have hstable : (prefixWord ++ tailWord_5461664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461664).length < 2 ^ (prefixWord ++ tailWord_5461664).sum := by decide
  have hdescent : baseEnd_5461664 < baseStart_5461664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461680 : List Nat := [2, 1, 1, 1, 2, 1, 8, 1, 2, 4]
def baseStart_5461680 : Nat := 118140960795 + 5461680 * 2 ^ 59
def prefixEnd_5461680 : Nat := 4983230072969 + 3 ^ 40 * 5461680 * 2
def baseEnd_5461680 : Nat := 934822340349432128527399

theorem tailTrace_5461680 : CollatzResearch.WordTrace tailWord_5461680 prefixEnd_5461680 934822340349432128527399 := by
  unfold tailWord_5461680
  simp only [CollatzResearch.WordTrace]
  refine ⟨99601917426636807763323247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132802556568849077017764329 99601917426636807763323247)
  ·
    refine ⟨149402876139955211644984871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99601917426636807763323247 149402876139955211644984871)
    ·
      refine ⟨224104314209932817467477307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149402876139955211644984871 224104314209932817467477307)
      ·
        refine ⟨336156471314899226201215961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224104314209932817467477307 336156471314899226201215961)
        ·
          refine ⟨252117353486174419650911971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336156471314899226201215961 252117353486174419650911971)
          ·
            refine ⟨378176030229261629476367957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252117353486174419650911971 378176030229261629476367957)
            ·
              refine ⟨4431750354249159720426187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 378176030229261629476367957 4431750354249159720426187)
              ·
                refine ⟨6647625531373739580639281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4431750354249159720426187 6647625531373739580639281)
                ·
                  refine ⟨4985719148530304685479461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6647625531373739580639281 4985719148530304685479461)
                  ·
                    refine ⟨934822340349432128527399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4985719148530304685479461 934822340349432128527399)
                    ·
                      rfl

theorem cell23_5461680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 2, 4].length) (baseStart_5461680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461680 prefixEnd_5461680 := by exact prefixLift 5461680
  have htrace : WordTrace (prefixWord ++ tailWord_5461680) baseStart_5461680 baseEnd_5461680 := by
    simpa [prefixWord, tailWord_5461680, baseEnd_5461680] using wordTrace_append hprefix tailTrace_5461680
  have hstable : (prefixWord ++ tailWord_5461680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461680).length < 2 ^ (prefixWord ++ tailWord_5461680).sum := by decide
  have hdescent : baseEnd_5461680 < baseStart_5461680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461690 : List Nat := [3, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3]
def baseStart_5461690 : Nat := 118140960795 + 5461690 * 2 ^ 59
def prefixEnd_5461690 : Nat := 4983230072969 + 3 ^ 40 * 5461690 * 2
def baseEnd_5461690 : Nat := 2804472155854841346457151

theorem tailTrace_5461690 : CollatzResearch.WordTrace tailWord_5461690 prefixEnd_5461690 2804472155854841346457151 := by
  unfold tailWord_5461690
  simp only [CollatzResearch.WordTrace]
  refine ⟨49801049895809346808627631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132802799722158258156340349 49801049895809346808627631)
  ·
    refine ⟨74701574843714020212941447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49801049895809346808627631 74701574843714020212941447)
    ·
      refine ⟨112052362265571030319412171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74701574843714020212941447 112052362265571030319412171)
      ·
        refine ⟨168078543398356545479118257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112052362265571030319412171 168078543398356545479118257)
        ·
          refine ⟨126058907548767409109338693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168078543398356545479118257 126058907548767409109338693)
          ·
            refine ⟨23636045165393889208001005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126058907548767409109338693 23636045165393889208001005)
            ·
              refine ⟨8863516937022708453000377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23636045165393889208001005 8863516937022708453000377)
              ·
                refine ⟨6647637702767031339750283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8863516937022708453000377 6647637702767031339750283)
                ·
                  refine ⟨9971456554150547009625425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6647637702767031339750283 9971456554150547009625425)
                  ·
                    refine ⟨7478592415612910257219069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9971456554150547009625425 7478592415612910257219069)
                    ·
                      refine ⟨2804472155854841346457151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7478592415612910257219069 2804472155854841346457151)
                      ·
                        rfl

theorem cell23_5461690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_5461690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461690 prefixEnd_5461690 := by exact prefixLift 5461690
  have htrace : WordTrace (prefixWord ++ tailWord_5461690) baseStart_5461690 baseEnd_5461690 := by
    simpa [prefixWord, tailWord_5461690, baseEnd_5461690] using wordTrace_append hprefix tailTrace_5461690
  have hstable : (prefixWord ++ tailWord_5461690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461690).length < 2 ^ (prefixWord ++ tailWord_5461690).sum := by decide
  have hdescent : baseEnd_5461690 < baseStart_5461690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461703 : List Nat := [1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_5461703 : Nat := 118140960795 + 5461703 * 2 ^ 59
def prefixEnd_5461703 : Nat := 4983230072969 + 3 ^ 40 * 5461703 * 2
def baseEnd_5461703 : Nat := 2804478831103349795594591

theorem tailTrace_5461703 : CollatzResearch.WordTrace tailWord_5461703 prefixEnd_5461703 2804478831103349795594591 := by
  unfold tailWord_5461703
  simp only [CollatzResearch.WordTrace]
  refine ⟨199204673732190290454733763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132803115821460193636489175 199204673732190290454733763)
  ·
    refine ⟨298807010598285435682100645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199204673732190290454733763 298807010598285435682100645)
    ·
      refine ⟨56026314487178519190393871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 298807010598285435682100645 56026314487178519190393871)
      ·
        refine ⟨84039471730767778785590807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56026314487178519190393871 84039471730767778785590807)
        ·
          refine ⟨126059207596151668178386211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84039471730767778785590807 126059207596151668178386211)
          ·
            refine ⟨189088811394227502267579317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126059207596151668178386211 189088811394227502267579317)
            ·
              refine ⟨17727076068208828337585561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 189088811394227502267579317 17727076068208828337585561)
              ·
                refine ⟨13295307051156621253189171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17727076068208828337585561 13295307051156621253189171)
                ·
                  refine ⟨19942960576734931879783757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13295307051156621253189171 19942960576734931879783757)
                  ·
                    refine ⟨7478610216275599454918909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19942960576734931879783757 7478610216275599454918909)
                    ·
                      refine ⟨2804478831103349795594591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7478610216275599454918909 2804478831103349795594591)
                      ·
                        rfl

theorem cell23_5461703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_5461703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461703 prefixEnd_5461703 := by exact prefixLift 5461703
  have htrace : WordTrace (prefixWord ++ tailWord_5461703) baseStart_5461703 baseEnd_5461703 := by
    simpa [prefixWord, tailWord_5461703, baseEnd_5461703] using wordTrace_append hprefix tailTrace_5461703
  have hstable : (prefixWord ++ tailWord_5461703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461703).length < 2 ^ (prefixWord ++ tailWord_5461703).sum := by decide
  have hdescent : baseEnd_5461703 < baseStart_5461703 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461721 : List Nat := [1, 2, 1, 2, 3, 5, 2, 2, 1, 2, 2]
def baseStart_5461721 : Nat := 118140960795 + 5461721 * 2 ^ 59
def prefixEnd_5461721 : Nat := 4983230072969 + 3 ^ 40 * 5461721 * 2
def baseEnd_5461721 : Nat := 2804488073755130725169509

theorem tailTrace_5461721 : CollatzResearch.WordTrace tailWord_5461721 prefixEnd_5461721 2804488073755130725169509 := by
  unfold tailWord_5461721
  simp only [CollatzResearch.WordTrace]
  refine ⟨199205330246125079528889017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132803553497416719685926011 199205330246125079528889017)
  ·
    refine ⟨149403997684593809646666763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199205330246125079528889017 149403997684593809646666763)
    ·
      refine ⟨224105996526890714470000145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149403997684593809646666763 224105996526890714470000145)
      ·
        refine ⟨168079497395168035852500109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224105996526890714470000145 168079497395168035852500109)
        ·
          refine ⟨63029811523188013444687541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168079497395168035852500109 63029811523188013444687541)
          ·
            refine ⟨5909044830298876260439457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 63029811523188013444687541 5909044830298876260439457)
            ·
              refine ⟨4431783622724157195329593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5909044830298876260439457 4431783622724157195329593)
              ·
                refine ⟨3323837717043117896497195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4431783622724157195329593 3323837717043117896497195)
                ·
                  refine ⟨4985756575564676844745793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3323837717043117896497195 4985756575564676844745793)
                  ·
                    refine ⟨3739317431673507633559345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4985756575564676844745793 3739317431673507633559345)
                    ·
                      refine ⟨2804488073755130725169509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3739317431673507633559345 2804488073755130725169509)
                      ·
                        rfl

theorem cell23_5461721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 2, 2, 1, 2, 2].length) (baseStart_5461721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461721 prefixEnd_5461721 := by exact prefixLift 5461721
  have htrace : WordTrace (prefixWord ++ tailWord_5461721) baseStart_5461721 baseEnd_5461721 := by
    simpa [prefixWord, tailWord_5461721, baseEnd_5461721] using wordTrace_append hprefix tailTrace_5461721
  have hstable : (prefixWord ++ tailWord_5461721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461721).length < 2 ^ (prefixWord ++ tailWord_5461721).sum := by decide
  have hdescent : baseEnd_5461721 < baseStart_5461721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461760 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 6, 2, 2]
def baseStart_5461760 : Nat := 118140960795 + 5461760 * 2 ^ 59
def prefixEnd_5461760 : Nat := 4983230072969 + 3 ^ 40 * 5461760 * 2
def baseEnd_5461760 : Nat := 2804508099500656072581829

theorem tailTrace_5461760 : CollatzResearch.WordTrace tailWord_5461760 prefixEnd_5461760 2804508099500656072581829 := by
  unfold tailWord_5461760
  simp only [CollatzResearch.WordTrace]
  refine ⟨99603376346491894594779367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132804501795322526126372489 99603376346491894594779367)
  ·
    refine ⟨149405064519737841892169051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99603376346491894594779367 149405064519737841892169051)
    ·
      refine ⟨224107596779606762838253577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149405064519737841892169051 224107596779606762838253577)
      ·
        refine ⟨168080697584705072128690183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224107596779606762838253577 168080697584705072128690183)
        ·
          refine ⟨252121046377057608193035275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168080697584705072128690183 252121046377057608193035275)
          ·
            refine ⟨378181569565586412289552913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252121046377057608193035275 378181569565586412289552913)
            ·
              refine ⟨283636177174189809217164685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378181569565586412289552913 283636177174189809217164685)
              ·
                refine ⟨106363566440321178456436757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 283636177174189809217164685 106363566440321178456436757)
                ·
                  refine ⟨4985792176890055240145473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106363566440321178456436757 4985792176890055240145473)
                  ·
                    refine ⟨3739344132667541430109105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4985792176890055240145473 3739344132667541430109105)
                    ·
                      refine ⟨2804508099500656072581829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3739344132667541430109105 2804508099500656072581829)
                      ·
                        rfl

theorem cell23_5461760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 6, 2, 2].length) (baseStart_5461760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461760 prefixEnd_5461760 := by exact prefixLift 5461760
  have htrace : WordTrace (prefixWord ++ tailWord_5461760) baseStart_5461760 baseEnd_5461760 := by
    simpa [prefixWord, tailWord_5461760, baseEnd_5461760] using wordTrace_append hprefix tailTrace_5461760
  have hstable : (prefixWord ++ tailWord_5461760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461760).length < 2 ^ (prefixWord ++ tailWord_5461760).sum := by decide
  have hdescent : baseEnd_5461760 < baseStart_5461760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461764 : List Nat := [2, 3, 2, 2, 1, 2, 4, 1, 1, 3, 2]
def baseStart_5461764 : Nat := 118140960795 + 5461764 * 2 ^ 59
def prefixEnd_5461764 : Nat := 4983230072969 + 3 ^ 40 * 5461764 * 2
def baseEnd_5461764 : Nat := 2804510153423274056931811

theorem tailTrace_5461764 : CollatzResearch.WordTrace tailWord_5461764 prefixEnd_5461764 2804510153423274056931811 := by
  unfold tailWord_5461764
  simp only [CollatzResearch.WordTrace]
  refine ⟨99603449292484648936352173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132804599056646198581802897 99603449292484648936352173)
  ·
    refine ⟨37351293484681743351132065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99603449292484648936352173 37351293484681743351132065)
    ·
      refine ⟨28013470113511307513349049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37351293484681743351132065 28013470113511307513349049)
      ·
        refine ⟨21010102585133480635011787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28013470113511307513349049 21010102585133480635011787)
        ·
          refine ⟨31515153877700220952517681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21010102585133480635011787 31515153877700220952517681)
          ·
            refine ⟨23636365408275165714388261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31515153877700220952517681 23636365408275165714388261)
            ·
              refine ⟨4431818514051593571447799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23636365408275165714388261 4431818514051593571447799)
              ·
                refine ⟨6647727771077390357171699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4431818514051593571447799 6647727771077390357171699)
                ·
                  refine ⟨9971591656616085535757549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6647727771077390357171699 9971591656616085535757549)
                  ·
                    refine ⟨3739346871231032075909081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9971591656616085535757549 3739346871231032075909081)
                    ·
                      refine ⟨2804510153423274056931811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3739346871231032075909081 2804510153423274056931811)
                      ·
                        rfl

theorem cell23_5461764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 1, 3, 2].length) (baseStart_5461764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461764 prefixEnd_5461764 := by exact prefixLift 5461764
  have htrace : WordTrace (prefixWord ++ tailWord_5461764) baseStart_5461764 baseEnd_5461764 := by
    simpa [prefixWord, tailWord_5461764, baseEnd_5461764] using wordTrace_append hprefix tailTrace_5461764
  have hstable : (prefixWord ++ tailWord_5461764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461764).length < 2 ^ (prefixWord ++ tailWord_5461764).sum := by decide
  have hdescent : baseEnd_5461764 < baseStart_5461764 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461783 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 7]
def baseStart_5461783 : Nat := 118140960795 + 5461783 * 2 ^ 59
def prefixEnd_5461783 : Nat := 4983230072969 + 3 ^ 40 * 5461783 * 2
def baseEnd_5461783 : Nat := 311613323283967720288247

theorem tailTrace_5461783 : CollatzResearch.WordTrace tailWord_5461783 prefixEnd_5461783 311613323283967720288247 := by
  unfold tailWord_5461783
  simp only [CollatzResearch.WordTrace]
  refine ⟨199207591571900464117646003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132805061047933642745097335 199207591571900464117646003)
  ·
    refine ⟨298811387357850696176469005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199207591571900464117646003 298811387357850696176469005)
    ·
      refine ⟨112054270259194011066175877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298811387357850696176469005 112054270259194011066175877)
      ·
        refine ⟨21010175673598877074907977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112054270259194011066175877 21010175673598877074907977)
        ·
          refine ⟨15757631755199157806180983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21010175673598877074907977 15757631755199157806180983)
          ·
            refine ⟨23636447632798736709271475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15757631755199157806180983 23636447632798736709271475)
            ·
              refine ⟨35454671449198105063907213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23636447632798736709271475 35454671449198105063907213)
              ·
                refine ⟨13295501793449289398965205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35454671449198105063907213 13295501793449289398965205)
                ·
                  refine ⟨311613323283967720288247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13295501793449289398965205 311613323283967720288247)
                  ·
                    rfl

theorem cell23_5461783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 7].length) (baseStart_5461783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461783 prefixEnd_5461783 := by exact prefixLift 5461783
  have htrace : WordTrace (prefixWord ++ tailWord_5461783) baseStart_5461783 baseEnd_5461783 := by
    simpa [prefixWord, tailWord_5461783, baseEnd_5461783] using wordTrace_append hprefix tailTrace_5461783
  have hstable : (prefixWord ++ tailWord_5461783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461783).length < 2 ^ (prefixWord ++ tailWord_5461783).sum := by decide
  have hdescent : baseEnd_5461783 < baseStart_5461783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461850 : List Nat := [3, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2]
def baseStart_5461850 : Nat := 118140960795 + 5461850 * 2 ^ 59
def prefixEnd_5461850 : Nat := 4983230072969 + 3 ^ 40 * 5461850 * 2
def baseEnd_5461850 : Nat := 2804554312759560720456415

theorem tailTrace_5461850 : CollatzResearch.WordTrace tailWord_5461850 prefixEnd_5461850 2804554312759560720456415 := by
  unfold tailWord_5461850
  simp only [CollatzResearch.WordTrace]
  refine ⟨49802508815664433640083751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132806690175105156373556669 49802508815664433640083751)
  ·
    refine ⟨74703763223496650460125627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49802508815664433640083751 74703763223496650460125627)
    ·
      refine ⟨112055644835244975690188441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74703763223496650460125627 112055644835244975690188441)
      ·
        refine ⟨84041733626433731767641331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112055644835244975690188441 84041733626433731767641331)
        ·
          refine ⟨126062600439650597651461997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84041733626433731767641331 126062600439650597651461997)
          ·
            refine ⟨47273475164868974119298249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126062600439650597651461997 47273475164868974119298249)
            ·
              refine ⟨35455106373651730589473687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47273475164868974119298249 35455106373651730589473687)
              ·
                refine ⟨53182659560477595884210531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35455106373651730589473687 53182659560477595884210531)
                ·
                  refine ⟨79773989340716393826315797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53182659560477595884210531 79773989340716393826315797)
                  ·
                    refine ⟨3739405750346080960608553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79773989340716393826315797 3739405750346080960608553)
                    ·
                      refine ⟨2804554312759560720456415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3739405750346080960608553 2804554312759560720456415)
                      ·
                        rfl

theorem cell23_5461850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2].length) (baseStart_5461850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461850 prefixEnd_5461850 := by exact prefixLift 5461850
  have htrace : WordTrace (prefixWord ++ tailWord_5461850) baseStart_5461850 baseEnd_5461850 := by
    simpa [prefixWord, tailWord_5461850, baseEnd_5461850] using wordTrace_append hprefix tailTrace_5461850
  have hstable : (prefixWord ++ tailWord_5461850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461850).length < 2 ^ (prefixWord ++ tailWord_5461850).sum := by decide
  have hdescent : baseEnd_5461850 < baseStart_5461850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461893 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_5461893 : Nat := 118140960795 + 5461893 * 2 ^ 59
def prefixEnd_5461893 : Nat := 4983230072969 + 3 ^ 40 * 5461893 * 2
def baseEnd_5461893 : Nat := 2804576392427704052218717

theorem tailTrace_5461893 : CollatzResearch.WordTrace tailWord_5461893 prefixEnd_5461893 2804576392427704052218717 := by
  unfold tailWord_5461893
  simp only [CollatzResearch.WordTrace]
  refine ⟨199211603601501952904150333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132807735734334635269433555 199211603601501952904150333)
  ·
    refine ⟨74704351350563232339056375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199211603601501952904150333 74704351350563232339056375)
    ·
      refine ⟨112056527025844848508584563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74704351350563232339056375 112056527025844848508584563)
      ·
        refine ⟨168084790538767272762876845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112056527025844848508584563 168084790538767272762876845)
        ·
          refine ⟨63031796452037727286078817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168084790538767272762876845 63031796452037727286078817)
          ·
            refine ⟨47273847339028295464559113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63031796452037727286078817 47273847339028295464559113)
            ·
              refine ⟨35455385504271221598419335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47273847339028295464559113 35455385504271221598419335)
              ·
                refine ⟨53183078256406832397629003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35455385504271221598419335 53183078256406832397629003)
                ·
                  refine ⟨79774617384610248596443505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53183078256406832397629003 79774617384610248596443505)
                  ·
                    refine ⟨59830963038457686447332629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79774617384610248596443505 59830963038457686447332629)
                    ·
                      refine ⟨2804576392427704052218717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59830963038457686447332629 2804576392427704052218717)
                      ·
                        rfl

theorem cell23_5461893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_5461893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461893 prefixEnd_5461893 := by exact prefixLift 5461893
  have htrace : WordTrace (prefixWord ++ tailWord_5461893) baseStart_5461893 baseEnd_5461893 := by
    simpa [prefixWord, tailWord_5461893, baseEnd_5461893] using wordTrace_append hprefix tailTrace_5461893
  have hstable : (prefixWord ++ tailWord_5461893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461893).length < 2 ^ (prefixWord ++ tailWord_5461893).sum := by decide
  have hdescent : baseEnd_5461893 < baseStart_5461893 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461917 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_5461917 : Nat := 118140960795 + 5461917 * 2 ^ 59
def prefixEnd_5461917 : Nat := 4983230072969 + 3 ^ 40 * 5461917 * 2
def baseEnd_5461917 : Nat := 2804588715963411958318607

theorem tailTrace_5461917 : CollatzResearch.WordTrace tailWord_5461917 prefixEnd_5461917 2804588715963411958318607 := by
  unfold tailWord_5461917
  simp only [CollatzResearch.WordTrace]
  refine ⟨199212478953415005003024005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132808319302276670002016003 199212478953415005003024005)
  ·
    refine ⟨37352339803765313438067001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199212478953415005003024005 37352339803765313438067001)
    ·
      refine ⟨28014254852823985078550251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37352339803765313438067001 28014254852823985078550251)
      ·
        refine ⟨42021382279235977617825377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28014254852823985078550251 42021382279235977617825377)
        ·
          refine ⟨31516036709426983213369033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42021382279235977617825377 31516036709426983213369033)
          ·
            refine ⟨23637027532070237410026775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31516036709426983213369033 23637027532070237410026775)
            ·
              refine ⟨35455541298105356115040163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23637027532070237410026775 35455541298105356115040163)
              ·
                refine ⟨53183311947158034172560245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35455541298105356115040163 53183311947158034172560245)
                ·
                  refine ⟨4985935495046065703677523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53183311947158034172560245 4985935495046065703677523)
                  ·
                    refine ⟨7478903242569098555516285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4985935495046065703677523 7478903242569098555516285)
                    ·
                      refine ⟨2804588715963411958318607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7478903242569098555516285 2804588715963411958318607)
                      ·
                        rfl

theorem cell23_5461917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_5461917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461917 prefixEnd_5461917 := by exact prefixLift 5461917
  have htrace : WordTrace (prefixWord ++ tailWord_5461917) baseStart_5461917 baseEnd_5461917 := by
    simpa [prefixWord, tailWord_5461917, baseEnd_5461917] using wordTrace_append hprefix tailTrace_5461917
  have hstable : (prefixWord ++ tailWord_5461917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461917).length < 2 ^ (prefixWord ++ tailWord_5461917).sum := by decide
  have hdescent : baseEnd_5461917 < baseStart_5461917 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461918 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 2, 1, 4]
def baseStart_5461918 : Nat := 118140960795 + 5461918 * 2 ^ 59
def prefixEnd_5461918 : Nat := 4983230072969 + 3 ^ 40 * 5461918 * 2
def baseEnd_5461918 : Nat := 2804589229444066454406103

theorem tailTrace_5461918 : CollatzResearch.WordTrace tailWord_5461918 prefixEnd_5461918 2804589229444066454406103 := by
  unfold tailWord_5461918
  simp only [CollatzResearch.WordTrace]
  refine ⟨24901564428301422771726301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132808343617607588115873605 24901564428301422771726301)
  ·
    refine ⟨9338086660613033539397363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24901564428301422771726301 9338086660613033539397363)
    ·
      refine ⟨14007129990919550309096045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9338086660613033539397363 14007129990919550309096045)
      ·
        refine ⟨5252673746594831365911017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14007129990919550309096045 5252673746594831365911017)
        ·
          refine ⟨3939505309946123524433263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5252673746594831365911017 3939505309946123524433263)
          ·
            refine ⟨5909257964919185286649895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3939505309946123524433263 5909257964919185286649895)
            ·
              refine ⟨8863886947378777929974843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5909257964919185286649895 8863886947378777929974843)
              ·
                refine ⟨13295830421068166894962265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8863886947378777929974843 13295830421068166894962265)
                ·
                  refine ⟨9971872815801125171221699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13295830421068166894962265 9971872815801125171221699)
                  ·
                    refine ⟨14957809223701687756832549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9971872815801125171221699 14957809223701687756832549)
                    ·
                      refine ⟨2804589229444066454406103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14957809223701687756832549 2804589229444066454406103)
                      ·
                        rfl

theorem cell23_5461918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 2, 1, 4].length) (baseStart_5461918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461918 prefixEnd_5461918 := by exact prefixLift 5461918
  have htrace : WordTrace (prefixWord ++ tailWord_5461918) baseStart_5461918 baseEnd_5461918 := by
    simpa [prefixWord, tailWord_5461918, baseEnd_5461918] using wordTrace_append hprefix tailTrace_5461918
  have hstable : (prefixWord ++ tailWord_5461918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461918).length < 2 ^ (prefixWord ++ tailWord_5461918).sum := by decide
  have hdescent : baseEnd_5461918 < baseStart_5461918 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461920 : List Nat := [2, 1, 1, 4, 1, 1, 1, 6, 1, 5]
def baseStart_5461920 : Nat := 118140960795 + 5461920 * 2 ^ 59
def prefixEnd_5461920 : Nat := 4983230072969 + 3 ^ 40 * 5461920 * 2
def baseEnd_5461920 : Nat := 934863418801791815527031

theorem tailTrace_5461920 : CollatzResearch.WordTrace tailWord_5461920 prefixEnd_5461920 934863418801791815527031 := by
  unfold tailWord_5461920
  simp only [CollatzResearch.WordTrace]
  refine ⟨99606294186202068257691607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132808392248269424343588809 99606294186202068257691607)
  ·
    refine ⟨149409441279303102386537411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99606294186202068257691607 149409441279303102386537411)
    ·
      refine ⟨224114161918954653579806117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149409441279303102386537411 224114161918954653579806117)
      ·
        refine ⟨42021405359803997546213647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224114161918954653579806117 42021405359803997546213647)
        ·
          refine ⟨63032108039705996319320471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42021405359803997546213647 63032108039705996319320471)
          ·
            refine ⟨94548162059558994478980707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63032108039705996319320471 94548162059558994478980707)
            ·
              refine ⟨141822243089338491718471061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94548162059558994478980707 141822243089338491718471061)
              ·
                refine ⟨6647917644812741799303331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141822243089338491718471061 6647917644812741799303331)
                ·
                  refine ⟨9971876467219112698954997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6647917644812741799303331 9971876467219112698954997)
                  ·
                    refine ⟨934863418801791815527031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9971876467219112698954997 934863418801791815527031)
                    ·
                      rfl

theorem cell23_5461920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 6, 1, 5].length) (baseStart_5461920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461920 prefixEnd_5461920 := by exact prefixLift 5461920
  have htrace : WordTrace (prefixWord ++ tailWord_5461920) baseStart_5461920 baseEnd_5461920 := by
    simpa [prefixWord, tailWord_5461920, baseEnd_5461920] using wordTrace_append hprefix tailTrace_5461920
  have hstable : (prefixWord ++ tailWord_5461920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461920).length < 2 ^ (prefixWord ++ tailWord_5461920).sum := by decide
  have hdescent : baseEnd_5461920 < baseStart_5461920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461921 : List Nat := [1, 2, 3, 4, 3, 1, 1, 1, 2, 2, 3]
def baseStart_5461921 : Nat := 118140960795 + 5461921 * 2 ^ 59
def prefixEnd_5461921 : Nat := 4983230072969 + 3 ^ 40 * 5461921 * 2
def baseEnd_5461921 : Nat := 2804590769886029942668589

theorem tailTrace_5461921 : CollatzResearch.WordTrace tailWord_5461921 prefixEnd_5461921 2804590769886029942668589 := by
  unfold tailWord_5461921
  simp only [CollatzResearch.WordTrace]
  refine ⟨199212624845400513686169617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132808416563600342457446411 199212624845400513686169617)
  ·
    refine ⟨149409468634050385264627213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199212624845400513686169617 149409468634050385264627213)
    ·
      refine ⟨56028550737768894474235205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149409468634050385264627213 56028550737768894474235205)
      ·
        refine ⟨10505353263331667713919101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56028550737768894474235205 10505353263331667713919101)
        ·
          refine ⟨3939507473749375392719663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10505353263331667713919101 3939507473749375392719663)
          ·
            refine ⟨5909261210624063089079495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3939507473749375392719663 5909261210624063089079495)
            ·
              refine ⟨8863891815936094633619243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5909261210624063089079495 8863891815936094633619243)
              ·
                refine ⟨13295837723904141950428865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8863891815936094633619243 13295837723904141950428865)
                ·
                  refine ⟨9971878292928106462821649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13295837723904141950428865 9971878292928106462821649)
                  ·
                    refine ⟨7478908719696079847116237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9971878292928106462821649 7478908719696079847116237)
                    ·
                      refine ⟨2804590769886029942668589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7478908719696079847116237 2804590769886029942668589)
                      ·
                        rfl

theorem cell23_5461921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 1, 1, 2, 2, 3].length) (baseStart_5461921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461921 prefixEnd_5461921 := by exact prefixLift 5461921
  have htrace : WordTrace (prefixWord ++ tailWord_5461921) baseStart_5461921 baseEnd_5461921 := by
    simpa [prefixWord, tailWord_5461921, baseEnd_5461921] using wordTrace_append hprefix tailTrace_5461921
  have hstable : (prefixWord ++ tailWord_5461921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461921).length < 2 ^ (prefixWord ++ tailWord_5461921).sum := by decide
  have hdescent : baseEnd_5461921 < baseStart_5461921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461928 : List Nat := [2, 1, 6, 2, 1, 1, 2, 3, 1, 4]
def baseStart_5461928 : Nat := 118140960795 + 5461928 * 2 ^ 59
def prefixEnd_5461928 : Nat := 4983230072969 + 3 ^ 40 * 5461928 * 2
def baseEnd_5461928 : Nat := 934864788083537138427019

theorem tailTrace_5461928 : CollatzResearch.WordTrace tailWord_5461928 prefixEnd_5461928 934864788083537138427019 := by
  unfold tailWord_5461928
  simp only [CollatzResearch.WordTrace]
  refine ⟨99606440078187576940837219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132808586770916769254449625 99606440078187576940837219)
  ·
    refine ⟨149409660117281365411255829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99606440078187576940837219 149409660117281365411255829)
    ·
      refine ⟨7003577817997564003652617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 149409660117281365411255829 7003577817997564003652617)
      ·
        refine ⟨5252683363498173002739463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7003577817997564003652617 5252683363498173002739463)
        ·
          refine ⟨7879025045247259504109195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5252683363498173002739463 7879025045247259504109195)
          ·
            refine ⟨11818537567870889256163793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7879025045247259504109195 11818537567870889256163793)
            ·
              refine ⟨8863903175903166942122845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11818537567870889256163793 8863903175903166942122845)
              ·
                refine ⟨3323963690963687603296067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8863903175903166942122845 3323963690963687603296067)
                ·
                  refine ⟨4985945536445531404944101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3323963690963687603296067 4985945536445531404944101)
                  ·
                    refine ⟨934864788083537138427019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4985945536445531404944101 934864788083537138427019)
                    ·
                      rfl

theorem cell23_5461928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_5461928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461928 prefixEnd_5461928 := by exact prefixLift 5461928
  have htrace : WordTrace (prefixWord ++ tailWord_5461928) baseStart_5461928 baseEnd_5461928 := by
    simpa [prefixWord, tailWord_5461928, baseEnd_5461928] using wordTrace_append hprefix tailTrace_5461928
  have hstable : (prefixWord ++ tailWord_5461928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461928).length < 2 ^ (prefixWord ++ tailWord_5461928).sum := by decide
  have hdescent : baseEnd_5461928 < baseStart_5461928 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461937 : List Nat := [1, 2, 2, 4, 2, 2, 1, 3, 1, 5]
def baseStart_5461937 : Nat := 118140960795 + 5461937 * 2 ^ 59
def prefixEnd_5461937 : Nat := 4983230072969 + 3 ^ 40 * 5461937 * 2
def baseEnd_5461937 : Nat := 934866328525500626689505

theorem tailTrace_5461937 : CollatzResearch.WordTrace tailWord_5461937 prefixEnd_5461937 934866328525500626689505 := by
  unfold tailWord_5461937
  simp only [CollatzResearch.WordTrace]
  refine ⟨199213208413342548418752065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132808805608895032279168043 199213208413342548418752065)
  ·
    refine ⟨149409906310006911314064049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199213208413342548418752065 149409906310006911314064049)
    ·
      refine ⟨112057429732505183485548037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149409906310006911314064049 112057429732505183485548037)
      ·
        refine ⟨21010768074844721903540257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112057429732505183485548037 21010768074844721903540257)
        ·
          refine ⟨15758076056133541427655193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21010768074844721903540257 15758076056133541427655193)
          ·
            refine ⟨11818557042100156070741395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15758076056133541427655193 11818557042100156070741395)
            ·
              refine ⟨17727835563150234106112093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11818557042100156070741395 17727835563150234106112093)
              ·
                refine ⟨6647938336181337789792035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17727835563150234106112093 6647938336181337789792035)
                ·
                  refine ⟨9971907504272006684688053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6647938336181337789792035 9971907504272006684688053)
                  ·
                    refine ⟨934866328525500626689505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9971907504272006684688053 934866328525500626689505)
                    ·
                      rfl

theorem cell23_5461937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_5461937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461937 prefixEnd_5461937 := by exact prefixLift 5461937
  have htrace : WordTrace (prefixWord ++ tailWord_5461937) baseStart_5461937 baseEnd_5461937 := by
    simpa [prefixWord, tailWord_5461937, baseEnd_5461937] using wordTrace_append hprefix tailTrace_5461937
  have hstable : (prefixWord ++ tailWord_5461937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461937).length < 2 ^ (prefixWord ++ tailWord_5461937).sum := by decide
  have hdescent : baseEnd_5461937 < baseStart_5461937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461960 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 3, 1, 5]
def baseStart_5461960 : Nat := 118140960795 + 5461960 * 2 ^ 59
def prefixEnd_5461960 : Nat := 4983230072969 + 3 ^ 40 * 5461960 * 2
def baseEnd_5461960 : Nat := 2804610795631555290080909

theorem tailTrace_5461960 : CollatzResearch.WordTrace tailWord_5461960 prefixEnd_5461960 2804610795631555290080909 := by
  unfold tailWord_5461960
  simp only [CollatzResearch.WordTrace]
  refine ⟨99607023646129611673419667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132809364861506148897892889 99607023646129611673419667)
  ·
    refine ⟨149410535469194417510129501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99607023646129611673419667 149410535469194417510129501)
    ·
      refine ⟨56028950800947906566298563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149410535469194417510129501 56028950800947906566298563)
      ·
        refine ⟨84043426201421859849447845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56028950800947906566298563 84043426201421859849447845)
        ·
          refine ⟨15758142412766598721771471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84043426201421859849447845 15758142412766598721771471)
          ·
            refine ⟨23637213619149898082657207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15758142412766598721771471 23637213619149898082657207)
            ·
              refine ⟨35455820428724847123985811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23637213619149898082657207 35455820428724847123985811)
              ·
                refine ⟨53183730643087270685978717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35455820428724847123985811 53183730643087270685978717)
                ·
                  refine ⟨19943898991157726507242019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53183730643087270685978717 19943898991157726507242019)
                  ·
                    refine ⟨29915848486736589760863029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19943898991157726507242019 29915848486736589760863029)
                    ·
                      refine ⟨2804610795631555290080909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29915848486736589760863029 2804610795631555290080909)
                      ·
                        rfl

theorem cell23_5461960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_5461960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461960 prefixEnd_5461960 := by exact prefixLift 5461960
  have htrace : WordTrace (prefixWord ++ tailWord_5461960) baseStart_5461960 baseEnd_5461960 := by
    simpa [prefixWord, tailWord_5461960, baseEnd_5461960] using wordTrace_append hprefix tailTrace_5461960
  have hstable : (prefixWord ++ tailWord_5461960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461960).length < 2 ^ (prefixWord ++ tailWord_5461960).sum := by decide
  have hdescent : baseEnd_5461960 < baseStart_5461960 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5461963 : List Nat := [1, 1, 1, 1, 3, 4, 2, 10]
def baseStart_5461963 : Nat := 118140960795 + 5461963 * 2 ^ 59
def prefixEnd_5461963 : Nat := 4983230072969 + 3 ^ 40 * 5461963 * 2
def baseEnd_5461963 : Nat := 103874530965685880679385

theorem tailTrace_5461963 : CollatzResearch.WordTrace tailWord_5461963 prefixEnd_5461963 103874530965685880679385 := by
  unfold tailWord_5461963
  simp only [CollatzResearch.WordTrace]
  refine ⟨199214156711248354859198543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132809437807498903239465695 199214156711248354859198543)
  ·
    refine ⟨298821235066872532288797815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199214156711248354859198543 298821235066872532288797815)
    ·
      refine ⟨448231852600308798433196723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298821235066872532288797815 448231852600308798433196723)
      ·
        refine ⟨672347778900463197649795085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448231852600308798433196723 672347778900463197649795085)
        ·
          refine ⟨252130417087673699118673157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 672347778900463197649795085 252130417087673699118673157)
          ·
            refine ⟨47274453203938818584751217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 252130417087673699118673157 47274453203938818584751217)
            ·
              refine ⟨35455839902954113938563413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47274453203938818584751217 35455839902954113938563413)
              ·
                refine ⟨103874530965685880679385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35455839902954113938563413 103874530965685880679385)
                ·
                  rfl

theorem cell23_5461963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 10].length) (baseStart_5461963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5461963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5461963 prefixEnd_5461963 := by exact prefixLift 5461963
  have htrace : WordTrace (prefixWord ++ tailWord_5461963) baseStart_5461963 baseEnd_5461963 := by
    simpa [prefixWord, tailWord_5461963, baseEnd_5461963] using wordTrace_append hprefix tailTrace_5461963
  have hstable : (prefixWord ++ tailWord_5461963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5461963).length < 2 ^ (prefixWord ++ tailWord_5461963).sum := by decide
  have hdescent : baseEnd_5461963 < baseStart_5461963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5461963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462022 : List Nat := [6, 2, 1, 2, 2, 1, 1, 2, 1, 5]
def baseStart_5462022 : Nat := 118140960795 + 5462022 * 2 ^ 59
def prefixEnd_5462022 : Nat := 4983230072969 + 3 ^ 40 * 5462022 * 2
def baseEnd_5462022 : Nat := 934880877144044682501875

theorem tailTrace_5462022 : CollatzResearch.WordTrace tailWord_5462022 prefixEnd_5462022 934880877144044682501875 := by
  unfold tailWord_5462022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6225509644313581497987385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132810872412023071957064213 6225509644313581497987385)
  ·
    refine ⟨4669132233235186123490539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6225509644313581497987385 4669132233235186123490539)
    ·
      refine ⟨7003698349852779185235809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4669132233235186123490539 7003698349852779185235809)
      ·
        refine ⟨5252773762389584388926857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7003698349852779185235809 5252773762389584388926857)
        ·
          refine ⟨3939580321792188291695143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5252773762389584388926857 3939580321792188291695143)
          ·
            refine ⟨5909370482688282437542715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3939580321792188291695143 5909370482688282437542715)
            ·
              refine ⟨8864055724032423656314073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5909370482688282437542715 8864055724032423656314073)
              ·
                refine ⟨6648041793024317742235555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8864055724032423656314073 6648041793024317742235555)
                ·
                  refine ⟨9972062689536476613353333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6648041793024317742235555 9972062689536476613353333)
                  ·
                    refine ⟨934880877144044682501875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9972062689536476613353333 934880877144044682501875)
                    ·
                      rfl

theorem cell23_5462022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_5462022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462022 prefixEnd_5462022 := by exact prefixLift 5462022
  have htrace : WordTrace (prefixWord ++ tailWord_5462022) baseStart_5462022 baseEnd_5462022 := by
    simpa [prefixWord, tailWord_5462022, baseEnd_5462022] using wordTrace_append hprefix tailTrace_5462022
  have hstable : (prefixWord ++ tailWord_5462022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462022).length < 2 ^ (prefixWord ++ tailWord_5462022).sum := by decide
  have hdescent : baseEnd_5462022 < baseStart_5462022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462024 : List Nat := [2, 1, 3, 2, 1, 2, 3, 3, 2, 1, 3]
def baseStart_5462024 : Nat := 118140960795 + 5462024 * 2 ^ 59
def prefixEnd_5462024 : Nat := 4983230072969 + 3 ^ 40 * 5462024 * 2
def baseEnd_5462024 : Nat := 2804643658393443039680615

theorem tailTrace_5462024 : CollatzResearch.WordTrace tailWord_5462024 prefixEnd_5462024 2804643658393443039680615 := by
  unfold tailWord_5462024
  simp only [CollatzResearch.WordTrace]
  refine ⟨99608190782013681138584563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132810921042684908184779417 99608190782013681138584563)
  ·
    refine ⟨149412286173020521707876845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99608190782013681138584563 149412286173020521707876845)
    ·
      refine ⟨56029607314882695640453817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149412286173020521707876845 56029607314882695640453817)
      ·
        refine ⟨42022205486162021730340363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56029607314882695640453817 42022205486162021730340363)
        ·
          refine ⟨63033308229243032595510545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42022205486162021730340363 63033308229243032595510545)
          ·
            refine ⟨47274981171932274446632909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63033308229243032595510545 47274981171932274446632909)
            ·
              refine ⟨17728117939474602917487341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47274981171932274446632909 17728117939474602917487341)
              ·
                refine ⟨6648044227302976094057753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17728117939474602917487341 6648044227302976094057753)
                ·
                  refine ⟨4986033170477232070543315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6648044227302976094057753 4986033170477232070543315)
                  ·
                    refine ⟨7479049755715848105814973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4986033170477232070543315 7479049755715848105814973)
                    ·
                      refine ⟨2804643658393443039680615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7479049755715848105814973 2804643658393443039680615)
                      ·
                        rfl

theorem cell23_5462024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 2, 1, 3].length) (baseStart_5462024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462024 prefixEnd_5462024 := by exact prefixLift 5462024
  have htrace : WordTrace (prefixWord ++ tailWord_5462024) baseStart_5462024 baseEnd_5462024 := by
    simpa [prefixWord, tailWord_5462024, baseEnd_5462024] using wordTrace_append hprefix tailTrace_5462024
  have hstable : (prefixWord ++ tailWord_5462024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462024).length < 2 ^ (prefixWord ++ tailWord_5462024).sum := by decide
  have hdescent : baseEnd_5462024 < baseStart_5462024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462051 : List Nat := [1, 1, 1, 4, 3, 1, 5, 1, 1, 3, 2]
def baseStart_5462051 : Nat := 118140960795 + 5462051 * 2 ^ 59
def prefixEnd_5462051 : Nat := 4983230072969 + 3 ^ 40 * 5462051 * 2
def baseEnd_5462051 : Nat := 2804657522371114434042991

theorem tailTrace_5462051 : CollatzResearch.WordTrace tailWord_5462051 prefixEnd_5462051 2804657522371114434042991 := by
  unfold tailWord_5462051
  simp only [CollatzResearch.WordTrace]
  refine ⟨199217366334929545888402007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132811577556619697258934671 199217366334929545888402007)
  ·
    refine ⟨298826049502394318832603011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199217366334929545888402007 298826049502394318832603011)
    ·
      refine ⟨448239074253591478248904517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298826049502394318832603011 448239074253591478248904517)
      ·
        refine ⟨84044826422548402171669597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 448239074253591478248904517 84044826422548402171669597)
        ·
          refine ⟨31516809908455650814376099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84044826422548402171669597 31516809908455650814376099)
          ·
            refine ⟨47275214862683476221564149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31516809908455650814376099 47275214862683476221564149)
            ·
              refine ⟨4432051393376575895771639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 47275214862683476221564149 4432051393376575895771639)
              ·
                refine ⟨6648077090064863843657459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4432051393376575895771639 6648077090064863843657459)
                ·
                  refine ⟨9972115635097295765486189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6648077090064863843657459 9972115635097295765486189)
                  ·
                    refine ⟨3739543363161485912057321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9972115635097295765486189 3739543363161485912057321)
                    ·
                      refine ⟨2804657522371114434042991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3739543363161485912057321 2804657522371114434042991)
                      ·
                        rfl

theorem cell23_5462051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 1, 3, 2].length) (baseStart_5462051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462051 prefixEnd_5462051 := by exact prefixLift 5462051
  have htrace : WordTrace (prefixWord ++ tailWord_5462051) baseStart_5462051 baseEnd_5462051 := by
    simpa [prefixWord, tailWord_5462051, baseEnd_5462051] using wordTrace_append hprefix tailTrace_5462051
  have hstable : (prefixWord ++ tailWord_5462051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462051).length < 2 ^ (prefixWord ++ tailWord_5462051).sum := by decide
  have hdescent : baseEnd_5462051 < baseStart_5462051 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462077 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_5462077 : Nat := 118140960795 + 5462077 * 2 ^ 59
def prefixEnd_5462077 : Nat := 4983230072969 + 3 ^ 40 * 5462077 * 2
def baseEnd_5462077 : Nat := 2804670872868131332317871

theorem tailTrace_5462077 : CollatzResearch.WordTrace tailWord_5462077 prefixEnd_5462077 2804670872868131332317871 := by
  unfold tailWord_5462077
  simp only [CollatzResearch.WordTrace]
  refine ⟨199218314632835352328848485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132812209755223568219232323 199218314632835352328848485)
  ·
    refine ⟨37353433993656628561659091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199218314632835352328848485 37353433993656628561659091)
    ·
      refine ⟨56030150990484942842488637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37353433993656628561659091 56030150990484942842488637)
      ·
        refine ⟨21011306621431853565933239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56030150990484942842488637 21011306621431853565933239)
        ·
          refine ⟨31516959932147780348899859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21011306621431853565933239 31516959932147780348899859)
          ·
            refine ⟨47275439898221670523349789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31516959932147780348899859 47275439898221670523349789)
            ·
              refine ⟨17728289961833126446256171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47275439898221670523349789 17728289961833126446256171)
              ·
                refine ⟨26592434942749689669384257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17728289961833126446256171 26592434942749689669384257)
                ·
                  refine ⟨19944326207062267252038193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26592434942749689669384257 19944326207062267252038193)
                  ·
                    refine ⟨14958244655296700439028645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19944326207062267252038193 14958244655296700439028645)
                    ·
                      refine ⟨2804670872868131332317871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14958244655296700439028645 2804670872868131332317871)
                      ·
                        rfl

theorem cell23_5462077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_5462077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462077 prefixEnd_5462077 := by exact prefixLift 5462077
  have htrace : WordTrace (prefixWord ++ tailWord_5462077) baseStart_5462077 baseEnd_5462077 := by
    simpa [prefixWord, tailWord_5462077, baseEnd_5462077] using wordTrace_append hprefix tailTrace_5462077
  have hstable : (prefixWord ++ tailWord_5462077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462077).length < 2 ^ (prefixWord ++ tailWord_5462077).sum := by decide
  have hdescent : baseEnd_5462077 < baseStart_5462077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462081 : List Nat := [1, 2, 5, 1, 2, 2, 2, 1, 1, 4, 2]
def baseStart_5462081 : Nat := 118140960795 + 5462081 * 2 ^ 59
def prefixEnd_5462081 : Nat := 4983230072969 + 3 ^ 40 * 5462081 * 2
def baseEnd_5462081 : Nat := 2804672926790749316667853

theorem tailTrace_5462081 : CollatzResearch.WordTrace tailWord_5462081 prefixEnd_5462081 2804672926790749316667853 := by
  unfold tailWord_5462081
  simp only [CollatzResearch.WordTrace]
  refine ⟨199218460524820861011994097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132812307016547240674662731 199218460524820861011994097)
  ·
    refine ⟨149413845393615645758995573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199218460524820861011994097 149413845393615645758995573)
    ·
      refine ⟨14007548005651466789905835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149413845393615645758995573 14007548005651466789905835)
      ·
        refine ⟨21011322008477200184858753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14007548005651466789905835 21011322008477200184858753)
        ·
          refine ⟨15758491506357900138644065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21011322008477200184858753 15758491506357900138644065)
          ·
            refine ⟨11818868629768425103983049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15758491506357900138644065 11818868629768425103983049)
            ·
              refine ⟨8864151472326318827987287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11818868629768425103983049 8864151472326318827987287)
              ·
                refine ⟨13296227208489478241980931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8864151472326318827987287 13296227208489478241980931)
                ·
                  refine ⟨19944340812734217362971397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13296227208489478241980931 19944340812734217362971397)
                  ·
                    refine ⟨3739563902387665755557137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19944340812734217362971397 3739563902387665755557137)
                    ·
                      refine ⟨2804672926790749316667853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3739563902387665755557137 2804672926790749316667853)
                      ·
                        rfl

theorem cell23_5462081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 4, 2].length) (baseStart_5462081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462081 prefixEnd_5462081 := by exact prefixLift 5462081
  have htrace : WordTrace (prefixWord ++ tailWord_5462081) baseStart_5462081 baseEnd_5462081 := by
    simpa [prefixWord, tailWord_5462081, baseEnd_5462081] using wordTrace_append hprefix tailTrace_5462081
  have hstable : (prefixWord ++ tailWord_5462081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462081).length < 2 ^ (prefixWord ++ tailWord_5462081).sum := by decide
  have hdescent : baseEnd_5462081 < baseStart_5462081 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462102 : List Nat := [5, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2]
def baseStart_5462102 : Nat := 118140960795 + 5462102 * 2 ^ 59
def prefixEnd_5462102 : Nat := 4983230072969 + 3 ^ 40 * 5462102 * 2
def baseEnd_5462102 : Nat := 2804683709884493734505257

theorem tailTrace_5462102 : CollatzResearch.WordTrace tailWord_5462102 prefixEnd_5462102 2804683709884493734505257 := by
  unfold tailWord_5462102
  simp only [CollatzResearch.WordTrace]
  refine ⟨12451201653609048849906785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132812817638496521065672373 12451201653609048849906785)
  ·
    refine ⟨9338401240206786637430089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12451201653609048849906785 9338401240206786637430089)
    ·
      refine ⟨7003800930155089978072567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9338401240206786637430089 7003800930155089978072567)
      ·
        refine ⟨10505701395232634967108851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7003800930155089978072567 10505701395232634967108851)
        ·
          refine ⟨15758552092848952450663277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10505701395232634967108851 15758552092848952450663277)
          ·
            refine ⟨5909457034818357168998729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15758552092848952450663277 5909457034818357168998729)
            ·
              refine ⟨4432092776113767876749047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5909457034818357168998729 4432092776113767876749047)
              ·
                refine ⟨6648139164170651815123571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4432092776113767876749047 6648139164170651815123571)
                ·
                  refine ⟨9972208746255977722685357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6648139164170651815123571 9972208746255977722685357)
                  ·
                    refine ⟨3739578279845991646007009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9972208746255977722685357 3739578279845991646007009)
                    ·
                      refine ⟨2804683709884493734505257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3739578279845991646007009 2804683709884493734505257)
                      ·
                        rfl

theorem cell23_5462102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_5462102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462102 prefixEnd_5462102 := by exact prefixLift 5462102
  have htrace : WordTrace (prefixWord ++ tailWord_5462102) baseStart_5462102 baseEnd_5462102 := by
    simpa [prefixWord, tailWord_5462102, baseEnd_5462102] using wordTrace_append hprefix tailTrace_5462102
  have hstable : (prefixWord ++ tailWord_5462102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462102).length < 2 ^ (prefixWord ++ tailWord_5462102).sum := by decide
  have hdescent : baseEnd_5462102 < baseStart_5462102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462104 : List Nat := [2, 1, 2, 2, 1, 5, 2, 3, 5]
def baseStart_5462104 : Nat := 118140960795 + 5462104 * 2 ^ 59
def prefixEnd_5462104 : Nat := 4983230072969 + 3 ^ 40 * 5462104 * 2
def baseEnd_5462104 : Nat := 311631637427311414075583

theorem tailTrace_5462104 : CollatzResearch.WordTrace tailWord_5462104 prefixEnd_5462104 311631637427311414075583 := by
  unfold tailWord_5462104
  simp only [CollatzResearch.WordTrace]
  refine ⟨99609649701868767970040683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132812866269158357293387577 99609649701868767970040683)
  ·
    refine ⟨149414474552803151955061025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99609649701868767970040683 149414474552803151955061025)
    ·
      refine ⟨112060855914602363966295769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149414474552803151955061025 112060855914602363966295769)
      ·
        refine ⟨84045641935951772974721827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112060855914602363966295769 84045641935951772974721827)
        ·
          refine ⟨126068462903927659462082741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84045641935951772974721827 126068462903927659462082741)
          ·
            refine ⟨11818918397243218074570257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126068462903927659462082741 11818918397243218074570257)
            ·
              refine ⟨8864188797932413555927693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11818918397243218074570257 8864188797932413555927693)
              ·
                refine ⟨3324070799224655083472885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8864188797932413555927693 3324070799224655083472885)
                ·
                  refine ⟨311631637427311414075583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3324070799224655083472885 311631637427311414075583)
                  ·
                    rfl

theorem cell23_5462104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 3, 5].length) (baseStart_5462104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462104 prefixEnd_5462104 := by exact prefixLift 5462104
  have htrace : WordTrace (prefixWord ++ tailWord_5462104) baseStart_5462104 baseEnd_5462104 := by
    simpa [prefixWord, tailWord_5462104, baseEnd_5462104] using wordTrace_append hprefix tailTrace_5462104
  have hstable : (prefixWord ++ tailWord_5462104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462104).length < 2 ^ (prefixWord ++ tailWord_5462104).sum := by decide
  have hdescent : baseEnd_5462104 < baseStart_5462104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462137 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 1, 3, 4]
def baseStart_5462137 : Nat := 118140960795 + 5462137 * 2 ^ 59
def prefixEnd_5462137 : Nat := 4983230072969 + 3 ^ 40 * 5462137 * 2
def baseEnd_5462137 : Nat := 2804701681707401097567595

theorem tailTrace_5462137 : CollatzResearch.WordTrace tailWord_5462137 prefixEnd_5462137 2804701681707401097567595 := by
  unfold tailWord_5462137
  simp only [CollatzResearch.WordTrace]
  refine ⟨199220503012617982576032665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132813668675078655050688443 199220503012617982576032665)
  ·
    refine ⟨149415377259463486932024499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199220503012617982576032665 149415377259463486932024499)
    ·
      refine ⟨224123065889195230398036749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149415377259463486932024499 224123065889195230398036749)
      ·
        refine ⟨84046149708448211399263781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224123065889195230398036749 84046149708448211399263781)
        ·
          refine ⟨15758653070334039637361959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84046149708448211399263781 15758653070334039637361959)
          ·
            refine ⟨23637979605501059456042939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15758653070334039637361959 23637979605501059456042939)
            ·
              refine ⟨35456969408251589184064409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23637979605501059456042939 35456969408251589184064409)
              ·
                refine ⟨26592727056188691888048307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35456969408251589184064409 26592727056188691888048307)
                ·
                  refine ⟨39889090584283037832072461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26592727056188691888048307 39889090584283037832072461)
                  ·
                    refine ⟨14958408969106139187027173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39889090584283037832072461 14958408969106139187027173)
                    ·
                      refine ⟨2804701681707401097567595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14958408969106139187027173 2804701681707401097567595)
                      ·
                        rfl

theorem cell23_5462137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_5462137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462137 prefixEnd_5462137 := by exact prefixLift 5462137
  have htrace : WordTrace (prefixWord ++ tailWord_5462137) baseStart_5462137 baseEnd_5462137 := by
    simpa [prefixWord, tailWord_5462137, baseEnd_5462137] using wordTrace_append hprefix tailTrace_5462137
  have hstable : (prefixWord ++ tailWord_5462137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462137).length < 2 ^ (prefixWord ++ tailWord_5462137).sum := by decide
  have hdescent : baseEnd_5462137 < baseStart_5462137 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462160 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 10]
def baseStart_5462160 : Nat := 118140960795 + 5462160 * 2 ^ 59
def prefixEnd_5462160 : Nat := 4983230072969 + 3 ^ 40 * 5462160 * 2
def baseEnd_5462160 : Nat := 311634832418050500842221

theorem tailTrace_5462160 : CollatzResearch.WordTrace tailWord_5462160 prefixEnd_5462160 311634832418050500842221 := by
  unfold tailWord_5462160
  simp only [CollatzResearch.WordTrace]
  refine ⟨99610670945767328752059967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132814227927689771669413289 99610670945767328752059967)
  ·
    refine ⟨149416006418650993128089951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99610670945767328752059967 149416006418650993128089951)
    ·
      refine ⟨224124009627976489692134927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149416006418650993128089951 224124009627976489692134927)
      ·
        refine ⟨336186014441964734538202391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224124009627976489692134927 336186014441964734538202391)
        ·
          refine ⟨504279021662947101807303587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336186014441964734538202391 504279021662947101807303587)
          ·
            refine ⟨756418532494420652710955381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504279021662947101807303587 756418532494420652710955381)
            ·
              refine ⟨70914237421351936191652067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 756418532494420652710955381 70914237421351936191652067)
              ·
                refine ⟨106371356132027904287478101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70914237421351936191652067 106371356132027904287478101)
                ·
                  refine ⟨311634832418050500842221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 106371356132027904287478101 311634832418050500842221)
                  ·
                    rfl

theorem cell23_5462160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 10].length) (baseStart_5462160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462160 prefixEnd_5462160 := by exact prefixLift 5462160
  have htrace : WordTrace (prefixWord ++ tailWord_5462160) baseStart_5462160 baseEnd_5462160 := by
    simpa [prefixWord, tailWord_5462160, baseEnd_5462160] using wordTrace_append hprefix tailTrace_5462160
  have hstable : (prefixWord ++ tailWord_5462160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462160).length < 2 ^ (prefixWord ++ tailWord_5462160).sum := by decide
  have hdescent : baseEnd_5462160 < baseStart_5462160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462177 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 8]
def baseStart_5462177 : Nat := 118140960795 + 5462177 * 2 ^ 59
def prefixEnd_5462177 : Nat := 4983230072969 + 3 ^ 40 * 5462177 * 2
def baseEnd_5462177 : Nat := 311635802325953437896379

theorem tailTrace_5462177 : CollatzResearch.WordTrace tailWord_5462177 prefixEnd_5462177 311635802325953437896379 := by
  unfold tailWord_5462177
  simp only [CollatzResearch.WordTrace]
  refine ⟨199221961932473069407488785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132814641288315379604992523 199221961932473069407488785)
  ·
    refine ⟨149416471449354802055616589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199221961932473069407488785 149416471449354802055616589)
    ·
      refine ⟨56031176793508050770856221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149416471449354802055616589 56031176793508050770856221)
      ·
        refine ⟨21011691297565519039071083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56031176793508050770856221 21011691297565519039071083)
        ·
          refine ⟨31517536946348278558606625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21011691297565519039071083 31517536946348278558606625)
          ·
            refine ⟨23638152709761208918954969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31517536946348278558606625 23638152709761208918954969)
            ·
              refine ⟨17728614532320906689216227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23638152709761208918954969 17728614532320906689216227)
              ·
                refine ⟨26592921798481360033824341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17728614532320906689216227 26592921798481360033824341)
                ·
                  refine ⟨311635802325953437896379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26592921798481360033824341 311635802325953437896379)
                  ·
                    rfl

theorem cell23_5462177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 8].length) (baseStart_5462177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462177 prefixEnd_5462177 := by exact prefixLift 5462177
  have htrace : WordTrace (prefixWord ++ tailWord_5462177) baseStart_5462177 baseEnd_5462177 := by
    simpa [prefixWord, tailWord_5462177, baseEnd_5462177] using wordTrace_append hprefix tailTrace_5462177
  have hstable : (prefixWord ++ tailWord_5462177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462177).length < 2 ^ (prefixWord ++ tailWord_5462177).sum := by decide
  have hdescent : baseEnd_5462177 < baseStart_5462177 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462227 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 4]
def baseStart_5462227 : Nat := 118140960795 + 5462227 * 2 ^ 59
def prefixEnd_5462227 : Nat := 4983230072969 + 3 ^ 40 * 5462227 * 2
def baseEnd_5462227 : Nat := 2804747894966305745442181

theorem tailTrace_5462227 : CollatzResearch.WordTrace tailWord_5462227 prefixEnd_5462227 2804747894966305745442181 := by
  unfold tailWord_5462227
  simp only [CollatzResearch.WordTrace]
  refine ⟨199223785582291927946808935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132815857054861285297872623 199223785582291927946808935)
  ·
    refine ⟨298835678373437891920213403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199223785582291927946808935 298835678373437891920213403)
    ·
      refine ⟨448253517560156837880320105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298835678373437891920213403 448253517560156837880320105)
      ·
        refine ⟨336190138170117628410240079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 448253517560156837880320105 336190138170117628410240079)
        ·
          refine ⟨504285207255176442615360119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336190138170117628410240079 504285207255176442615360119)
          ·
            refine ⟨756427810882764663923040179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504285207255176442615360119 756427810882764663923040179)
            ·
              refine ⟨1134641716324146995884560269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756427810882764663923040179 1134641716324146995884560269)
              ·
                refine ⟨425490643621555123456710101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1134641716324146995884560269 425490643621555123456710101)
                ·
                  refine ⟨9972436959880198206016643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 425490643621555123456710101 9972436959880198206016643)
                  ·
                    refine ⟨14958655439820297309024965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9972436959880198206016643 14958655439820297309024965)
                    ·
                      refine ⟨2804747894966305745442181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14958655439820297309024965 2804747894966305745442181)
                      ·
                        rfl

theorem cell23_5462227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_5462227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462227 prefixEnd_5462227 := by exact prefixLift 5462227
  have htrace : WordTrace (prefixWord ++ tailWord_5462227) baseStart_5462227 baseEnd_5462227 := by
    simpa [prefixWord, tailWord_5462227, baseEnd_5462227] using wordTrace_append hprefix tailTrace_5462227
  have hstable : (prefixWord ++ tailWord_5462227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462227).length < 2 ^ (prefixWord ++ tailWord_5462227).sum := by decide
  have hdescent : baseEnd_5462227 < baseStart_5462227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462244 : List Nat := [2, 3, 1, 1, 1, 2, 1, 2, 2, 6, 2]
def baseStart_5462244 : Nat := 118140960795 + 5462244 * 2 ^ 59
def prefixEnd_5462244 : Nat := 4983230072969 + 3 ^ 40 * 5462244 * 2
def baseEnd_5462244 : Nat := 2804756624137432178929603

theorem tailTrace_5462244 : CollatzResearch.WordTrace tailWord_5462244 prefixEnd_5462244 2804756624137432178929603 := by
  unfold tailWord_5462244
  simp only [CollatzResearch.WordTrace]
  refine ⟨99612202811615169925088893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132816270415486893233451857 99612202811615169925088893)
  ·
    refine ⟨37354576054355688721908335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99612202811615169925088893 37354576054355688721908335)
    ·
      refine ⟨56031864081533533082862503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37354576054355688721908335 56031864081533533082862503)
      ·
        refine ⟨84047796122300299624293755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56031864081533533082862503 84047796122300299624293755)
        ·
          refine ⟨126071694183450449436440633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84047796122300299624293755 126071694183450449436440633)
          ·
            refine ⟨94553770637587837077330475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126071694183450449436440633 94553770637587837077330475)
            ·
              refine ⟨141830655956381755615995713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94553770637587837077330475 141830655956381755615995713)
              ·
                refine ⟨106372991967286316711996785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141830655956381755615995713 106372991967286316711996785)
                ·
                  refine ⟨79779743975464737533997589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106372991967286316711996785 79779743975464737533997589)
                  ·
                    refine ⟨3739675498849909571906137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79779743975464737533997589 3739675498849909571906137)
                    ·
                      refine ⟨2804756624137432178929603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3739675498849909571906137 2804756624137432178929603)
                      ·
                        rfl

theorem cell23_5462244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 2, 2, 6, 2].length) (baseStart_5462244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462244 prefixEnd_5462244 := by exact prefixLift 5462244
  have htrace : WordTrace (prefixWord ++ tailWord_5462244) baseStart_5462244 baseEnd_5462244 := by
    simpa [prefixWord, tailWord_5462244, baseEnd_5462244] using wordTrace_append hprefix tailTrace_5462244
  have hstable : (prefixWord ++ tailWord_5462244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462244).length < 2 ^ (prefixWord ++ tailWord_5462244).sum := by decide
  have hdescent : baseEnd_5462244 < baseStart_5462244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462254 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 6, 4]
def baseStart_5462254 : Nat := 118140960795 + 5462254 * 2 ^ 59
def prefixEnd_5462254 : Nat := 4983230072969 + 3 ^ 40 * 5462254 * 2
def baseEnd_5462254 : Nat := 934920586314659046601519

theorem tailTrace_5462254 : CollatzResearch.WordTrace tailWord_5462254 prefixEnd_5462254 934920586314659046601519 := by
  unfold tailWord_5462254
  simp only [CollatzResearch.WordTrace]
  refine ⟨24903096294149263944755227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132816513568796074372027877 24903096294149263944755227)
  ·
    refine ⟨37354644441223895917132841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24903096294149263944755227 37354644441223895917132841)
    ·
      refine ⟨28015983330917921937849631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37354644441223895917132841 28015983330917921937849631)
      ·
        refine ⟨42023974996376882906774447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28015983330917921937849631 42023974996376882906774447)
        ·
          refine ⟨63035962494565324360161671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42023974996376882906774447 63035962494565324360161671)
          ·
            refine ⟨94553943741847986540242507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63035962494565324360161671 94553943741847986540242507)
            ·
              refine ⟨141830915612771979810363761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94553943741847986540242507 141830915612771979810363761)
              ·
                refine ⟨106373186709578984857772821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141830915612771979810363761 106373186709578984857772821)
                ·
                  refine ⟨4986243127011514915208101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106373186709578984857772821 4986243127011514915208101)
                  ·
                    refine ⟨934920586314659046601519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4986243127011514915208101 934920586314659046601519)
                    ·
                      rfl

theorem cell23_5462254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 6, 4].length) (baseStart_5462254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462254 prefixEnd_5462254 := by exact prefixLift 5462254
  have htrace : WordTrace (prefixWord ++ tailWord_5462254) baseStart_5462254 baseEnd_5462254 := by
    simpa [prefixWord, tailWord_5462254, baseEnd_5462254] using wordTrace_append hprefix tailTrace_5462254
  have hstable : (prefixWord ++ tailWord_5462254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462254).length < 2 ^ (prefixWord ++ tailWord_5462254).sum := by decide
  have hdescent : baseEnd_5462254 < baseStart_5462254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462257 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_5462257 : Nat := 118140960795 + 5462257 * 2 ^ 59
def prefixEnd_5462257 : Nat := 4983230072969 + 3 ^ 40 * 5462257 * 2
def baseEnd_5462257 : Nat := 2804763299385940628067043

theorem tailTrace_5462257 : CollatzResearch.WordTrace tailWord_5462257 prefixEnd_5462257 2804763299385940628067043 := by
  unfold tailWord_5462257
  simp only [CollatzResearch.WordTrace]
  refine ⟨199224879772183243070401025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132816586514788828713600683 199224879772183243070401025)
  ·
    refine ⟨149418659829137432302800769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199224879772183243070401025 149418659829137432302800769)
    ·
      refine ⟨112063994871853074227100577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149418659829137432302800769 112063994871853074227100577)
      ·
        refine ⟨84047996153889805670325433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112063994871853074227100577 84047996153889805670325433)
        ·
          refine ⟨63035997115417354252744075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84047996153889805670325433 63035997115417354252744075)
          ·
            refine ⟨94553995673126031379116113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63035997115417354252744075 94553995673126031379116113)
            ·
              refine ⟨70915496754844523534337085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94553995673126031379116113 70915496754844523534337085)
              ·
                refine ⟨26593311283066696325376407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70915496754844523534337085 26593311283066696325376407)
                ·
                  refine ⟨39889966924600044488064611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26593311283066696325376407 39889966924600044488064611)
                  ·
                    refine ⟨59834950386900066732096917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39889966924600044488064611 59834950386900066732096917)
                    ·
                      refine ⟨2804763299385940628067043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59834950386900066732096917 2804763299385940628067043)
                      ·
                        rfl

theorem cell23_5462257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_5462257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462257 prefixEnd_5462257 := by exact prefixLift 5462257
  have htrace : WordTrace (prefixWord ++ tailWord_5462257) baseStart_5462257 baseEnd_5462257 := by
    simpa [prefixWord, tailWord_5462257, baseEnd_5462257] using wordTrace_append hprefix tailTrace_5462257
  have hstable : (prefixWord ++ tailWord_5462257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462257).length < 2 ^ (prefixWord ++ tailWord_5462257).sum := by decide
  have hdescent : baseEnd_5462257 < baseStart_5462257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462281 : List Nat := [1, 2, 1, 1, 3, 5, 1, 3, 1, 2, 3]
def baseStart_5462281 : Nat := 118140960795 + 5462281 * 2 ^ 59
def prefixEnd_5462281 : Nat := 4983230072969 + 3 ^ 40 * 5462281 * 2
def baseEnd_5462281 : Nat := 2804775622921648534166933

theorem tailTrace_5462281 : CollatzResearch.WordTrace tailWord_5462281 prefixEnd_5462281 2804775622921648534166933 := by
  unfold tailWord_5462281
  simp only [CollatzResearch.WordTrace]
  refine ⟨199225755124096295169274697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132817170082730863446183131 199225755124096295169274697)
  ·
    refine ⟨149419316343072221376956023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199225755124096295169274697 149419316343072221376956023)
    ·
      refine ⟨224128974514608332065434035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149419316343072221376956023 224128974514608332065434035)
      ·
        refine ⟨336193461771912498098151053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224128974514608332065434035 336193461771912498098151053)
        ·
          refine ⟨126072548164467186786806645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336193461771912498098151053 126072548164467186786806645)
          ·
            refine ⟨11819301390418798761263123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126072548164467186786806645 11819301390418798761263123)
            ·
              refine ⟨17728952085628198141894685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11819301390418798761263123 17728952085628198141894685)
              ·
                refine ⟨6648357032110574303210507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17728952085628198141894685 6648357032110574303210507)
                ·
                  refine ⟨9972535548165861454815761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6648357032110574303210507 9972535548165861454815761)
                  ·
                    refine ⟨7479401661124396091111821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9972535548165861454815761 7479401661124396091111821)
                    ·
                      refine ⟨2804775622921648534166933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7479401661124396091111821 2804775622921648534166933)
                      ·
                        rfl

theorem cell23_5462281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 2, 3].length) (baseStart_5462281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462281 prefixEnd_5462281 := by exact prefixLift 5462281
  have htrace : WordTrace (prefixWord ++ tailWord_5462281) baseStart_5462281 baseEnd_5462281 := by
    simpa [prefixWord, tailWord_5462281, baseEnd_5462281] using wordTrace_append hprefix tailTrace_5462281
  have hstable : (prefixWord ++ tailWord_5462281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462281).length < 2 ^ (prefixWord ++ tailWord_5462281).sum := by decide
  have hdescent : baseEnd_5462281 < baseStart_5462281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462295 : List Nat := [1, 1, 3, 4, 1, 2, 2, 4, 1, 2, 2]
def baseStart_5462295 : Nat := 118140960795 + 5462295 * 2 ^ 59
def prefixEnd_5462295 : Nat := 4983230072969 + 3 ^ 40 * 5462295 * 2
def baseEnd_5462295 : Nat := 2804782811650811479391869

theorem tailTrace_5462295 : CollatzResearch.WordTrace tailWord_5462295 prefixEnd_5462295 2804782811650811479391869 := by
  unfold tailWord_5462295
  simp only [CollatzResearch.WordTrace]
  refine ⟨199226265746045575560284339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132817510497363717040189559 199226265746045575560284339)
  ·
    refine ⟨298839398619068363340426509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199226265746045575560284339 298839398619068363340426509)
    ·
      refine ⟨112064774482150636252659941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298839398619068363340426509 112064774482150636252659941)
      ·
        refine ⟨21012145215403244297373739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112064774482150636252659941 21012145215403244297373739)
        ·
          refine ⟨31518217823104866446060609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21012145215403244297373739 31518217823104866446060609)
          ·
            refine ⟨23638663367328649834545457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31518217823104866446060609 23638663367328649834545457)
            ·
              refine ⟨17728997525496487375909093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23638663367328649834545457 17728997525496487375909093)
              ·
                refine ⟨3324187036030591382982955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17728997525496487375909093 3324187036030591382982955)
                ·
                  refine ⟨4986280554045887074474433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3324187036030591382982955 4986280554045887074474433)
                  ·
                    refine ⟨3739710415534415305855825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4986280554045887074474433 3739710415534415305855825)
                    ·
                      refine ⟨2804782811650811479391869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3739710415534415305855825 2804782811650811479391869)
                      ·
                        rfl

theorem cell23_5462295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 4, 1, 2, 2].length) (baseStart_5462295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462295 prefixEnd_5462295 := by exact prefixLift 5462295
  have htrace : WordTrace (prefixWord ++ tailWord_5462295) baseStart_5462295 baseEnd_5462295 := by
    simpa [prefixWord, tailWord_5462295, baseEnd_5462295] using wordTrace_append hprefix tailTrace_5462295
  have hstable : (prefixWord ++ tailWord_5462295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462295).length < 2 ^ (prefixWord ++ tailWord_5462295).sum := by decide
  have hdescent : baseEnd_5462295 < baseStart_5462295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462327 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 1, 8]
def baseStart_5462327 : Nat := 118140960795 + 5462327 * 2 ^ 59
def prefixEnd_5462327 : Nat := 4983230072969 + 3 ^ 40 * 5462327 * 2
def baseEnd_5462327 : Nat := 934933081010585118063907

theorem tailTrace_5462327 : CollatzResearch.WordTrace tailWord_5462327 prefixEnd_5462327 934933081010585118063907 := by
  unfold tailWord_5462327
  simp only [CollatzResearch.WordTrace]
  refine ⟨199227432881929645025449235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132818288587953096683632823 199227432881929645025449235)
  ·
    refine ⟨298841149322894467538173853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199227432881929645025449235 298841149322894467538173853)
    ·
      refine ⟨112065430996085425326815195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 298841149322894467538173853 112065430996085425326815195)
      ·
        refine ⟨168098146494128137990222793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112065430996085425326815195 168098146494128137990222793)
        ·
          refine ⟨126073609870596103492667095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168098146494128137990222793 126073609870596103492667095)
          ·
            refine ⟨189110414805894155239000643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126073609870596103492667095 189110414805894155239000643)
            ·
              refine ⟨283665622208841232858500965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189110414805894155239000643 283665622208841232858500965)
              ·
                refine ⟨53187304164157731160968931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 283665622208841232858500965 53187304164157731160968931)
                ·
                  refine ⟨79780956246236596741453397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53187304164157731160968931 79780956246236596741453397)
                  ·
                    refine ⟨934933081010585118063907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 79780956246236596741453397 934933081010585118063907)
                    ·
                      rfl

theorem cell23_5462327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_5462327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462327 prefixEnd_5462327 := by exact prefixLift 5462327
  have htrace : WordTrace (prefixWord ++ tailWord_5462327) baseStart_5462327 baseEnd_5462327 := by
    simpa [prefixWord, tailWord_5462327, baseEnd_5462327] using wordTrace_append hprefix tailTrace_5462327
  have hstable : (prefixWord ++ tailWord_5462327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462327).length < 2 ^ (prefixWord ++ tailWord_5462327).sum := by decide
  have hdescent : baseEnd_5462327 < baseStart_5462327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462347 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 6]
def baseStart_5462347 : Nat := 118140960795 + 5462347 * 2 ^ 59
def prefixEnd_5462347 : Nat := 4983230072969 + 3 ^ 40 * 5462347 * 2
def baseEnd_5462347 : Nat := 2804809512644845275941629

theorem tailTrace_5462347 : CollatzResearch.WordTrace tailWord_5462347 prefixEnd_5462347 2804809512644845275941629 := by
  unfold tailWord_5462347
  simp only [CollatzResearch.WordTrace]
  refine ⟨199228162341857188441177295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132818774894571458960784863 199228162341857188441177295)
  ·
    refine ⟨298842243512785782661765943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199228162341857188441177295 298842243512785782661765943)
    ·
      refine ⟨448263365269178673992648915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298842243512785782661765943 448263365269178673992648915)
      ·
        refine ⟨672395047903768010988973373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448263365269178673992648915 672395047903768010988973373)
        ·
          refine ⟨252148142963913004120865015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 672395047903768010988973373 252148142963913004120865015)
          ·
            refine ⟨378222214445869506181297523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252148142963913004120865015 378222214445869506181297523)
            ·
              refine ⟨567333321668804259271946285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 378222214445869506181297523 567333321668804259271946285)
              ·
                refine ⟨212749995625801597226979857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 567333321668804259271946285 212749995625801597226979857)
                ·
                  refine ⟨159562496719351197920234893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 212749995625801597226979857 159562496719351197920234893)
                  ·
                    refine ⟨59835936269756699220088085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159562496719351197920234893 59835936269756699220088085)
                    ·
                      refine ⟨2804809512644845275941629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59835936269756699220088085 2804809512644845275941629)
                      ·
                        rfl

theorem cell23_5462347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 6].length) (baseStart_5462347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462347 prefixEnd_5462347 := by exact prefixLift 5462347
  have htrace : WordTrace (prefixWord ++ tailWord_5462347) baseStart_5462347 baseEnd_5462347 := by
    simpa [prefixWord, tailWord_5462347, baseEnd_5462347] using wordTrace_append hprefix tailTrace_5462347
  have hstable : (prefixWord ++ tailWord_5462347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462347).length < 2 ^ (prefixWord ++ tailWord_5462347).sum := by decide
  have hdescent : baseEnd_5462347 < baseStart_5462347 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462366 : List Nat := [4, 4, 2, 1, 1, 2, 1, 2, 1, 2, 3]
def baseStart_5462366 : Nat := 118140960795 + 5462366 * 2 ^ 59
def prefixEnd_5462366 : Nat := 4983230072969 + 3 ^ 40 * 5462366 * 2
def baseEnd_5462366 : Nat := 2804819268777280701604043

theorem tailTrace_5462366 : CollatzResearch.WordTrace tailWord_5462366 prefixEnd_5462366 2804819268777280701604043 := by
  unfold tailWord_5462366
  simp only [CollatzResearch.WordTrace]
  refine ⟨24903606916098544335764869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132819236885858903124079301 24903606916098544335764869)
  ·
    refine ⟨4669426296768477062955913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24903606916098544335764869 4669426296768477062955913)
    ·
      refine ⟨3502069722576357797216935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4669426296768477062955913 3502069722576357797216935)
      ·
        refine ⟨5253104583864536695825403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3502069722576357797216935 5253104583864536695825403)
        ·
          refine ⟨7879656875796805043738105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5253104583864536695825403 7879656875796805043738105)
          ·
            refine ⟨5909742656847603782803579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7879656875796805043738105 5909742656847603782803579)
            ·
              refine ⟨8864613985271405674205369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5909742656847603782803579 8864613985271405674205369)
              ·
                refine ⟨6648460488953554255654027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8864613985271405674205369 6648460488953554255654027)
                ·
                  refine ⟨9972690733430331383481041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6648460488953554255654027 9972690733430331383481041)
                  ·
                    refine ⟨7479518050072748537610781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9972690733430331383481041 7479518050072748537610781)
                    ·
                      refine ⟨2804819268777280701604043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7479518050072748537610781 2804819268777280701604043)
                      ·
                        rfl

theorem cell23_5462366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_5462366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462366 prefixEnd_5462366 := by exact prefixLift 5462366
  have htrace : WordTrace (prefixWord ++ tailWord_5462366) baseStart_5462366 baseEnd_5462366 := by
    simpa [prefixWord, tailWord_5462366, baseEnd_5462366] using wordTrace_append hprefix tailTrace_5462366
  have hstable : (prefixWord ++ tailWord_5462366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462366).length < 2 ^ (prefixWord ++ tailWord_5462366).sum := by decide
  have hdescent : baseEnd_5462366 < baseStart_5462366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462411 : List Nat := [1, 1, 1, 1, 4, 4, 1, 1, 2, 5, 2]
def baseStart_5462411 : Nat := 118140960795 + 5462411 * 2 ^ 59
def prefixEnd_5462411 : Nat := 4983230072969 + 3 ^ 40 * 5462411 * 2
def baseEnd_5462411 : Nat := 2804842375406733025541335

theorem tailTrace_5462411 : CollatzResearch.WordTrace tailWord_5462411 prefixEnd_5462411 2804842375406733025541335 := by
  unfold tailWord_5462411
  simp only [CollatzResearch.WordTrace]
  refine ⟨199230496613625327371507087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132820331075750218247671391 199230496613625327371507087)
  ·
    refine ⟨298845744920437991057260631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199230496613625327371507087 298845744920437991057260631)
    ·
      refine ⟨448268617380656986585890947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298845744920437991057260631 448268617380656986585890947)
      ·
        refine ⟨672402926070985479878836421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448268617380656986585890947 672402926070985479878836421)
        ·
          refine ⟨126075548638309777477281829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 672402926070985479878836421 126075548638309777477281829)
          ·
            refine ⟨23639165369683083276990343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126075548638309777477281829 23639165369683083276990343)
            ·
              refine ⟨35458748054524624915485515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23639165369683083276990343 35458748054524624915485515)
              ·
                refine ⟨53188122081786937373228273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35458748054524624915485515 53188122081786937373228273)
                ·
                  refine ⟨39891091561340203029921205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53188122081786937373228273 39891091561340203029921205)
                  ·
                    refine ⟨3739789833875644034055113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39891091561340203029921205 3739789833875644034055113)
                    ·
                      refine ⟨2804842375406733025541335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3739789833875644034055113 2804842375406733025541335)
                      ·
                        rfl

theorem cell23_5462411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 2, 5, 2].length) (baseStart_5462411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462411 prefixEnd_5462411 := by exact prefixLift 5462411
  have htrace : WordTrace (prefixWord ++ tailWord_5462411) baseStart_5462411 baseEnd_5462411 := by
    simpa [prefixWord, tailWord_5462411, baseEnd_5462411] using wordTrace_append hprefix tailTrace_5462411
  have hstable : (prefixWord ++ tailWord_5462411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462411).length < 2 ^ (prefixWord ++ tailWord_5462411).sum := by decide
  have hdescent : baseEnd_5462411 < baseStart_5462411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462531 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 4]
def baseStart_5462531 : Nat := 118140960795 + 5462531 * 2 ^ 59
def prefixEnd_5462531 : Nat := 4983230072969 + 3 ^ 40 * 5462531 * 2
def baseEnd_5462531 : Nat := 2804903993085272556040783

theorem tailTrace_5462531 : CollatzResearch.WordTrace tailWord_5462531 prefixEnd_5462531 2804903993085272556040783 := by
  unfold tailWord_5462531
  simp only [CollatzResearch.WordTrace]
  refine ⟨199234873373190587865875447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132823248915460391910583631 199234873373190587865875447)
  ·
    refine ⟨298852310059785881798813171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199234873373190587865875447 298852310059785881798813171)
    ·
      refine ⟨448278465089678822698219757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298852310059785881798813171 448278465089678822698219757)
      ·
        refine ⟨168104424408629558511832409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 448278465089678822698219757 168104424408629558511832409)
        ·
          refine ⟨126078318306472168883874307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168104424408629558511832409 126078318306472168883874307)
          ·
            refine ⟨189117477459708253325811461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126078318306472168883874307 189117477459708253325811461)
            ·
              refine ⟨35459527023695297498589649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189117477459708253325811461 35459527023695297498589649)
              ·
                refine ⟨26594645267771473123942237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35459527023695297498589649 26594645267771473123942237)
                ·
                  refine ⟨9972991975414302421478339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26594645267771473123942237 9972991975414302421478339)
                  ·
                    refine ⟨14959487963121453632217509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9972991975414302421478339 14959487963121453632217509)
                    ·
                      refine ⟨2804903993085272556040783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14959487963121453632217509 2804903993085272556040783)
                      ·
                        rfl

theorem cell23_5462531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_5462531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462531 prefixEnd_5462531 := by exact prefixLift 5462531
  have htrace : WordTrace (prefixWord ++ tailWord_5462531) baseStart_5462531 baseEnd_5462531 := by
    simpa [prefixWord, tailWord_5462531, baseEnd_5462531] using wordTrace_append hprefix tailTrace_5462531
  have hstable : (prefixWord ++ tailWord_5462531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462531).length < 2 ^ (prefixWord ++ tailWord_5462531).sum := by decide
  have hdescent : baseEnd_5462531 < baseStart_5462531 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462588 : List Nat := [2, 2, 2, 2, 3, 3, 1, 8]
def baseStart_5462588 : Nat := 118140960795 + 5462588 * 2 ^ 59
def prefixEnd_5462588 : Nat := 4983230072969 + 3 ^ 40 * 5462588 * 2
def baseEnd_5462588 : Nat := 103886417091947364186223

theorem tailTrace_5462588 : CollatzResearch.WordTrace tailWord_5462588 prefixEnd_5462588 103886417091947364186223 := by
  unfold tailWord_5462588
  simp only [CollatzResearch.WordTrace]
  refine ⟨99618476166992043300350209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132824634889322724400466945 99618476166992043300350209)
  ·
    refine ⟨74713857125244032475262657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99618476166992043300350209 74713857125244032475262657)
    ·
      refine ⟨56035392843933024356446993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74713857125244032475262657 56035392843933024356446993)
      ·
        refine ⟨42026544632949768267335245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56035392843933024356446993 42026544632949768267335245)
        ·
          refine ⟨15759954237356163100250717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42026544632949768267335245 15759954237356163100250717)
          ·
            refine ⟨5909982839008561162594019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15759954237356163100250717 5909982839008561162594019)
            ·
              refine ⟨8864974258512841743891029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5909982839008561162594019 8864974258512841743891029)
              ·
                refine ⟨103886417091947364186223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8864974258512841743891029 103886417091947364186223)
                ·
                  rfl

theorem cell23_5462588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 8].length) (baseStart_5462588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462588 prefixEnd_5462588 := by exact prefixLift 5462588
  have htrace : WordTrace (prefixWord ++ tailWord_5462588) baseStart_5462588 baseEnd_5462588 := by
    simpa [prefixWord, tailWord_5462588, baseEnd_5462588] using wordTrace_append hprefix tailTrace_5462588
  have hstable : (prefixWord ++ tailWord_5462588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462588).length < 2 ^ (prefixWord ++ tailWord_5462588).sum := by decide
  have hdescent : baseEnd_5462588 < baseStart_5462588 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462605 : List Nat := [1, 6, 1, 1, 2, 2, 3, 7]
def baseStart_5462605 : Nat := 118140960795 + 5462605 * 2 ^ 59
def prefixEnd_5462605 : Nat := 4983230072969 + 3 ^ 40 * 5462605 * 2
def baseEnd_5462605 : Nat := 103886740394581676537609

theorem tailTrace_5462605 : CollatzResearch.WordTrace tailWord_5462605 prefixEnd_5462605 103886740394581676537609 := by
  unfold tailWord_5462605
  simp only [CollatzResearch.WordTrace]
  refine ⟨199237572374922498504069269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132825048249948332336046179 199237572374922498504069269)
  ·
    refine ⟨9339261205074492117378247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 199237572374922498504069269 9339261205074492117378247)
    ·
      refine ⟨14008891807611738176067371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9339261205074492117378247 14008891807611738176067371)
      ·
        refine ⟨21013337711417607264101057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14008891807611738176067371 21013337711417607264101057)
        ·
          refine ⟨15760003283563205448075793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21013337711417607264101057 15760003283563205448075793)
          ·
            refine ⟨11820002462672404086056845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15760003283563205448075793 11820002462672404086056845)
            ·
              refine ⟨4432500923502151532271317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11820002462672404086056845 4432500923502151532271317)
              ·
                refine ⟨103886740394581676537609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4432500923502151532271317 103886740394581676537609)
                ·
                  rfl

theorem cell23_5462605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 7].length) (baseStart_5462605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462605 prefixEnd_5462605 := by exact prefixLift 5462605
  have htrace : WordTrace (prefixWord ++ tailWord_5462605) baseStart_5462605 baseEnd_5462605 := by
    simpa [prefixWord, tailWord_5462605, baseEnd_5462605] using wordTrace_append hprefix tailTrace_5462605
  have hstable : (prefixWord ++ tailWord_5462605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462605).length < 2 ^ (prefixWord ++ tailWord_5462605).sum := by decide
  have hdescent : baseEnd_5462605 < baseStart_5462605 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462622 : List Nat := [4, 4, 1, 2, 1, 1, 10]
def baseStart_5462622 : Nat := 118140960795 + 5462622 * 2 ^ 59
def prefixEnd_5462622 : Nat := 4983230072969 + 3 ^ 40 * 5462622 * 2
def baseEnd_5462622 : Nat := 34629021232405329629665

theorem tailTrace_5462622 : CollatzResearch.WordTrace tailWord_5462622 prefixEnd_5462622 34629021232405329629665 := by
  unfold tailWord_5462622
  simp only [CollatzResearch.WordTrace]
  refine ⟨24904774051982613800929765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132825461610573940271625413 24904774051982613800929765)
  ·
    refine ⟨4669645134746740087674331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24904774051982613800929765 4669645134746740087674331)
    ·
      refine ⟨7004467702120110131511497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4669645134746740087674331 7004467702120110131511497)
      ·
        refine ⟨5253350776590082598633623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7004467702120110131511497 5253350776590082598633623)
        ·
          refine ⟨7880026164885123897950435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5253350776590082598633623 7880026164885123897950435)
          ·
            refine ⟨11820039247327685846925653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7880026164885123897950435 11820039247327685846925653)
            ·
              refine ⟨34629021232405329629665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 11820039247327685846925653 34629021232405329629665)
              ·
                rfl

theorem cell23_5462622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 10].length) (baseStart_5462622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462622 prefixEnd_5462622 := by exact prefixLift 5462622
  have htrace : WordTrace (prefixWord ++ tailWord_5462622) baseStart_5462622 baseEnd_5462622 := by
    simpa [prefixWord, tailWord_5462622, baseEnd_5462622] using wordTrace_append hprefix tailTrace_5462622
  have hstable : (prefixWord ++ tailWord_5462622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462622).length < 2 ^ (prefixWord ++ tailWord_5462622).sum := by decide
  have hdescent : baseEnd_5462622 < baseStart_5462622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462626 : List Nat := [3, 3, 2, 3, 2, 1, 1, 2, 2, 4]
def baseStart_5462626 : Nat := 118140960795 + 5462626 * 2 ^ 59
def prefixEnd_5462626 : Nat := 4983230072969 + 3 ^ 40 * 5462626 * 2
def baseEnd_5462626 : Nat := 934984257915816561450949

theorem tailTrace_5462626 : CollatzResearch.WordTrace tailWord_5462626 prefixEnd_5462626 934984257915816561450949 := by
  unfold tailWord_5462626
  simp only [CollatzResearch.WordTrace]
  refine ⟨49809584576961604772645933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132825558871897612727055821 49809584576961604772645933)
  ·
    refine ⟨18678594216360601789742225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49809584576961604772645933 18678594216360601789742225)
    ·
      refine ⟨14008945662270451342306669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18678594216360601789742225 14008945662270451342306669)
      ·
        refine ⟨5253354623351419253365001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14008945662270451342306669 5253354623351419253365001)
        ·
          refine ⟨3940015967513564440023751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5253354623351419253365001 3940015967513564440023751)
          ·
            refine ⟨5910023951270346660035627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3940015967513564440023751 5910023951270346660035627)
            ·
              refine ⟨8865035926905519990053441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5910023951270346660035627 8865035926905519990053441)
              ·
                refine ⟨6648776945179139992540081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8865035926905519990053441 6648776945179139992540081)
                ·
                  refine ⟨4986582708884354994405061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6648776945179139992540081 4986582708884354994405061)
                  ·
                    refine ⟨934984257915816561450949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4986582708884354994405061 934984257915816561450949)
                    ·
                      rfl

theorem cell23_5462626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 2, 4].length) (baseStart_5462626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462626 prefixEnd_5462626 := by exact prefixLift 5462626
  have htrace : WordTrace (prefixWord ++ tailWord_5462626) baseStart_5462626 baseEnd_5462626 := by
    simpa [prefixWord, tailWord_5462626, baseEnd_5462626] using wordTrace_append hprefix tailTrace_5462626
  have hstable : (prefixWord ++ tailWord_5462626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462626).length < 2 ^ (prefixWord ++ tailWord_5462626).sum := by decide
  have hdescent : baseEnd_5462626 < baseStart_5462626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462632 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 4, 1, 3]
def baseStart_5462632 : Nat := 118140960795 + 5462632 * 2 ^ 59
def prefixEnd_5462632 : Nat := 4983230072969 + 3 ^ 40 * 5462632 * 2
def baseEnd_5462632 : Nat := 2804955854631376660877819

theorem tailTrace_5462632 : CollatzResearch.WordTrace tailWord_5462632 prefixEnd_5462632 2804955854631376660877819 := by
  unfold tailWord_5462632
  simp only [CollatzResearch.WordTrace]
  refine ⟨99619278572912341057651075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132825704763883121410201433 99619278572912341057651075)
  ·
    refine ⟨149428917859368511586476613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99619278572912341057651075 149428917859368511586476613)
    ·
      refine ⟨28017922098631595922464365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149428917859368511586476613 28017922098631595922464365)
      ·
        refine ⟨10506720786986848470924137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28017922098631595922464365 10506720786986848470924137)
        ·
          refine ⟨7880040590240136353193103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10506720786986848470924137 7880040590240136353193103)
          ·
            refine ⟨11820060885360204529789655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7880040590240136353193103 11820060885360204529789655)
            ·
              refine ⟨17730091328040306794684483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11820060885360204529789655 17730091328040306794684483)
              ·
                refine ⟨26595136992060460192026725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17730091328040306794684483 26595136992060460192026725)
                ·
                  refine ⟨4986588186011336286005011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26595136992060460192026725 4986588186011336286005011)
                  ·
                    refine ⟨7479882279017004429007517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4986588186011336286005011 7479882279017004429007517)
                    ·
                      refine ⟨2804955854631376660877819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7479882279017004429007517 2804955854631376660877819)
                      ·
                        rfl

theorem cell23_5462632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_5462632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462632 prefixEnd_5462632 := by exact prefixLift 5462632
  have htrace : WordTrace (prefixWord ++ tailWord_5462632) baseStart_5462632 baseEnd_5462632 := by
    simpa [prefixWord, tailWord_5462632, baseEnd_5462632] using wordTrace_append hprefix tailTrace_5462632
  have hstable : (prefixWord ++ tailWord_5462632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462632).length < 2 ^ (prefixWord ++ tailWord_5462632).sum := by decide
  have hdescent : baseEnd_5462632 < baseStart_5462632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462641 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_5462641 : Nat := 118140960795 + 5462641 * 2 ^ 59
def prefixEnd_5462641 : Nat := 4983230072969 + 3 ^ 40 * 5462641 * 2
def baseEnd_5462641 : Nat := 2804960475957267125665277

theorem tailTrace_5462641 : CollatzResearch.WordTrace tailWord_5462641 prefixEnd_5462641 2804960475957267125665277 := by
  unfold tailWord_5462641
  simp only [CollatzResearch.WordTrace]
  refine ⟨199238885402792076652379777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132825923601861384434919851 199238885402792076652379777)
  ·
    refine ⟨149429164052094057489284833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199238885402792076652379777 149429164052094057489284833)
    ·
      refine ⟨112071873039070543116963625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149429164052094057489284833 112071873039070543116963625)
      ·
        refine ⟨84053904779302907337722719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112071873039070543116963625 84053904779302907337722719)
        ·
          refine ⟨126080857168954361006584079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84053904779302907337722719 126080857168954361006584079)
          ·
            refine ⟨189121285753431541509876119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126080857168954361006584079 189121285753431541509876119)
            ·
              refine ⟨283681928630147312264814179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189121285753431541509876119 283681928630147312264814179)
              ·
                refine ⟨425522892945220968397221269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283681928630147312264814179 425522892945220968397221269)
                ·
                  refine ⟨19946385606807232893619747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 425522892945220968397221269 19946385606807232893619747)
                  ·
                    refine ⟨29919578410210849340429621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19946385606807232893619747 29919578410210849340429621)
                    ·
                      refine ⟨2804960475957267125665277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29919578410210849340429621 2804960475957267125665277)
                      ·
                        rfl

theorem cell23_5462641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_5462641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462641 prefixEnd_5462641 := by exact prefixLift 5462641
  have htrace : WordTrace (prefixWord ++ tailWord_5462641) baseStart_5462641 baseEnd_5462641 := by
    simpa [prefixWord, tailWord_5462641, baseEnd_5462641] using wordTrace_append hprefix tailTrace_5462641
  have hstable : (prefixWord ++ tailWord_5462641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462641).length < 2 ^ (prefixWord ++ tailWord_5462641).sum := by decide
  have hdescent : baseEnd_5462641 < baseStart_5462641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462651 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 4]
def baseStart_5462651 : Nat := 118140960795 + 5462651 * 2 ^ 59
def prefixEnd_5462651 : Nat := 4983230072969 + 3 ^ 40 * 5462651 * 2
def baseEnd_5462651 : Nat := 2804965610763812086540231

theorem tailTrace_5462651 : CollatzResearch.WordTrace tailWord_5462651 prefixEnd_5462651 2804965610763812086540231 := by
  unfold tailWord_5462651
  simp only [CollatzResearch.WordTrace]
  refine ⟨199239250132755848360243807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132826166755170565573495871 199239250132755848360243807)
  ·
    refine ⟨298858875199133772540365711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199239250132755848360243807 298858875199133772540365711)
    ·
      refine ⟨448288312798700658810548567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298858875199133772540365711 448288312798700658810548567)
      ·
        refine ⟨672432469198050988215822851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448288312798700658810548567 672432469198050988215822851)
        ·
          refine ⟨1008648703797076482323734277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 672432469198050988215822851 1008648703797076482323734277)
          ·
            refine ⟨189121631961951840435700177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1008648703797076482323734277 189121631961951840435700177)
            ·
              refine ⟨141841223971463880326775133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189121631961951840435700177 141841223971463880326775133)
              ·
                refine ⟨53190458989298955122540675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141841223971463880326775133 53190458989298955122540675)
                ·
                  refine ⟨79785688483948432683811013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53190458989298955122540675 79785688483948432683811013)
                  ·
                    refine ⟨14959816590740331128214565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79785688483948432683811013 14959816590740331128214565)
                    ·
                      refine ⟨2804965610763812086540231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14959816590740331128214565 2804965610763812086540231)
                      ·
                        rfl

theorem cell23_5462651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 4].length) (baseStart_5462651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462651 prefixEnd_5462651 := by exact prefixLift 5462651
  have htrace : WordTrace (prefixWord ++ tailWord_5462651) baseStart_5462651 baseEnd_5462651 := by
    simpa [prefixWord, tailWord_5462651, baseEnd_5462651] using wordTrace_append hprefix tailTrace_5462651
  have hstable : (prefixWord ++ tailWord_5462651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462651).length < 2 ^ (prefixWord ++ tailWord_5462651).sum := by decide
  have hdescent : baseEnd_5462651 < baseStart_5462651 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462691 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 3, 7]
def baseStart_5462691 : Nat := 118140960795 + 5462691 * 2 ^ 59
def prefixEnd_5462691 : Nat := 4983230072969 + 3 ^ 40 * 5462691 * 2
def baseEnd_5462691 : Nat := 934995383329997310013349

theorem tailTrace_5462691 : CollatzResearch.WordTrace tailWord_5462691 prefixEnd_5462691 934995383329997310013349 := by
  unfold tailWord_5462691
  simp only [CollatzResearch.WordTrace]
  refine ⟨199240709052610935191699927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132827139368407290127799951 199240709052610935191699927)
  ·
    refine ⟨298861063578916402787549891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199240709052610935191699927 298861063578916402787549891)
    ·
      refine ⟨448291595368374604181324837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298861063578916402787549891 448291595368374604181324837)
      ·
        refine ⟨84054674131570238283998407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 448291595368374604181324837 84054674131570238283998407)
        ·
          refine ⟨126082011197355357425997611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84054674131570238283998407 126082011197355357425997611)
          ·
            refine ⟨189123016796033036138996417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126082011197355357425997611 189123016796033036138996417)
            ·
              refine ⟨141842262597024777104247313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189123016796033036138996417 141842262597024777104247313)
              ·
                refine ⟨106381696947768582828185485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141842262597024777104247313 106381696947768582828185485)
                ·
                  refine ⟨39893136355413218560569557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106381696947768582828185485 39893136355413218560569557)
                  ·
                    refine ⟨934995383329997310013349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39893136355413218560569557 934995383329997310013349)
                    ·
                      rfl

theorem cell23_5462691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 7].length) (baseStart_5462691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462691 prefixEnd_5462691 := by exact prefixLift 5462691
  have htrace : WordTrace (prefixWord ++ tailWord_5462691) baseStart_5462691 baseEnd_5462691 := by
    simpa [prefixWord, tailWord_5462691, baseEnd_5462691] using wordTrace_append hprefix tailTrace_5462691
  have hstable : (prefixWord ++ tailWord_5462691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462691).length < 2 ^ (prefixWord ++ tailWord_5462691).sum := by decide
  have hdescent : baseEnd_5462691 < baseStart_5462691 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462718 : List Nat := [4, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_5462718 : Nat := 118140960795 + 5462718 * 2 ^ 59
def prefixEnd_5462718 : Nat := 4983230072969 + 3 ^ 40 * 5462718 * 2
def baseEnd_5462718 : Nat := 2805000013967663324402423

theorem tailTrace_5462718 : CollatzResearch.WordTrace tailWord_5462718 prefixEnd_5462718 2805000013967663324402423 := by
  unfold tailWord_5462718
  simp only [CollatzResearch.WordTrace]
  refine ⟨24905211727939139850366601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132827795882342079201955205 24905211727939139850366601)
  ·
    refine ⟨18678908795954354887774951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24905211727939139850366601 18678908795954354887774951)
    ·
      refine ⟨28018363193931532331662427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18678908795954354887774951 28018363193931532331662427)
      ·
        refine ⟨42027544790897298497493641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28018363193931532331662427 42027544790897298497493641)
        ·
          refine ⟨31520658593172973873120231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42027544790897298497493641 31520658593172973873120231)
          ·
            refine ⟨47280987889759460809680347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31520658593172973873120231 47280987889759460809680347)
            ·
              refine ⟨70921481834639191214520521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47280987889759460809680347 70921481834639191214520521)
              ·
                refine ⟨53191111375979393410890391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70921481834639191214520521 53191111375979393410890391)
                ·
                  refine ⟨79786667063969090116335587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53191111375979393410890391 79786667063969090116335587)
                  ·
                    refine ⟨119680000595953635174503381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79786667063969090116335587 119680000595953635174503381)
                    ·
                      refine ⟨2805000013967663324402423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119680000595953635174503381 2805000013967663324402423)
                      ·
                        rfl

theorem cell23_5462718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_5462718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462718 prefixEnd_5462718 := by exact prefixLift 5462718
  have htrace : WordTrace (prefixWord ++ tailWord_5462718) baseStart_5462718 baseEnd_5462718 := by
    simpa [prefixWord, tailWord_5462718, baseEnd_5462718] using wordTrace_append hprefix tailTrace_5462718
  have hstable : (prefixWord ++ tailWord_5462718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462718).length < 2 ^ (prefixWord ++ tailWord_5462718).sum := by decide
  have hdescent : baseEnd_5462718 < baseStart_5462718 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462731 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 9]
def baseStart_5462731 : Nat := 118140960795 + 5462731 * 2 ^ 59
def prefixEnd_5462731 : Nat := 4983230072969 + 3 ^ 40 * 5462731 * 2
def baseEnd_5462731 : Nat := 2805006689216171773539863

theorem tailTrace_5462731 : CollatzResearch.WordTrace tailWord_5462731 prefixEnd_5462731 2805006689216171773539863 := by
  unfold tailWord_5462731
  simp only [CollatzResearch.WordTrace]
  refine ⟨199242167972466022023156047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132828111981644014682104031 199242167972466022023156047)
  ·
    refine ⟨298863251958699033034734071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199242167972466022023156047 298863251958699033034734071)
    ·
      refine ⟨448294877938048549552101107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298863251958699033034734071 448294877938048549552101107)
      ·
        refine ⟨672442316907072824328151661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448294877938048549552101107 672442316907072824328151661)
        ·
          refine ⟨252165868840152309123056873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 672442316907072824328151661 252165868840152309123056873)
          ·
            refine ⟨189124401630114231842292655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252165868840152309123056873 189124401630114231842292655)
            ·
              refine ⟨283686602445171347763438983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189124401630114231842292655 283686602445171347763438983)
              ·
                refine ⟨425529903667757021645158475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283686602445171347763438983 425529903667757021645158475)
                ·
                  refine ⟨638294855501635532467737713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 425529903667757021645158475 638294855501635532467737713)
                  ·
                    refine ⟨478721141626226649350803285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 638294855501635532467737713 478721141626226649350803285)
                    ·
                      refine ⟨2805006689216171773539863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 478721141626226649350803285 2805006689216171773539863)
                      ·
                        rfl

theorem cell23_5462731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 9].length) (baseStart_5462731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462731 prefixEnd_5462731 := by exact prefixLift 5462731
  have htrace : WordTrace (prefixWord ++ tailWord_5462731) baseStart_5462731 baseEnd_5462731 := by
    simpa [prefixWord, tailWord_5462731, baseEnd_5462731] using wordTrace_append hprefix tailTrace_5462731
  have hstable : (prefixWord ++ tailWord_5462731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462731).length < 2 ^ (prefixWord ++ tailWord_5462731).sum := by decide
  have hdescent : baseEnd_5462731 < baseStart_5462731 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462745 : List Nat := [1, 2, 1, 2, 3, 2, 2, 2, 2, 4, 2]
def baseStart_5462745 : Nat := 118140960795 + 5462745 * 2 ^ 59
def prefixEnd_5462745 : Nat := 4983230072969 + 3 ^ 40 * 5462745 * 2
def baseEnd_5462745 : Nat := 2805013877945334718764799

theorem tailTrace_5462745 : CollatzResearch.WordTrace tailWord_5462745 prefixEnd_5462745 2805013877945334718764799 := by
  unfold tailWord_5462745
  simp only [CollatzResearch.WordTrace]
  refine ⟨199242678594415302414165689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132828452396276868276110459 199242678594415302414165689)
  ·
    refine ⟨149432008945811476810624267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199242678594415302414165689 149432008945811476810624267)
    ·
      refine ⟨224148013418717215215936401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149432008945811476810624267 224148013418717215215936401)
      ·
        refine ⟨168111010064037911411952301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224148013418717215215936401 168111010064037911411952301)
        ·
          refine ⟨63041628774014216779482113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168111010064037911411952301 63041628774014216779482113)
          ·
            refine ⟨47281221580510662584611585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63041628774014216779482113 47281221580510662584611585)
            ·
              refine ⟨35460916185382996938458689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47281221580510662584611585 35460916185382996938458689)
              ·
                refine ⟨26595687139037247703844017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35460916185382996938458689 26595687139037247703844017)
                ·
                  refine ⟨19946765354277935777883013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26595687139037247703844017 19946765354277935777883013)
                  ·
                    refine ⟨3740018503927112958353065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19946765354277935777883013 3740018503927112958353065)
                    ·
                      refine ⟨2805013877945334718764799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3740018503927112958353065 2805013877945334718764799)
                      ·
                        rfl

theorem cell23_5462745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 2, 2, 2, 4, 2].length) (baseStart_5462745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462745 prefixEnd_5462745 := by exact prefixLift 5462745
  have htrace : WordTrace (prefixWord ++ tailWord_5462745) baseStart_5462745 baseEnd_5462745 := by
    simpa [prefixWord, tailWord_5462745, baseEnd_5462745] using wordTrace_append hprefix tailTrace_5462745
  have hstable : (prefixWord ++ tailWord_5462745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462745).length < 2 ^ (prefixWord ++ tailWord_5462745).sum := by decide
  have hdescent : baseEnd_5462745 < baseStart_5462745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462765 : List Nat := [1, 5, 1, 2, 1, 1, 2, 2, 1, 4, 3]
def baseStart_5462765 : Nat := 118140960795 + 5462765 * 2 ^ 59
def prefixEnd_5462765 : Nat := 4983230072969 + 3 ^ 40 * 5462765 * 2
def baseEnd_5462765 : Nat := 2805024147558424640514707

theorem tailTrace_5462765 : CollatzResearch.WordTrace tailWord_5462765 prefixEnd_5462765 2805024147558424640514707 := by
  unfold tailWord_5462765
  simp only [CollatzResearch.WordTrace]
  refine ⟨199243408054342845829893749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132828938702895230553262499 199243408054342845829893749)
  ·
    refine ⟨18679069505094641796552539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199243408054342845829893749 18679069505094641796552539)
    ·
      refine ⟨28018604257641962694828809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18679069505094641796552539 28018604257641962694828809)
      ·
        refine ⟨21013953193231472021121607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28018604257641962694828809 21013953193231472021121607)
        ·
          refine ⟨31520929789847208031682411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21013953193231472021121607 31520929789847208031682411)
          ·
            refine ⟨47281394684770812047523617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31520929789847208031682411 47281394684770812047523617)
            ·
              refine ⟨35461046013578109035642713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47281394684770812047523617 35461046013578109035642713)
              ·
                refine ⟨26595784510183581776732035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35461046013578109035642713 26595784510183581776732035)
                ·
                  refine ⟨39893676765275372665098053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26595784510183581776732035 39893676765275372665098053)
                  ·
                    refine ⟨7480064393489132374705885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39893676765275372665098053 7480064393489132374705885)
                    ·
                      refine ⟨2805024147558424640514707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7480064393489132374705885 2805024147558424640514707)
                      ·
                        rfl

theorem cell23_5462765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 2, 1, 4, 3].length) (baseStart_5462765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462765 prefixEnd_5462765 := by exact prefixLift 5462765
  have htrace : WordTrace (prefixWord ++ tailWord_5462765) baseStart_5462765 baseEnd_5462765 := by
    simpa [prefixWord, tailWord_5462765, baseEnd_5462765] using wordTrace_append hprefix tailTrace_5462765
  have hstable : (prefixWord ++ tailWord_5462765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462765).length < 2 ^ (prefixWord ++ tailWord_5462765).sum := by decide
  have hdescent : baseEnd_5462765 < baseStart_5462765 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462768 : List Nat := [2, 1, 1, 1, 3, 1, 3, 5, 6]
def baseStart_5462768 : Nat := 118140960795 + 5462768 * 2 ^ 59
def prefixEnd_5462768 : Nat := 4983230072969 + 3 ^ 40 * 5462768 * 2
def baseEnd_5462768 : Nat := 311669520888932014308577

theorem tailTrace_5462768 : CollatzResearch.WordTrace tailWord_5462768 prefixEnd_5462768 311669520888932014308577 := by
  unfold tailWord_5462768
  simp only [CollatzResearch.WordTrace]
  refine ⟨99621758736665988671126479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132829011648887984894835305 99621758736665988671126479)
  ·
    refine ⟨149432638104998983006689719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99621758736665988671126479 149432638104998983006689719)
    ·
      refine ⟨224148957157498474510034579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149432638104998983006689719 224148957157498474510034579)
      ·
        refine ⟨336223435736247711765051869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224148957157498474510034579 336223435736247711765051869)
        ·
          refine ⟨126083788401092891911894451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 336223435736247711765051869 126083788401092891911894451)
          ·
            refine ⟨189125682601639337867841677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126083788401092891911894451 189125682601639337867841677)
            ·
              refine ⟨70922130975614751700440629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189125682601639337867841677 70922130975614751700440629)
              ·
                refine ⟨6648949778963882971916309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70922130975614751700440629 6648949778963882971916309)
                ·
                  refine ⟨311669520888932014308577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6648949778963882971916309 311669520888932014308577)
                  ·
                    rfl

theorem cell23_5462768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 5, 6].length) (baseStart_5462768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462768 prefixEnd_5462768 := by exact prefixLift 5462768
  have htrace : WordTrace (prefixWord ++ tailWord_5462768) baseStart_5462768 baseEnd_5462768 := by
    simpa [prefixWord, tailWord_5462768, baseEnd_5462768] using wordTrace_append hprefix tailTrace_5462768
  have hstable : (prefixWord ++ tailWord_5462768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462768).length < 2 ^ (prefixWord ++ tailWord_5462768).sum := by decide
  have hdescent : baseEnd_5462768 < baseStart_5462768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462782 : List Nat := [4, 2, 2, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_5462782 : Nat := 118140960795 + 5462782 * 2 ^ 59
def prefixEnd_5462782 : Nat := 4983230072969 + 3 ^ 40 * 5462782 * 2
def baseEnd_5462782 : Nat := 2805032876729551074002129

theorem tailTrace_5462782 : CollatzResearch.WordTrace tailWord_5462782 prefixEnd_5462782 2805032876729551074002129 := by
  unfold tailWord_5462782
  simp only [CollatzResearch.WordTrace]
  refine ⟨24905503511910157216657825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132829352063520838488841733 24905503511910157216657825)
  ·
    refine ⟨18679127633932617912493369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24905503511910157216657825 18679127633932617912493369)
    ·
      refine ⟨14009345725449463434370027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18679127633932617912493369 14009345725449463434370027)
      ·
        refine ⟨21014018588174195151555041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14009345725449463434370027 21014018588174195151555041)
        ·
          refine ⟨15760513941130646363666281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21014018588174195151555041 15760513941130646363666281)
          ·
            refine ⟨11820385455847984772749711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15760513941130646363666281 11820385455847984772749711)
            ·
              refine ⟨17730578183771977159124567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11820385455847984772749711 17730578183771977159124567)
              ·
                refine ⟨26595867275657965738686851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17730578183771977159124567 26595867275657965738686851)
                ·
                  refine ⟨39893800913486948608030277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26595867275657965738686851 39893800913486948608030277)
                  ·
                    refine ⟨7480087671278802864005677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39893800913486948608030277 7480087671278802864005677)
                    ·
                      refine ⟨2805032876729551074002129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7480087671278802864005677 2805032876729551074002129)
                      ·
                        rfl

theorem cell23_5462782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_5462782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462782 prefixEnd_5462782 := by exact prefixLift 5462782
  have htrace : WordTrace (prefixWord ++ tailWord_5462782) baseStart_5462782 baseEnd_5462782 := by
    simpa [prefixWord, tailWord_5462782, baseEnd_5462782] using wordTrace_append hprefix tailTrace_5462782
  have hstable : (prefixWord ++ tailWord_5462782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462782).length < 2 ^ (prefixWord ++ tailWord_5462782).sum := by decide
  have hdescent : baseEnd_5462782 < baseStart_5462782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5462795 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 7, 1, 3]
def baseStart_5462795 : Nat := 118140960795 + 5462795 * 2 ^ 59
def prefixEnd_5462795 : Nat := 4983230072969 + 3 ^ 40 * 5462795 * 2
def baseEnd_5462795 : Nat := 2805039551978059523139569

theorem tailTrace_5462795 : CollatzResearch.WordTrace tailWord_5462795 prefixEnd_5462795 2805039551978059523139569 := by
  unfold tailWord_5462795
  simp only [CollatzResearch.WordTrace]
  refine ⟨199244502244234160953485839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132829668162822773968990559 199244502244234160953485839)
  ·
    refine ⟨298866753366351241430228759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199244502244234160953485839 298866753366351241430228759)
    ·
      refine ⟨448300130049526862145343139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298866753366351241430228759 448300130049526862145343139)
      ·
        refine ⟨672450195074290293218014709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448300130049526862145343139 672450195074290293218014709)
        ·
          refine ⟨63042205788214714989188879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 672450195074290293218014709 63042205788214714989188879)
          ·
            refine ⟨94563308682322072483783319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63042205788214714989188879 94563308682322072483783319)
            ·
              refine ⟨141844963023483108725674979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94563308682322072483783319 141844963023483108725674979)
              ·
                refine ⟨212767444535224663088512469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141844963023483108725674979 212767444535224663088512469)
                ·
                  refine ⟨4986736981294328041137011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 212767444535224663088512469 4986736981294328041137011)
                  ·
                    refine ⟨7480105471941492061705517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4986736981294328041137011 7480105471941492061705517)
                    ·
                      refine ⟨2805039551978059523139569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7480105471941492061705517 2805039551978059523139569)
                      ·
                        rfl

theorem cell23_5462795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 1, 3].length) (baseStart_5462795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5462795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5462795 prefixEnd_5462795 := by exact prefixLift 5462795
  have htrace : WordTrace (prefixWord ++ tailWord_5462795) baseStart_5462795 baseEnd_5462795 := by
    simpa [prefixWord, tailWord_5462795, baseEnd_5462795] using wordTrace_append hprefix tailTrace_5462795
  have hstable : (prefixWord ++ tailWord_5462795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5462795).length < 2 ^ (prefixWord ++ tailWord_5462795).sum := by decide
  have hdescent : baseEnd_5462795 < baseStart_5462795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5462795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
