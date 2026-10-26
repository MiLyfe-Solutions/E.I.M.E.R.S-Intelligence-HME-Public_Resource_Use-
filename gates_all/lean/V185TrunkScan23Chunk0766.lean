import V185TrunkScan23Chunk0765

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4530862 : List Nat := [4, 1, 4, 1, 1, 3, 9]
def baseStart_4530862 : Nat := 118140960795 + 4530862 * 2 ^ 59
def prefixEnd_4530862 : Nat := 4983230072969 + 3 ^ 40 * 4530862 * 2
def baseEnd_4530862 : Nat := 28722345496192064386271

theorem tailTrace_4530862 : CollatzResearch.WordTrace tailWord_4530862 prefixEnd_4530862 28722345496192064386271 := by
  unfold tailWord_4530862
  simp only [CollatzResearch.WordTrace]
  refine ⟨20656764163933532308572355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110169408874312172312385893 20656764163933532308572355)
  ·
    refine ⟨30985146245900298462858533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20656764163933532308572355 30985146245900298462858533)
    ·
      refine ⟨5809714921106305961785975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30985146245900298462858533 5809714921106305961785975)
      ·
        refine ⟨8714572381659458942678963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5809714921106305961785975 8714572381659458942678963)
        ·
          refine ⟨13071858572489188414018445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8714572381659458942678963 13071858572489188414018445)
          ·
            refine ⟨4901946964683445655256917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13071858572489188414018445 4901946964683445655256917)
            ·
              refine ⟨28722345496192064386271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4901946964683445655256917 28722345496192064386271)
              ·
                rfl

theorem cell23_4530862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 9].length) (baseStart_4530862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530862 prefixEnd_4530862 := by exact prefixLift 4530862
  have htrace : WordTrace (prefixWord ++ tailWord_4530862) baseStart_4530862 baseEnd_4530862 := by
    simpa [prefixWord, tailWord_4530862, baseEnd_4530862] using wordTrace_append hprefix tailTrace_4530862
  have hstable : (prefixWord ++ tailWord_4530862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530862).length < 2 ^ (prefixWord ++ tailWord_4530862).sum := by decide
  have hdescent : baseEnd_4530862 < baseStart_4530862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530893 : List Nat := [1, 6, 2, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_4530893 : Nat := 118140960795 + 4530893 * 2 ^ 59
def prefixEnd_4530893 : Nat := 4983230072969 + 3 ^ 40 * 4530893 * 2
def baseEnd_4530893 : Nat := 2326525903091846594000309

theorem tailTrace_4530893 : CollatzResearch.WordTrace tailWord_4530893 prefixEnd_4530893 2326525903091846594000309 := by
  unfold tailWord_4530893
  simp only [CollatzResearch.WordTrace]
  refine ⟨165255243974355950762957333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110170162649570633841971555 165255243974355950762957333)
  ·
    refine ⟨7746339561297935192013625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 165255243974355950762957333 7746339561297935192013625)
    ·
      refine ⟨5809754670973451394010219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7746339561297935192013625 5809754670973451394010219)
      ·
        refine ⟨8714632006460177091015329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5809754670973451394010219 8714632006460177091015329)
        ·
          refine ⟨6535974004845132818261497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8714632006460177091015329 6535974004845132818261497)
          ·
            refine ⟨4901980503633849613696123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6535974004845132818261497 4901980503633849613696123)
            ·
              refine ⟨7352970755450774420544185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4901980503633849613696123 7352970755450774420544185)
              ·
                refine ⟨5514728066588080815408139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7352970755450774420544185 5514728066588080815408139)
                ·
                  refine ⟨8272092099882121223112209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5514728066588080815408139 8272092099882121223112209)
                  ·
                    refine ⟨6204069074911590917334157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8272092099882121223112209 6204069074911590917334157)
                    ·
                      refine ⟨2326525903091846594000309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6204069074911590917334157 2326525903091846594000309)
                      ·
                        rfl

theorem cell23_4530893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_4530893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530893 prefixEnd_4530893 := by exact prefixLift 4530893
  have htrace : WordTrace (prefixWord ++ tailWord_4530893) baseStart_4530893 baseEnd_4530893 := by
    simpa [prefixWord, tailWord_4530893, baseEnd_4530893] using wordTrace_append hprefix tailTrace_4530893
  have hstable : (prefixWord ++ tailWord_4530893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530893).length < 2 ^ (prefixWord ++ tailWord_4530893).sum := by decide
  have hdescent : baseEnd_4530893 < baseStart_4530893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530916 : List Nat := [2, 3, 1, 1, 1, 5, 3, 1, 1, 3, 2]
def baseStart_4530916 : Nat := 118140960795 + 4530916 * 2 ^ 59
def prefixEnd_4530916 : Nat := 4983230072969 + 3 ^ 40 * 4530916 * 2
def baseEnd_4530916 : Nat := 2326537713146900004012703

theorem tailTrace_4530916 : CollatzResearch.WordTrace tailWord_4530916 prefixEnd_4530916 2326537713146900004012703 := by
  unfold tailWord_4530916
  simp only [CollatzResearch.WordTrace]
  refine ⟨82628041426636312845522301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110170721902181750460696401 82628041426636312845522301)
  ·
    refine ⟨30985515534988617317070863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82628041426636312845522301 30985515534988617317070863)
    ·
      refine ⟨46478273302482925975606295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30985515534988617317070863 46478273302482925975606295)
      ·
        refine ⟨69717409953724388963409443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46478273302482925975606295 69717409953724388963409443)
        ·
          refine ⟨104576114930586583445114165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69717409953724388963409443 104576114930586583445114165)
          ·
            refine ⟨9804010774742492197979453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104576114930586583445114165 9804010774742492197979453)
            ·
              refine ⟨3676504040528434574242295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9804010774742492197979453 3676504040528434574242295)
              ·
                refine ⟨5514756060792651861363443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3676504040528434574242295 5514756060792651861363443)
                ·
                  refine ⟨8272134091188977792045165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5514756060792651861363443 8272134091188977792045165)
                  ·
                    refine ⟨3102050284195866672016937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8272134091188977792045165 3102050284195866672016937)
                    ·
                      refine ⟨2326537713146900004012703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3102050284195866672016937 2326537713146900004012703)
                      ·
                        rfl

theorem cell23_4530916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_4530916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530916 prefixEnd_4530916 := by exact prefixLift 4530916
  have htrace : WordTrace (prefixWord ++ tailWord_4530916) baseStart_4530916 baseEnd_4530916 := by
    simpa [prefixWord, tailWord_4530916, baseEnd_4530916] using wordTrace_append hprefix tailTrace_4530916
  have hstable : (prefixWord ++ tailWord_4530916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530916).length < 2 ^ (prefixWord ++ tailWord_4530916).sum := by decide
  have hdescent : baseEnd_4530916 < baseStart_4530916 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530942 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 1, 4, 4]
def baseStart_4530942 : Nat := 118140960795 + 4530942 * 2 ^ 59
def prefixEnd_4530942 : Nat := 4983230072969 + 3 ^ 40 * 4530942 * 2
def baseEnd_4530942 : Nat := 2326551063643916902287583

theorem tailTrace_4530942 : CollatzResearch.WordTrace tailWord_4530942 prefixEnd_4530942 2326551063643916902287583 := by
  unfold tailWord_4530942
  simp only [CollatzResearch.WordTrace]
  refine ⟨20657128893897304016436385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110171354100785621420994053 20657128893897304016436385)
  ·
    refine ⟨15492846670422978012327289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20657128893897304016436385 15492846670422978012327289)
    ·
      refine ⟨11619635002817233509245467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15492846670422978012327289 11619635002817233509245467)
      ·
        refine ⟨17429452504225850263868201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11619635002817233509245467 17429452504225850263868201)
        ·
          refine ⟨13072089378169387697901151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17429452504225850263868201 13072089378169387697901151)
          ·
            refine ⟨19608134067254081546851727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13072089378169387697901151 19608134067254081546851727)
            ·
              refine ⟨29412201100881122320277591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19608134067254081546851727 29412201100881122320277591)
              ·
                refine ⟨44118301651321683480416387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29412201100881122320277591 44118301651321683480416387)
                ·
                  refine ⟨66177452476982525220624581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44118301651321683480416387 66177452476982525220624581)
                  ·
                    refine ⟨12408272339434223478867109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66177452476982525220624581 12408272339434223478867109)
                    ·
                      refine ⟨2326551063643916902287583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12408272339434223478867109 2326551063643916902287583)
                      ·
                        rfl

theorem cell23_4530942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_4530942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530942 prefixEnd_4530942 := by exact prefixLift 4530942
  have htrace : WordTrace (prefixWord ++ tailWord_4530942) baseStart_4530942 baseEnd_4530942 := by
    simpa [prefixWord, tailWord_4530942, baseEnd_4530942] using wordTrace_append hprefix tailTrace_4530942
  have hstable : (prefixWord ++ tailWord_4530942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530942).length < 2 ^ (prefixWord ++ tailWord_4530942).sum := by decide
  have hdescent : baseEnd_4530942 < baseStart_4530942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530946 : List Nat := [3, 4, 1, 1, 1, 3, 2, 1, 1, 4, 2]
def baseStart_4530946 : Nat := 118140960795 + 4530946 * 2 ^ 59
def prefixEnd_4530946 : Nat := 4983230072969 + 3 ^ 40 * 4530946 * 2
def baseEnd_4530946 : Nat := 2326553117566534886637565

theorem tailTrace_4530946 : CollatzResearch.WordTrace tailWord_4530946 prefixEnd_4530946 2326553117566534886637565 := by
  unfold tailWord_4530946
  simp only [CollatzResearch.WordTrace]
  refine ⟨41314294260790985203659173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110171451362109293876424461 41314294260790985203659173)
  ·
    refine ⟨7746430173898309725686095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41314294260790985203659173 7746430173898309725686095)
    ·
      refine ⟨11619645260847464588529143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7746430173898309725686095 11619645260847464588529143)
      ·
        refine ⟨17429467891271196882793715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11619645260847464588529143 17429467891271196882793715)
        ·
          refine ⟨26144201836906795324190573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17429467891271196882793715 26144201836906795324190573)
          ·
            refine ⟨9804075688840048246571465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26144201836906795324190573 9804075688840048246571465)
            ·
              refine ⟨7353056766630036184928599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9804075688840048246571465 7353056766630036184928599)
              ·
                refine ⟨11029585149945054277392899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7353056766630036184928599 11029585149945054277392899)
                ·
                  refine ⟨16544377724917581416089349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11029585149945054277392899 16544377724917581416089349)
                  ·
                    refine ⟨3102070823422046515516753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16544377724917581416089349 3102070823422046515516753)
                    ·
                      refine ⟨2326553117566534886637565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3102070823422046515516753 2326553117566534886637565)
                      ·
                        rfl

theorem cell23_4530946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 2, 1, 1, 4, 2].length) (baseStart_4530946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530946 prefixEnd_4530946 := by exact prefixLift 4530946
  have htrace : WordTrace (prefixWord ++ tailWord_4530946) baseStart_4530946 baseEnd_4530946 := by
    simpa [prefixWord, tailWord_4530946, baseEnd_4530946] using wordTrace_append hprefix tailTrace_4530946
  have hstable : (prefixWord ++ tailWord_4530946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530946).length < 2 ^ (prefixWord ++ tailWord_4530946).sum := by decide
  have hdescent : baseEnd_4530946 < baseStart_4530946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530965 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 1, 7]
def baseStart_4530965 : Nat := 118140960795 + 4530965 * 2 ^ 59
def prefixEnd_4530965 : Nat := 4983230072969 + 3 ^ 40 * 4530965 * 2
def baseEnd_4530965 : Nat := 775520957899656770766659

theorem tailTrace_4530965 : CollatzResearch.WordTrace tailWord_4530965 prefixEnd_4530965 775520957899656770766659 := by
  unfold tailWord_4530965
  simp only [CollatzResearch.WordTrace]
  refine ⟨165257870030095107059578349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110171913353396738039718899 165257870030095107059578349)
  ·
    refine ⟨61971701261285665147341881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165257870030095107059578349 61971701261285665147341881)
    ·
      refine ⟨46478775945964248860506411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61971701261285665147341881 46478775945964248860506411)
      ·
        refine ⟨69718163918946373290759617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46478775945964248860506411 69718163918946373290759617)
        ·
          refine ⟨52288622939209779968069713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69718163918946373290759617 52288622939209779968069713)
          ·
            refine ⟨39216467204407334976052285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52288622939209779968069713 39216467204407334976052285)
            ·
              refine ⟨14706175201652750616019607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39216467204407334976052285 14706175201652750616019607)
              ·
                refine ⟨22059262802479125924029411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14706175201652750616019607 22059262802479125924029411)
                ·
                  refine ⟨33088894203718688886044117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22059262802479125924029411 33088894203718688886044117)
                  ·
                    refine ⟨775520957899656770766659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33088894203718688886044117 775520957899656770766659)
                    ·
                      rfl

theorem cell23_4530965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_4530965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530965 prefixEnd_4530965 := by exact prefixLift 4530965
  have htrace : WordTrace (prefixWord ++ tailWord_4530965) baseStart_4530965 baseEnd_4530965 := by
    simpa [prefixWord, tailWord_4530965, baseEnd_4530965] using wordTrace_append hprefix tailTrace_4530965
  have hstable : (prefixWord ++ tailWord_4530965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530965).length < 2 ^ (prefixWord ++ tailWord_4530965).sum := by decide
  have hdescent : baseEnd_4530965 < baseStart_4530965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4530980 : List Nat := [2, 3, 1, 3, 4, 1, 1, 2, 2, 2, 2]
def baseStart_4530980 : Nat := 118140960795 + 4530980 * 2 ^ 59
def prefixEnd_4530980 : Nat := 4983230072969 + 3 ^ 40 * 4530980 * 2
def baseEnd_4530980 : Nat := 2326570575908787753612409

theorem tailTrace_4530980 : CollatzResearch.WordTrace tailWord_4530980 prefixEnd_4530980 2326570575908787753612409 := by
  unfold tailWord_4530980
  simp only [CollatzResearch.WordTrace]
  refine ⟨82629208562520382310687197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110172278083360509747582929 82629208562520382310687197)
  ·
    refine ⟨30985953210945143366507699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82629208562520382310687197 30985953210945143366507699)
    ·
      refine ⟨46478929816417715049761549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30985953210945143366507699 46478929816417715049761549)
      ·
        refine ⟨17429598681156643143660581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46478929816417715049761549 17429598681156643143660581)
        ·
          refine ⟨3268049752716870589436359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17429598681156643143660581 3268049752716870589436359)
          ·
            refine ⟨4902074629075305884154539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3268049752716870589436359 4902074629075305884154539)
            ·
              refine ⟨7353111943612958826231809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4902074629075305884154539 7353111943612958826231809)
              ·
                refine ⟨5514833957709719119673857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7353111943612958826231809 5514833957709719119673857)
                ·
                  refine ⟨4136125468282289339755393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5514833957709719119673857 4136125468282289339755393)
                  ·
                    refine ⟨3102094101211717004816545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4136125468282289339755393 3102094101211717004816545)
                    ·
                      refine ⟨2326570575908787753612409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3102094101211717004816545 2326570575908787753612409)
                      ·
                        rfl

theorem cell23_4530980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_4530980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4530980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4530980 prefixEnd_4530980 := by exact prefixLift 4530980
  have htrace : WordTrace (prefixWord ++ tailWord_4530980) baseStart_4530980 baseEnd_4530980 := by
    simpa [prefixWord, tailWord_4530980, baseEnd_4530980] using wordTrace_append hprefix tailTrace_4530980
  have hstable : (prefixWord ++ tailWord_4530980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4530980).length < 2 ^ (prefixWord ++ tailWord_4530980).sum := by decide
  have hdescent : baseEnd_4530980 < baseStart_4530980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4530980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531015 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_4531015 : Nat := 118140960795 + 4531015 * 2 ^ 59
def prefixEnd_4531015 : Nat := 4983230072969 + 3 ^ 40 * 4531015 * 2
def baseEnd_4531015 : Nat := 2326588547731695116674747

theorem tailTrace_4531015 : CollatzResearch.WordTrace tailWord_4531015 prefixEnd_4531015 2326588547731695116674747 := by
  unfold tailWord_4531015
  simp only [CollatzResearch.WordTrace]
  refine ⟨165259693679913965598898499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110173129119942643732598999 165259693679913965598898499)
  ·
    refine ⟨247889540519870948398347749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165259693679913965598898499 247889540519870948398347749)
    ·
      refine ⟨46479288847475802824690203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 247889540519870948398347749 46479288847475802824690203)
      ·
        refine ⟨69718933271213704237035305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46479288847475802824690203 69718933271213704237035305)
        ·
          refine ⟨52289199953410278177776479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69718933271213704237035305 52289199953410278177776479)
          ·
            refine ⟨78433799930115417266664719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52289199953410278177776479 78433799930115417266664719)
            ·
              refine ⟨117650699895173125899997079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78433799930115417266664719 117650699895173125899997079)
              ·
                refine ⟨176476049842759688849995619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117650699895173125899997079 176476049842759688849995619)
                ·
                  refine ⟨264714074764139533274993429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176476049842759688849995619 264714074764139533274993429)
                  ·
                    refine ⟨12408472254569040622265317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 264714074764139533274993429 12408472254569040622265317)
                    ·
                      refine ⟨2326588547731695116674747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12408472254569040622265317 2326588547731695116674747)
                      ·
                        rfl

theorem cell23_4531015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_4531015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531015 prefixEnd_4531015 := by exact prefixLift 4531015
  have htrace : WordTrace (prefixWord ++ tailWord_4531015) baseStart_4531015 baseEnd_4531015 := by
    simpa [prefixWord, tailWord_4531015, baseEnd_4531015] using wordTrace_append hprefix tailTrace_4531015
  have hstable : (prefixWord ++ tailWord_4531015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531015).length < 2 ^ (prefixWord ++ tailWord_4531015).sum := by decide
  have hdescent : baseEnd_4531015 < baseStart_4531015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531022 : List Nat := [4, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3]
def baseStart_4531022 : Nat := 118140960795 + 4531022 * 2 ^ 59
def prefixEnd_4531022 : Nat := 4983230072969 + 3 ^ 40 * 4531022 * 2
def baseEnd_4531022 : Nat := 2326592142096276589287215

theorem tailTrace_4531022 : CollatzResearch.WordTrace tailWord_4531022 prefixEnd_4531022 2326592142096276589287215 := by
  unfold tailWord_4531022
  simp only [CollatzResearch.WordTrace]
  refine ⟨20657493623861075724300415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110173299327259070529602213 20657493623861075724300415)
  ·
    refine ⟨30986240435791613586450623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20657493623861075724300415 30986240435791613586450623)
    ·
      refine ⟨46479360653687420379675935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30986240435791613586450623 46479360653687420379675935)
      ·
        refine ⟨69719040980531130569513903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46479360653687420379675935 69719040980531130569513903)
        ·
          refine ⟨104578561470796695854270855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69719040980531130569513903 104578561470796695854270855)
          ·
            refine ⟨156867842206195043781406283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104578561470796695854270855 156867842206195043781406283)
            ·
              refine ⟨235301763309292565672109425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156867842206195043781406283 235301763309292565672109425)
              ·
                refine ⟨176476322481969424254082069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235301763309292565672109425 176476322481969424254082069)
                ·
                  refine ⟨8272327616342316761910097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 176476322481969424254082069 8272327616342316761910097)
                  ·
                    refine ⟨6204245712256737571432573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8272327616342316761910097 6204245712256737571432573)
                    ·
                      refine ⟨2326592142096276589287215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6204245712256737571432573 2326592142096276589287215)
                      ·
                        rfl

theorem cell23_4531022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 2, 6, 2, 3].length) (baseStart_4531022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531022 prefixEnd_4531022 := by exact prefixLift 4531022
  have htrace : WordTrace (prefixWord ++ tailWord_4531022) baseStart_4531022 baseEnd_4531022 := by
    simpa [prefixWord, tailWord_4531022, baseEnd_4531022] using wordTrace_append hprefix tailTrace_4531022
  have hstable : (prefixWord ++ tailWord_4531022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531022).length < 2 ^ (prefixWord ++ tailWord_4531022).sum := by decide
  have hdescent : baseEnd_4531022 < baseStart_4531022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531045 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_4531045 : Nat := 118140960795 + 4531045 * 2 ^ 59
def prefixEnd_4531045 : Nat := 4983230072969 + 3 ^ 40 * 4531045 * 2
def baseEnd_4531045 : Nat := 2326603952151329999299609

theorem tailTrace_4531045 : CollatzResearch.WordTrace tailWord_4531045 prefixEnd_4531045 2326603952151329999299609 := by
  unfold tailWord_4531045
  simp only [CollatzResearch.WordTrace]
  refine ⟨165260787869805280722490589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110173858579870187148327059 165260787869805280722490589)
  ·
    refine ⟨61972795451176980270933971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165260787869805280722490589 61972795451176980270933971)
    ·
      refine ⟨92959193176765470406400957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61972795451176980270933971 92959193176765470406400957)
      ·
        refine ⟨34859697441287051402400359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92959193176765470406400957 34859697441287051402400359)
        ·
          refine ⟨52289546161930577103600539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34859697441287051402400359 52289546161930577103600539)
          ·
            refine ⟨78434319242895865655400809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52289546161930577103600539 78434319242895865655400809)
            ·
              refine ⟨58825739432171899241550607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78434319242895865655400809 58825739432171899241550607)
              ·
                refine ⟨88238609148257848862325911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58825739432171899241550607 88238609148257848862325911)
                ·
                  refine ⟨132357913722386773293488867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88238609148257848862325911 132357913722386773293488867)
                  ·
                    refine ⟨198536870583580159940233301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 132357913722386773293488867 198536870583580159940233301)
                    ·
                      refine ⟨2326603952151329999299609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 198536870583580159940233301 2326603952151329999299609)
                      ·
                        rfl

theorem cell23_4531045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_4531045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531045 prefixEnd_4531045 := by exact prefixLift 4531045
  have htrace : WordTrace (prefixWord ++ tailWord_4531045) baseStart_4531045 baseEnd_4531045 := by
    simpa [prefixWord, tailWord_4531045, baseEnd_4531045] using wordTrace_append hprefix tailTrace_4531045
  have hstable : (prefixWord ++ tailWord_4531045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531045).length < 2 ^ (prefixWord ++ tailWord_4531045).sum := by decide
  have hdescent : baseEnd_4531045 < baseStart_4531045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531069 : List Nat := [1, 4, 1, 1, 2, 1, 2, 4, 3, 1, 3]
def baseStart_4531069 : Nat := 118140960795 + 4531069 * 2 ^ 59
def prefixEnd_4531069 : Nat := 4983230072969 + 3 ^ 40 * 4531069 * 2
def baseEnd_4531069 : Nat := 2326616275687037905399499

theorem tailTrace_4531069 : CollatzResearch.WordTrace tailWord_4531069 prefixEnd_4531069 2326616275687037905399499 := by
  unfold tailWord_4531069
  simp only [CollatzResearch.WordTrace]
  refine ⟨165261663221718332821364261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110174442147812221880909507 165261663221718332821364261)
  ·
    refine ⟨30986561854072187404005799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165261663221718332821364261 30986561854072187404005799)
    ·
      refine ⟨46479842781108281106008699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30986561854072187404005799 46479842781108281106008699)
      ·
        refine ⟨69719764171662421659013049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46479842781108281106008699 69719764171662421659013049)
        ·
          refine ⟨52289823128746816244259787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69719764171662421659013049 52289823128746816244259787)
          ·
            refine ⟨78434734693120224366389681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52289823128746816244259787 78434734693120224366389681)
            ·
              refine ⟨58826051019840168274792261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78434734693120224366389681 58826051019840168274792261)
              ·
                refine ⟨11029884566220031551523549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58826051019840168274792261 11029884566220031551523549)
                ·
                  refine ⟨4136206712332511831821331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11029884566220031551523549 4136206712332511831821331)
                  ·
                    refine ⟨6204310068498767747731997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4136206712332511831821331 6204310068498767747731997)
                    ·
                      refine ⟨2326616275687037905399499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6204310068498767747731997 2326616275687037905399499)
                      ·
                        rfl

theorem cell23_4531069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_4531069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531069 prefixEnd_4531069 := by exact prefixLift 4531069
  have htrace : WordTrace (prefixWord ++ tailWord_4531069) baseStart_4531069 baseEnd_4531069 := by
    simpa [prefixWord, tailWord_4531069, baseEnd_4531069] using wordTrace_append hprefix tailTrace_4531069
  have hstable : (prefixWord ++ tailWord_4531069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531069).length < 2 ^ (prefixWord ++ tailWord_4531069).sum := by decide
  have hdescent : baseEnd_4531069 < baseStart_4531069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531072 : List Nat := [2, 1, 1, 2, 1, 2, 2, 6, 1, 5]
def baseStart_4531072 : Nat := 118140960795 + 4531072 * 2 ^ 59
def prefixEnd_4531072 : Nat := 4983230072969 + 3 ^ 40 * 4531072 * 2
def baseEnd_4531072 : Nat := 775539272043000464553995

theorem tailTrace_4531072 : CollatzResearch.WordTrace tailWord_4531072 prefixEnd_4531072 775539272043000464553995 := by
  unfold tailWord_4531072
  simp only [CollatzResearch.WordTrace]
  refine ⟨82630886320353732166861735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110174515093804976222482313 82630886320353732166861735)
  ·
    refine ⟨123946329480530598250292603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82630886320353732166861735 123946329480530598250292603)
    ·
      refine ⟨185919494220795897375438905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123946329480530598250292603 185919494220795897375438905)
      ·
        refine ⟨139439620665596923031579179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185919494220795897375438905 139439620665596923031579179)
        ·
          refine ⟨209159430998395384547368769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139439620665596923031579179 209159430998395384547368769)
          ·
            refine ⟨156869573248796538410526577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209159430998395384547368769 156869573248796538410526577)
            ·
              refine ⟨117652179936597403807894933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156869573248796538410526577 117652179936597403807894933)
              ·
                refine ⟨5514945934528003303495075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117652179936597403807894933 5514945934528003303495075)
                ·
                  refine ⟨8272418901792004955242613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5514945934528003303495075 8272418901792004955242613)
                  ·
                    refine ⟨775539272043000464553995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8272418901792004955242613 775539272043000464553995)
                    ·
                      rfl

theorem cell23_4531072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 6, 1, 5].length) (baseStart_4531072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531072 prefixEnd_4531072 := by exact prefixLift 4531072
  have htrace : WordTrace (prefixWord ++ tailWord_4531072) baseStart_4531072 baseEnd_4531072 := by
    simpa [prefixWord, tailWord_4531072, baseEnd_4531072] using wordTrace_append hprefix tailTrace_4531072
  have hstable : (prefixWord ++ tailWord_4531072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531072).length < 2 ^ (prefixWord ++ tailWord_4531072).sum := by decide
  have hdescent : baseEnd_4531072 < baseStart_4531072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531103 : List Nat := [1, 1, 2, 5, 2, 2, 1, 4, 1, 1, 3]
def baseStart_4531103 : Nat := 118140960795 + 4531103 * 2 ^ 59
def prefixEnd_4531103 : Nat := 4983230072969 + 3 ^ 40 * 4531103 * 2
def baseEnd_4531103 : Nat := 2326633734029290772374343

theorem tailTrace_4531103 : CollatzResearch.WordTrace tailWord_4531103 prefixEnd_4531103 2326633734029290772374343 := by
  unfold tailWord_4531103
  simp only [CollatzResearch.WordTrace]
  refine ⟨165262903303595156628101963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110175268869063437752067975 165262903303595156628101963)
  ·
    refine ⟨247894354955392734942152945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165262903303595156628101963 247894354955392734942152945)
    ·
      refine ⟨185920766216544551206614709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247894354955392734942152945 185920766216544551206614709)
      ·
        refine ⟨17430071832801051675620129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 185920766216544551206614709 17430071832801051675620129)
        ·
          refine ⟨13072553874600788756715097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17430071832801051675620129 13072553874600788756715097)
          ·
            refine ⟨9804415405950591567536323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13072553874600788756715097 9804415405950591567536323)
            ·
              refine ⟨14706623108925887351304485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9804415405950591567536323 14706623108925887351304485)
              ·
                refine ⟨2757491832923603878369591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14706623108925887351304485 2757491832923603878369591)
                ·
                  refine ⟨4136237749385405817554387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2757491832923603878369591 4136237749385405817554387)
                  ·
                    refine ⟨6204356624078108726331581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4136237749385405817554387 6204356624078108726331581)
                    ·
                      refine ⟨2326633734029290772374343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6204356624078108726331581 2326633734029290772374343)
                      ·
                        rfl

theorem cell23_4531103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_4531103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531103 prefixEnd_4531103 := by exact prefixLift 4531103
  have htrace : WordTrace (prefixWord ++ tailWord_4531103) baseStart_4531103 baseEnd_4531103 := by
    simpa [prefixWord, tailWord_4531103, baseEnd_4531103] using wordTrace_append hprefix tailTrace_4531103
  have hstable : (prefixWord ++ tailWord_4531103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531103).length < 2 ^ (prefixWord ++ tailWord_4531103).sum := by decide
  have hdescent : baseEnd_4531103 < baseStart_4531103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531129 : List Nat := [1, 2, 1, 4, 2, 2, 2, 1, 3, 2, 3]
def baseStart_4531129 : Nat := 118140960795 + 4531129 * 2 ^ 59
def prefixEnd_4531129 : Nat := 4983230072969 + 3 ^ 40 * 4531129 * 2
def baseEnd_4531129 : Nat := 2326647084526307670649223

theorem tailTrace_4531129 : CollatzResearch.WordTrace tailWord_4531129 prefixEnd_4531129 2326647084526307670649223 := by
  unfold tailWord_4531129
  simp only [CollatzResearch.WordTrace]
  refine ⟨165263851601500963068548441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110175901067667308712365627 165263851601500963068548441)
  ·
    refine ⟨123947888701125722301411331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165263851601500963068548441 123947888701125722301411331)
    ·
      refine ⟨185921833051688583452116997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123947888701125722301411331 185921833051688583452116997)
      ·
        refine ⟨34860343697191609397271937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185921833051688583452116997 34860343697191609397271937)
        ·
          refine ⟨26145257772893707047953953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34860343697191609397271937 26145257772893707047953953)
          ·
            refine ⟨19608943329670280285965465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26145257772893707047953953 19608943329670280285965465)
            ·
              refine ⟨14706707497252710214474099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19608943329670280285965465 14706707497252710214474099)
              ·
                refine ⟨22060061245879065321711149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14706707497252710214474099 22060061245879065321711149)
                ·
                  refine ⟨8272522967204649495641681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22060061245879065321711149 8272522967204649495641681)
                  ·
                    refine ⟨6204392225403487121731261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8272522967204649495641681 6204392225403487121731261)
                    ·
                      refine ⟨2326647084526307670649223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6204392225403487121731261 2326647084526307670649223)
                      ·
                        rfl

theorem cell23_4531129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_4531129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531129 prefixEnd_4531129 := by exact prefixLift 4531129
  have htrace : WordTrace (prefixWord ++ tailWord_4531129) baseStart_4531129 baseEnd_4531129 := by
    simpa [prefixWord, tailWord_4531129, baseEnd_4531129] using wordTrace_append hprefix tailTrace_4531129
  have hstable : (prefixWord ++ tailWord_4531129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531129).length < 2 ^ (prefixWord ++ tailWord_4531129).sum := by decide
  have hdescent : baseEnd_4531129 < baseStart_4531129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531140 : List Nat := [2, 3, 3, 3, 1, 2, 2, 1, 1, 5]
def baseStart_4531140 : Nat := 118140960795 + 4531140 * 2 ^ 59
def prefixEnd_4531140 : Nat := 4983230072969 + 3 ^ 40 * 4531140 * 2
def baseEnd_4531140 : Nat := 775550910937835709203891

theorem tailTrace_4531140 : CollatzResearch.WordTrace tailWord_4531140 prefixEnd_4531140 775550910937835709203891 := by
  unfold tailWord_4531140
  simp only [CollatzResearch.WordTrace]
  refine ⟨82632126402230555973599437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110176168536307407964799249 82632126402230555973599437)
  ·
    refine ⟨30987047400836458490099789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82632126402230555973599437 30987047400836458490099789)
    ·
      refine ⟨11620142775313671933787421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30987047400836458490099789 11620142775313671933787421)
      ·
        refine ⟨4357553540742626975170283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11620142775313671933787421 4357553540742626975170283)
        ·
          refine ⟨6536330311113940462755425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4357553540742626975170283 6536330311113940462755425)
          ·
            refine ⟨4902247733335455347066569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6536330311113940462755425 4902247733335455347066569)
            ·
              refine ⟨3676685800001591510299927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4902247733335455347066569 3676685800001591510299927)
              ·
                refine ⟨5515028700002387265449891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3676685800001591510299927 5515028700002387265449891)
                ·
                  refine ⟨8272543050003580898174837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5515028700002387265449891 8272543050003580898174837)
                  ·
                    refine ⟨775550910937835709203891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8272543050003580898174837 775550910937835709203891)
                    ·
                      rfl

theorem cell23_4531140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_4531140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531140 prefixEnd_4531140 := by exact prefixLift 4531140
  have htrace : WordTrace (prefixWord ++ tailWord_4531140) baseStart_4531140 baseEnd_4531140 := by
    simpa [prefixWord, tailWord_4531140, baseEnd_4531140] using wordTrace_append hprefix tailTrace_4531140
  have hstable : (prefixWord ++ tailWord_4531140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531140).length < 2 ^ (prefixWord ++ tailWord_4531140).sum := by decide
  have hdescent : baseEnd_4531140 < baseStart_4531140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531143 : List Nat := [1, 1, 4, 1, 1, 2, 3, 5, 1, 2, 2]
def baseStart_4531143 : Nat := 118140960795 + 4531143 * 2 ^ 59
def prefixEnd_4531143 : Nat := 4983230072969 + 3 ^ 40 * 4531143 * 2
def baseEnd_4531143 : Nat := 2326654273255470615874159

theorem tailTrace_4531143 : CollatzResearch.WordTrace tailWord_4531143 prefixEnd_4531143 2326654273255470615874159 := by
  unfold tailWord_4531143
  simp only [CollatzResearch.WordTrace]
  refine ⟨165264362223450243459558083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110176241482300162306372055 165264362223450243459558083)
  ·
    refine ⟨247896543335175365189337125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165264362223450243459558083 247896543335175365189337125)
    ·
      refine ⟨46480601875345380973000711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 247896543335175365189337125 46480601875345380973000711)
      ·
        refine ⟨69720902813018071459501067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46480601875345380973000711 69720902813018071459501067)
        ·
          refine ⟨104581354219527107189251601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69720902813018071459501067 104581354219527107189251601)
          ·
            refine ⟨78436015664645330391938701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104581354219527107189251601 78436015664645330391938701)
            ·
              refine ⟨29413505874241998896977013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78436015664645330391938701 29413505874241998896977013)
              ·
                refine ⟨2757516175710187396591595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29413505874241998896977013 2757516175710187396591595)
                ·
                  refine ⟨4136274263565281094887393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2757516175710187396591595 4136274263565281094887393)
                  ·
                    refine ⟨3102205697673960821165545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4136274263565281094887393 3102205697673960821165545)
                    ·
                      refine ⟨2326654273255470615874159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3102205697673960821165545 2326654273255470615874159)
                      ·
                        rfl

theorem cell23_4531143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_4531143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531143 prefixEnd_4531143 := by exact prefixLift 4531143
  have htrace : WordTrace (prefixWord ++ tailWord_4531143) baseStart_4531143 baseEnd_4531143 := by
    simpa [prefixWord, tailWord_4531143, baseEnd_4531143] using wordTrace_append hprefix tailTrace_4531143
  have hstable : (prefixWord ++ tailWord_4531143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531143).length < 2 ^ (prefixWord ++ tailWord_4531143).sum := by decide
  have hdescent : baseEnd_4531143 < baseStart_4531143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531170 : List Nat := [3, 3, 3, 1, 1, 2, 3, 1, 2, 4]
def baseStart_4531170 : Nat := 118140960795 + 4531170 * 2 ^ 59
def prefixEnd_4531170 : Nat := 4983230072969 + 3 ^ 40 * 4531170 * 2
def baseEnd_4531170 : Nat := 775556045744380670078845

theorem tailTrace_4531170 : CollatzResearch.WordTrace tailWord_4531170 prefixEnd_4531170 775556045744380670078845 := by
  unfold tailWord_4531170
  simp only [CollatzResearch.WordTrace]
  refine ⟨41316336748588106767697741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110176897996234951380527309 41316336748588106767697741)
  ·
    refine ⟨15493626280720540037886653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41316336748588106767697741 15493626280720540037886653)
    ·
      refine ⟨5810109855270202514207495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15493626280720540037886653 5810109855270202514207495)
      ·
        refine ⟨8715164782905303771311243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5810109855270202514207495 8715164782905303771311243)
        ·
          refine ⟨13072747174357955656966865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8715164782905303771311243 13072747174357955656966865)
          ·
            refine ⟨9804560380768466742725149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13072747174357955656966865 9804560380768466742725149)
            ·
              refine ⟨3676710142788175028521931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9804560380768466742725149 3676710142788175028521931)
              ·
                refine ⟨5515065214182262542782897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3676710142788175028521931 5515065214182262542782897)
                ·
                  refine ⟨4136298910636696907087173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5515065214182262542782897 4136298910636696907087173)
                  ·
                    refine ⟨775556045744380670078845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4136298910636696907087173 775556045744380670078845)
                    ·
                      rfl

theorem cell23_4531170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_4531170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531170 prefixEnd_4531170 := by exact prefixLift 4531170
  have htrace : WordTrace (prefixWord ++ tailWord_4531170) baseStart_4531170 baseEnd_4531170 := by
    simpa [prefixWord, tailWord_4531170, baseEnd_4531170] using wordTrace_append hprefix tailTrace_4531170
  have hstable : (prefixWord ++ tailWord_4531170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531170).length < 2 ^ (prefixWord ++ tailWord_4531170).sum := by decide
  have hdescent : baseEnd_4531170 < baseStart_4531170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531173 : List Nat := [1, 3, 1, 6, 1, 2, 1, 1, 1, 2, 4]
def baseStart_4531173 : Nat := 118140960795 + 4531173 * 2 ^ 59
def prefixEnd_4531173 : Nat := 4983230072969 + 3 ^ 40 * 4531173 * 2
def baseEnd_4531173 : Nat := 2326669677675105498499021

theorem tailTrace_4531173 : CollatzResearch.WordTrace tailWord_4531173 prefixEnd_4531173 2326669677675105498499021 := by
  unfold tailWord_4531173
  simp only [CollatzResearch.WordTrace]
  refine ⟨165265456413341558583150173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110176970942227705722100115 165265456413341558583150173)
  ·
    refine ⟨61974546155003084468681315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165265456413341558583150173 61974546155003084468681315)
    ·
      refine ⟨92961819232504626703021973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61974546155003084468681315 92961819232504626703021973)
      ·
        refine ⟨4357585276523654376704155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92961819232504626703021973 4357585276523654376704155)
        ·
          refine ⟨6536377914785481565056233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4357585276523654376704155 6536377914785481565056233)
          ·
            refine ⟨4902283436089111173792175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6536377914785481565056233 4902283436089111173792175)
            ·
              refine ⟨7353425154133666760688263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4902283436089111173792175 7353425154133666760688263)
              ·
                refine ⟨11030137731200500141032395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7353425154133666760688263 11030137731200500141032395)
                ·
                  refine ⟨16545206596800750211548593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11030137731200500141032395 16545206596800750211548593)
                  ·
                    refine ⟨12408904947600562658661445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16545206596800750211548593 12408904947600562658661445)
                    ·
                      refine ⟨2326669677675105498499021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12408904947600562658661445 2326669677675105498499021)
                      ·
                        rfl

theorem cell23_4531173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_4531173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531173 prefixEnd_4531173 := by exact prefixLift 4531173
  have htrace : WordTrace (prefixWord ++ tailWord_4531173) baseStart_4531173 baseEnd_4531173 := by
    simpa [prefixWord, tailWord_4531173, baseEnd_4531173] using wordTrace_append hprefix tailTrace_4531173
  have hstable : (prefixWord ++ tailWord_4531173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531173).length < 2 ^ (prefixWord ++ tailWord_4531173).sum := by decide
  have hdescent : baseEnd_4531173 < baseStart_4531173 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531176 : List Nat := [2, 1, 4, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_4531176 : Nat := 118140960795 + 4531176 * 2 ^ 59
def prefixEnd_4531176 : Nat := 4983230072969 + 3 ^ 40 * 4531176 * 2
def baseEnd_4531176 : Nat := 2326671218117068986761507

theorem tailTrace_4531176 : CollatzResearch.WordTrace tailWord_4531176 prefixEnd_4531176 2326671218117068986761507 := by
  unfold tailWord_4531176
  simp only [CollatzResearch.WordTrace]
  refine ⟨82632782916165345047754691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110177043888220460063672921 82632782916165345047754691)
  ·
    refine ⟨123949174374248017571632037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82632782916165345047754691 123949174374248017571632037)
    ·
      refine ⟨23240470195171503294681007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123949174374248017571632037 23240470195171503294681007)
      ·
        refine ⟨34860705292757254942021511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23240470195171503294681007 34860705292757254942021511)
        ·
          refine ⟨52291057939135882413032267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34860705292757254942021511 52291057939135882413032267)
          ·
            refine ⟨78436586908703823619548401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52291057939135882413032267 78436586908703823619548401)
            ·
              refine ⟨58827440181527867714661301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78436586908703823619548401 58827440181527867714661301)
              ·
                refine ⟨5515072517018237598249497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58827440181527867714661301 5515072517018237598249497)
                ·
                  refine ⟨4136304387763678198687123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5515072517018237598249497 4136304387763678198687123)
                  ·
                    refine ⟨6204456581645517298030685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4136304387763678198687123 6204456581645517298030685)
                    ·
                      refine ⟨2326671218117068986761507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6204456581645517298030685 2326671218117068986761507)
                      ·
                        rfl

theorem cell23_4531176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_4531176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531176 prefixEnd_4531176 := by exact prefixLift 4531176
  have htrace : WordTrace (prefixWord ++ tailWord_4531176) baseStart_4531176 baseEnd_4531176 := by
    simpa [prefixWord, tailWord_4531176, baseEnd_4531176] using wordTrace_append hprefix tailTrace_4531176
  have hstable : (prefixWord ++ tailWord_4531176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531176).length < 2 ^ (prefixWord ++ tailWord_4531176).sum := by decide
  have hdescent : baseEnd_4531176 < baseStart_4531176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531188 : List Nat := [2, 6, 2, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_4531188 : Nat := 118140960795 + 4531188 * 2 ^ 59
def prefixEnd_4531188 : Nat := 4983230072969 + 3 ^ 40 * 4531188 * 2
def baseEnd_4531188 : Nat := 2326677379884922939811453

theorem tailTrace_4531188 : CollatzResearch.WordTrace tailWord_4531188 prefixEnd_4531188 2326677379884922939811453 := by
  unfold tailWord_4531188
  simp only [CollatzResearch.WordTrace]
  refine ⟨82633001754143608072473109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110177335672191477429964145 82633001754143608072473109)
  ·
    refine ⟨3873421957225481628397177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 82633001754143608072473109 3873421957225481628397177)
    ·
      refine ⟨2905066467919111221297883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3873421957225481628397177 2905066467919111221297883)
      ·
        refine ⟨4357599701878666831946825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2905066467919111221297883 4357599701878666831946825)
        ·
          refine ⟨3268199776409000123960119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4357599701878666831946825 3268199776409000123960119)
          ·
            refine ⟨4902299664613500185940179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3268199776409000123960119 4902299664613500185940179)
            ·
              refine ⟨7353449496920250278910269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4902299664613500185940179 7353449496920250278910269)
              ·
                refine ⟨2757543561345093854591351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7353449496920250278910269 2757543561345093854591351)
                ·
                  refine ⟨4136315342017640781887027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2757543561345093854591351 4136315342017640781887027)
                  ·
                    refine ⟨6204473013026461172830541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4136315342017640781887027 6204473013026461172830541)
                    ·
                      refine ⟨2326677379884922939811453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6204473013026461172830541 2326677379884922939811453)
                      ·
                        rfl

theorem cell23_4531188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_4531188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531188 prefixEnd_4531188 := by exact prefixLift 4531188
  have htrace : WordTrace (prefixWord ++ tailWord_4531188) baseStart_4531188 baseEnd_4531188 := by
    simpa [prefixWord, tailWord_4531188, baseEnd_4531188] using wordTrace_append hprefix tailTrace_4531188
  have hstable : (prefixWord ++ tailWord_4531188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531188).length < 2 ^ (prefixWord ++ tailWord_4531188).sum := by decide
  have hdescent : baseEnd_4531188 < baseStart_4531188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531259 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 3, 7, 2]
def baseStart_4531259 : Nat := 118140960795 + 4531259 * 2 ^ 59
def prefixEnd_4531259 : Nat := 4983230072969 + 3 ^ 40 * 4531259 * 2
def baseEnd_4531259 : Nat := 2326713837011392162023625

theorem tailTrace_4531259 : CollatzResearch.WordTrace tailWord_4531259 prefixEnd_4531259 2326713837011392162023625 := by
  unfold tailWord_4531259
  simp only [CollatzResearch.WordTrace]
  refine ⟨165268593091029995270780831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110179062060686663513853887 165268593091029995270780831)
  ·
    refine ⟨247902889636544992906171247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165268593091029995270780831 247902889636544992906171247)
    ·
      refine ⟨371854334454817489359256871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247902889636544992906171247 371854334454817489359256871)
      ·
        refine ⟨557781501682226234038885307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371854334454817489359256871 557781501682226234038885307)
        ·
          refine ⟨836672252523339351058327961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557781501682226234038885307 836672252523339351058327961)
          ·
            refine ⟨627504189392504513293745971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 836672252523339351058327961 627504189392504513293745971)
            ·
              refine ⟨941256284088756769940618957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627504189392504513293745971 941256284088756769940618957)
              ·
                refine ⟨352971106533283788727732109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 941256284088756769940618957 352971106533283788727732109)
                ·
                  refine ⟨132364164949981420772899541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 352971106533283788727732109 132364164949981420772899541)
                  ·
                    refine ⟨3102285116015189549364833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 132364164949981420772899541 3102285116015189549364833)
                    ·
                      refine ⟨2326713837011392162023625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3102285116015189549364833 2326713837011392162023625)
                      ·
                        rfl

theorem cell23_4531259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 7, 2].length) (baseStart_4531259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531259 prefixEnd_4531259 := by exact prefixLift 4531259
  have htrace : WordTrace (prefixWord ++ tailWord_4531259) baseStart_4531259 baseEnd_4531259 := by
    simpa [prefixWord, tailWord_4531259, baseEnd_4531259] using wordTrace_append hprefix tailTrace_4531259
  have hstable : (prefixWord ++ tailWord_4531259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531259).length < 2 ^ (prefixWord ++ tailWord_4531259).sum := by decide
  have hdescent : baseEnd_4531259 < baseStart_4531259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531269 : List Nat := [1, 3, 1, 1, 1, 3, 4, 2, 2, 5]
def baseStart_4531269 : Nat := 118140960795 + 4531269 * 2 ^ 59
def prefixEnd_4531269 : Nat := 4983230072969 + 3 ^ 40 * 4531269 * 2
def baseEnd_4531269 : Nat := 775572990605979040966193

theorem tailTrace_4531269 : CollatzResearch.WordTrace tailWord_4531269 prefixEnd_4531269 775572990605979040966193 := by
  unfold tailWord_4531269
  simp only [CollatzResearch.WordTrace]
  refine ⟨165268957820993766978644861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110179305213995844652429907 165268957820993766978644861)
  ·
    refine ⟨61975859182872662616991823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165268957820993766978644861 61975859182872662616991823)
    ·
      refine ⟨92963788774308993925487735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61975859182872662616991823 92963788774308993925487735)
      ·
        refine ⟨139445683161463490888231603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92963788774308993925487735 139445683161463490888231603)
        ·
          refine ⟨209168524742195236332347405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139445683161463490888231603 209168524742195236332347405)
          ·
            refine ⟨78438196778323213624630277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209168524742195236332347405 78438196778323213624630277)
            ·
              refine ⟨14707161895935602554618177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78438196778323213624630277 14707161895935602554618177)
              ·
                refine ⟨11030371421951701915963633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14707161895935602554618177 11030371421951701915963633)
                ·
                  refine ⟨8272778566463776436972725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11030371421951701915963633 8272778566463776436972725)
                  ·
                    refine ⟨775572990605979040966193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8272778566463776436972725 775572990605979040966193)
                    ·
                      rfl

theorem cell23_4531269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_4531269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531269 prefixEnd_4531269 := by exact prefixLift 4531269
  have htrace : WordTrace (prefixWord ++ tailWord_4531269) baseStart_4531269 baseEnd_4531269 := by
    simpa [prefixWord, tailWord_4531269, baseEnd_4531269] using wordTrace_append hprefix tailTrace_4531269
  have hstable : (prefixWord ++ tailWord_4531269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531269).length < 2 ^ (prefixWord ++ tailWord_4531269).sum := by decide
  have hdescent : baseEnd_4531269 < baseStart_4531269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531306 : List Nat := [3, 1, 3, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_4531306 : Nat := 118140960795 + 4531306 * 2 ^ 59
def prefixEnd_4531306 : Nat := 4983230072969 + 3 ^ 40 * 4531306 * 2
def baseEnd_4531306 : Nat := 2326737970602153478135909

theorem tailTrace_4531306 : CollatzResearch.WordTrace tailWord_4531306 prefixEnd_4531306 2326737970602153478135909 := by
  unfold tailWord_4531306
  simp only [CollatzResearch.WordTrace]
  refine ⟨41317576830464930574435443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110180204881239814865161181 41317576830464930574435443)
  ·
    refine ⟨61976365245697395861653165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41317576830464930574435443 61976365245697395861653165)
    ·
      refine ⟨23241136967136523448119937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61976365245697395861653165 23241136967136523448119937)
      ·
        refine ⟨17430852725352392586089953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23241136967136523448119937 17430852725352392586089953)
        ·
          refine ⟨13073139544014294439567465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17430852725352392586089953 13073139544014294439567465)
          ·
            refine ⟨9804854658010720829675599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13073139544014294439567465 9804854658010720829675599)
            ·
              refine ⟨14707281987016081244513399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9804854658010720829675599 14707281987016081244513399)
              ·
                refine ⟨22060922980524121866770099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14707281987016081244513399 22060922980524121866770099)
                ·
                  refine ⟨33091384470786182800155149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22060922980524121866770099 33091384470786182800155149)
                  ·
                    refine ⟨12409269176544818550058181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33091384470786182800155149 12409269176544818550058181)
                    ·
                      refine ⟨2326737970602153478135909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12409269176544818550058181 2326737970602153478135909)
                      ·
                        rfl

theorem cell23_4531306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_4531306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531306 prefixEnd_4531306 := by exact prefixLift 4531306
  have htrace : WordTrace (prefixWord ++ tailWord_4531306) baseStart_4531306 baseEnd_4531306 := by
    simpa [prefixWord, tailWord_4531306, baseEnd_4531306] using wordTrace_append hprefix tailTrace_4531306
  have hstable : (prefixWord ++ tailWord_4531306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531306).length < 2 ^ (prefixWord ++ tailWord_4531306).sum := by decide
  have hdescent : baseEnd_4531306 < baseStart_4531306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531333 : List Nat := [1, 3, 1, 1, 6, 1, 2, 1, 3, 4]
def baseStart_4531333 : Nat := 118140960795 + 4531333 * 2 ^ 59
def prefixEnd_4531333 : Nat := 4983230072969 + 3 ^ 40 * 4531333 * 2
def baseEnd_4531333 : Nat := 775583944859941624166095

theorem tailTrace_4531333 : CollatzResearch.WordTrace tailWord_4531333 prefixEnd_4531333 775583944859941624166095 := by
  unfold tailWord_4531333
  simp only [CollatzResearch.WordTrace]
  refine ⟨165271292092761905908974653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110180861395174603939316435 165271292092761905908974653)
  ·
    refine ⟨61976734534785714715865495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165271292092761905908974653 61976734534785714715865495)
    ·
      refine ⟨92965101802178572073798243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61976734534785714715865495 92965101802178572073798243)
      ·
        refine ⟨139447652703267858110697365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92965101802178572073798243 139447652703267858110697365)
        ·
          refine ⟨6536608720465680848938939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 139447652703267858110697365 6536608720465680848938939)
          ·
            refine ⟨9804913080698521273408409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6536608720465680848938939 9804913080698521273408409)
            ·
              refine ⟨7353684810523890955056307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9804913080698521273408409 7353684810523890955056307)
              ·
                refine ⟨11030527215785836432584461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7353684810523890955056307 11030527215785836432584461)
                ·
                  refine ⟨4136447705919688662219173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11030527215785836432584461 4136447705919688662219173)
                  ·
                    refine ⟨775583944859941624166095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4136447705919688662219173 775583944859941624166095)
                    ·
                      rfl

theorem cell23_4531333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_4531333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531333 prefixEnd_4531333 := by exact prefixLift 4531333
  have htrace : WordTrace (prefixWord ++ tailWord_4531333) baseStart_4531333 baseEnd_4531333 := by
    simpa [prefixWord, tailWord_4531333, baseEnd_4531333] using wordTrace_append hprefix tailTrace_4531333
  have hstable : (prefixWord ++ tailWord_4531333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531333).length < 2 ^ (prefixWord ++ tailWord_4531333).sum := by decide
  have hdescent : baseEnd_4531333 < baseStart_4531333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531367 : List Nat := [1, 1, 6, 2, 1, 3, 1, 3, 1, 4]
def baseStart_4531367 : Nat := 118140960795 + 4531367 * 2 ^ 59
def prefixEnd_4531367 : Nat := 4983230072969 + 3 ^ 40 * 4531367 * 2
def baseEnd_4531367 : Nat := 775589764307359246491043

theorem tailTrace_4531367 : CollatzResearch.WordTrace tailWord_4531367 prefixEnd_4531367 775589764307359246491043 := by
  unfold tailWord_4531367
  simp only [CollatzResearch.WordTrace]
  refine ⟨165272532174638729715712355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110181688116425819810474903 165272532174638729715712355)
  ·
    refine ⟨247908798261958094573568533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165272532174638729715712355 247908798261958094573568533)
    ·
      refine ⟨11620724918529285683136025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 247908798261958094573568533 11620724918529285683136025)
      ·
        refine ⟨8715543688896964262352019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11620724918529285683136025 8715543688896964262352019)
        ·
          refine ⟨13073315533345446393528029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8715543688896964262352019 13073315533345446393528029)
          ·
            refine ⟨4902493325004542397573011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13073315533345446393528029 4902493325004542397573011)
            ·
              refine ⟨7353739987506813596359517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4902493325004542397573011 7353739987506813596359517)
              ·
                refine ⟨2757652495315055098634819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7353739987506813596359517 2757652495315055098634819)
                ·
                  refine ⟨4136478742972582647952229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2757652495315055098634819 4136478742972582647952229)
                  ·
                    refine ⟨775589764307359246491043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4136478742972582647952229 775589764307359246491043)
                    ·
                      rfl

theorem cell23_4531367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_4531367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531367 prefixEnd_4531367 := by exact prefixLift 4531367
  have htrace : WordTrace (prefixWord ++ tailWord_4531367) baseStart_4531367 baseEnd_4531367 := by
    simpa [prefixWord, tailWord_4531367, baseEnd_4531367] using wordTrace_append hprefix tailTrace_4531367
  have hstable : (prefixWord ++ tailWord_4531367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531367).length < 2 ^ (prefixWord ++ tailWord_4531367).sum := by decide
  have hdescent : baseEnd_4531367 < baseStart_4531367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531383 : List Nat := [1, 1, 3, 1, 4, 1, 3, 2, 2, 3, 2]
def baseStart_4531383 : Nat := 118140960795 + 4531383 * 2 ^ 59
def prefixEnd_4531383 : Nat := 4983230072969 + 3 ^ 40 * 4531383 * 2
def baseEnd_4531383 : Nat := 2326777508612549676873055

theorem tailTrace_4531383 : CollatzResearch.WordTrace tailWord_4531383 prefixEnd_4531383 2326777508612549676873055 := by
  unfold tailWord_4531383
  simp only [CollatzResearch.WordTrace]
  refine ⟨165273115742580764448294803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110182077161720509632196535 165273115742580764448294803)
  ·
    refine ⟨247909673613871146672442205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165273115742580764448294803 247909673613871146672442205)
    ·
      refine ⟨92966127605201680002165827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247909673613871146672442205 92966127605201680002165827)
      ·
        refine ⟨139449191407802520003248741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92966127605201680002165827 139449191407802520003248741)
        ·
          refine ⟨26146723388962972500609139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139449191407802520003248741 26146723388962972500609139)
          ·
            refine ⟨39220085083444458750913709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26146723388962972500609139 39220085083444458750913709)
            ·
              refine ⟨14707531906291672031592641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39220085083444458750913709 14707531906291672031592641)
              ·
                refine ⟨11030648929718754023694481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14707531906291672031592641 11030648929718754023694481)
                ·
                  refine ⟨8272986697289065517770861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11030648929718754023694481 8272986697289065517770861)
                  ·
                    refine ⟨3102370011483399569164073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8272986697289065517770861 3102370011483399569164073)
                    ·
                      refine ⟨2326777508612549676873055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3102370011483399569164073 2326777508612549676873055)
                      ·
                        rfl

theorem cell23_4531383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 3, 2, 2, 3, 2].length) (baseStart_4531383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531383 prefixEnd_4531383 := by exact prefixLift 4531383
  have htrace : WordTrace (prefixWord ++ tailWord_4531383) baseStart_4531383 baseEnd_4531383 := by
    simpa [prefixWord, tailWord_4531383, baseEnd_4531383] using wordTrace_append hprefix tailTrace_4531383
  have hstable : (prefixWord ++ tailWord_4531383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531383).length < 2 ^ (prefixWord ++ tailWord_4531383).sum := by decide
  have hdescent : baseEnd_4531383 < baseStart_4531383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531390 : List Nat := [4, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3]
def baseStart_4531390 : Nat := 118140960795 + 4531390 * 2 ^ 59
def prefixEnd_4531390 : Nat := 4983230072969 + 3 ^ 40 * 4531390 * 2
def baseEnd_4531390 : Nat := 2326781102977131149485523

theorem tailTrace_4531390 : CollatzResearch.WordTrace tailWord_4531390 prefixEnd_4531390 2326781102977131149485523 := by
  unfold tailWord_4531390
  simp only [CollatzResearch.WordTrace]
  refine ⟨20659171381694425580474953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110182247369036936429199749 20659171381694425580474953)
  ·
    refine ⟨15494378536270819185356215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20659171381694425580474953 15494378536270819185356215)
    ·
      refine ⟨23241567804406228778034323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15494378536270819185356215 23241567804406228778034323)
      ·
        refine ⟨34862351706609343167051485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23241567804406228778034323 34862351706609343167051485)
        ·
          refine ⟨13073381889978503687644307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34862351706609343167051485 13073381889978503687644307)
          ·
            refine ⟨19610072834967755531466461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13073381889978503687644307 19610072834967755531466461)
            ·
              refine ⟨7353777313112908324299923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19610072834967755531466461 7353777313112908324299923)
              ·
                refine ⟨11030665969669362486449885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7353777313112908324299923 11030665969669362486449885)
                ·
                  refine ⟨4136499738626010932418707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11030665969669362486449885 4136499738626010932418707)
                  ·
                    refine ⟨6204749607939016398628061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4136499738626010932418707 6204749607939016398628061)
                    ·
                      refine ⟨2326781102977131149485523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6204749607939016398628061 2326781102977131149485523)
                      ·
                        rfl

theorem cell23_4531390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_4531390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531390 prefixEnd_4531390 := by exact prefixLift 4531390
  have htrace : WordTrace (prefixWord ++ tailWord_4531390) baseStart_4531390 baseEnd_4531390 := by
    simpa [prefixWord, tailWord_4531390, baseEnd_4531390] using wordTrace_append hprefix tailTrace_4531390
  have hstable : (prefixWord ++ tailWord_4531390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531390).length < 2 ^ (prefixWord ++ tailWord_4531390).sum := by decide
  have hdescent : baseEnd_4531390 < baseStart_4531390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531413 : List Nat := [1, 3, 2, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4531413 : Nat := 118140960795 + 4531413 * 2 ^ 59
def prefixEnd_4531413 : Nat := 4983230072969 + 3 ^ 40 * 4531413 * 2
def baseEnd_4531413 : Nat := 2326792913032184559497917

theorem tailTrace_4531413 : CollatzResearch.WordTrace tailWord_4531413 prefixEnd_4531413 2326792913032184559497917 := by
  unfold tailWord_4531413
  simp only [CollatzResearch.WordTrace]
  refine ⟨165274209932472079571886893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110182806621648053047924595 165274209932472079571886893)
  ·
    refine ⟨61977828724677029839457585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165274209932472079571886893 61977828724677029839457585)
    ·
      refine ⟨46483371543507772379593189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61977828724677029839457585 46483371543507772379593189)
      ·
        refine ⟨8715632164407707321173723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46483371543507772379593189 8715632164407707321173723)
        ·
          refine ⟨13073448246611560981760585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8715632164407707321173723 13073448246611560981760585)
          ·
            refine ⟨9805086184958670736320439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13073448246611560981760585 9805086184958670736320439)
            ·
              refine ⟨14707629277438006104480659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9805086184958670736320439 14707629277438006104480659)
              ·
                refine ⟨22061443916157009156720989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14707629277438006104480659 22061443916157009156720989)
                ·
                  refine ⟨8273041468558878433770371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22061443916157009156720989 8273041468558878433770371)
                  ·
                    refine ⟨12409562202838317650655557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8273041468558878433770371 12409562202838317650655557)
                    ·
                      refine ⟨2326792913032184559497917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12409562202838317650655557 2326792913032184559497917)
                      ·
                        rfl

theorem cell23_4531413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4531413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531413 prefixEnd_4531413 := by exact prefixLift 4531413
  have htrace : WordTrace (prefixWord ++ tailWord_4531413) baseStart_4531413 baseEnd_4531413 := by
    simpa [prefixWord, tailWord_4531413, baseEnd_4531413] using wordTrace_append hprefix tailTrace_4531413
  have hstable : (prefixWord ++ tailWord_4531413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531413).length < 2 ^ (prefixWord ++ tailWord_4531413).sum := by decide
  have hdescent : baseEnd_4531413 < baseStart_4531413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531449 : List Nat := [1, 2, 1, 3, 1, 1, 3, 1, 1, 9]
def baseStart_4531449 : Nat := 118140960795 + 4531449 * 2 ^ 59
def prefixEnd_4531449 : Nat := 4983230072969 + 3 ^ 40 * 4531449 * 2
def baseEnd_4531449 : Nat := 775603799445248806215917

theorem tailTrace_4531449 : CollatzResearch.WordTrace tailWord_4531449 prefixEnd_4531449 775603799445248806215917 := by
  unfold tailWord_4531449
  simp only [CollatzResearch.WordTrace]
  refine ⟨165275522960341657720197401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110183681973561105146798267 165275522960341657720197401)
  ·
    refine ⟨123956642220256243290148051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165275522960341657720197401 123956642220256243290148051)
    ·
      refine ⟨185934963330384364935222077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123956642220256243290148051 185934963330384364935222077)
      ·
        refine ⟨69725611248894136850708279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185934963330384364935222077 69725611248894136850708279)
        ·
          refine ⟨104588416873341205276062419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69725611248894136850708279 104588416873341205276062419)
          ·
            refine ⟨156882625310011807914093629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104588416873341205276062419 156882625310011807914093629)
            ·
              refine ⟨58830984491254427967785111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156882625310011807914093629 58830984491254427967785111)
              ·
                refine ⟨88246476736881641951677667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58830984491254427967785111 88246476736881641951677667)
                ·
                  refine ⟨132369715105322462927516501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88246476736881641951677667 132369715105322462927516501)
                  ·
                    refine ⟨775603799445248806215917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 132369715105322462927516501 775603799445248806215917)
                    ·
                      rfl

theorem cell23_4531449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_4531449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531449 prefixEnd_4531449 := by exact prefixLift 4531449
  have htrace : WordTrace (prefixWord ++ tailWord_4531449) baseStart_4531449 baseEnd_4531449 := by
    simpa [prefixWord, tailWord_4531449, baseEnd_4531449] using wordTrace_append hprefix tailTrace_4531449
  have hstable : (prefixWord ++ tailWord_4531449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531449).length < 2 ^ (prefixWord ++ tailWord_4531449).sum := by decide
  have hdescent : baseEnd_4531449 < baseStart_4531449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531473 : List Nat := [1, 2, 2, 1, 1, 4, 1, 3, 3, 3, 2]
def baseStart_4531473 : Nat := 118140960795 + 4531473 * 2 ^ 59
def prefixEnd_4531473 : Nat := 4983230072969 + 3 ^ 40 * 4531473 * 2
def baseEnd_4531473 : Nat := 2326823721871454324747641

theorem tailTrace_4531473 : CollatzResearch.WordTrace tailWord_4531473 prefixEnd_4531473 2326823721871454324747641 := by
  unfold tailWord_4531473
  simp only [CollatzResearch.WordTrace]
  refine ⟨165276398312254709819071073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110184265541503139879380715 165276398312254709819071073)
  ·
    refine ⟨123957298734191032364303305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165276398312254709819071073 123957298734191032364303305)
    ·
      refine ⟨92967974050643274273227479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123957298734191032364303305 92967974050643274273227479)
      ·
        refine ⟨139451961075964911409841219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92967974050643274273227479 139451961075964911409841219)
        ·
          refine ⟨209177941613947367114761829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139451961075964911409841219 209177941613947367114761829)
          ·
            refine ⟨39220864052615131334017843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 209177941613947367114761829 39220864052615131334017843)
            ·
              refine ⟨58831296078922697001026765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39220864052615131334017843 58831296078922697001026765)
              ·
                refine ⟨22061736029596011375385037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58831296078922697001026765 22061736029596011375385037)
                ·
                  refine ⟨8273151011098504265769389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22061736029596011375385037 8273151011098504265769389)
                  ·
                    refine ⟨3102431629161939099663521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8273151011098504265769389 3102431629161939099663521)
                    ·
                      refine ⟨2326823721871454324747641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3102431629161939099663521 2326823721871454324747641)
                      ·
                        rfl

theorem cell23_4531473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 3, 2].length) (baseStart_4531473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531473 prefixEnd_4531473 := by exact prefixLift 4531473
  have htrace : WordTrace (prefixWord ++ tailWord_4531473) baseStart_4531473 baseEnd_4531473 := by
    simpa [prefixWord, tailWord_4531473, baseEnd_4531473] using wordTrace_append hprefix tailTrace_4531473
  have hstable : (prefixWord ++ tailWord_4531473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531473).length < 2 ^ (prefixWord ++ tailWord_4531473).sum := by decide
  have hdescent : baseEnd_4531473 < baseStart_4531473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531524 : List Nat := [2, 3, 4, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_4531524 : Nat := 118140960795 + 4531524 * 2 ^ 59
def prefixEnd_4531524 : Nat := 4983230072969 + 3 ^ 40 * 4531524 * 2
def baseEnd_4531524 : Nat := 2326849909384833625209907

theorem tailTrace_4531524 : CollatzResearch.WordTrace tailWord_4531524 prefixEnd_4531524 2326849909384833625209907 := by
  unfold tailWord_4531524
  simp only [CollatzResearch.WordTrace]
  refine ⟨82639129217534972764588813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110185505623379963686118417 82639129217534972764588813)
  ·
    refine ⟨30989673456575614786720805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82639129217534972764588813 30989673456575614786720805)
    ·
      refine ⟨5810563773107927772510151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30989673456575614786720805 5810563773107927772510151)
      ·
        refine ⟨8715845659661891658765227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5810563773107927772510151 8715845659661891658765227)
        ·
          refine ⟨13073768489492837488147841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8715845659661891658765227 13073768489492837488147841)
          ·
            refine ⟨9805326367119628116110881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13073768489492837488147841 9805326367119628116110881)
            ·
              refine ⟨7353994775339721087083161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9805326367119628116110881 7353994775339721087083161)
              ·
                refine ⟨5515496081504790815312371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7353994775339721087083161 5515496081504790815312371)
                ·
                  refine ⟨8273244122257186222968557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5515496081504790815312371 8273244122257186222968557)
                  ·
                    refine ⟨3102466545846444833613209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8273244122257186222968557 3102466545846444833613209)
                    ·
                      refine ⟨2326849909384833625209907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3102466545846444833613209 2326849909384833625209907)
                      ·
                        rfl

theorem cell23_4531524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_4531524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531524 prefixEnd_4531524 := by exact prefixLift 4531524
  have htrace : WordTrace (prefixWord ++ tailWord_4531524) baseStart_4531524 baseEnd_4531524 := by
    simpa [prefixWord, tailWord_4531524, baseEnd_4531524] using wordTrace_append hprefix tailTrace_4531524
  have hstable : (prefixWord ++ tailWord_4531524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531524).length < 2 ^ (prefixWord ++ tailWord_4531524).sum := by decide
  have hdescent : baseEnd_4531524 < baseStart_4531524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531560 : List Nat := [2, 1, 4, 2, 3, 2, 1, 1, 7]
def baseStart_4531560 : Nat := 118140960795 + 4531560 * 2 ^ 59
def prefixEnd_4531560 : Nat := 4983230072969 + 3 ^ 40 * 4531560 * 2
def baseEnd_4531560 : Nat := 258540932743155053817749

theorem tailTrace_4531560 : CollatzResearch.WordTrace tailWord_4531560 prefixEnd_4531560 258540932743155053817749 := by
  unfold tailWord_4531560
  simp only [CollatzResearch.WordTrace]
  refine ⟨82639785731469761838744067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110186380975293015784992089 82639785731469761838744067)
  ·
    refine ⟨123959678597204642758116101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82639785731469761838744067 123959678597204642758116101)
    ·
      refine ⟨23242439736975870517146769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123959678597204642758116101 23242439736975870517146769)
      ·
        refine ⟨17431829802731902887860077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23242439736975870517146769 17431829802731902887860077)
        ·
          refine ⟨6536936176024463582947529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17431829802731902887860077 6536936176024463582947529)
          ·
            refine ⟨4902702132018347687210647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6536936176024463582947529 4902702132018347687210647)
            ·
              refine ⟨7354053198027521530815971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4902702132018347687210647 7354053198027521530815971)
              ·
                refine ⟨11031079797041282296223957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7354053198027521530815971 11031079797041282296223957)
                ·
                  refine ⟨258540932743155053817749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11031079797041282296223957 258540932743155053817749)
                  ·
                    rfl

theorem cell23_4531560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 1, 7].length) (baseStart_4531560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531560 prefixEnd_4531560 := by exact prefixLift 4531560
  have htrace : WordTrace (prefixWord ++ tailWord_4531560) baseStart_4531560 baseEnd_4531560 := by
    simpa [prefixWord, tailWord_4531560, baseEnd_4531560] using wordTrace_append hprefix tailTrace_4531560
  have hstable : (prefixWord ++ tailWord_4531560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531560).length < 2 ^ (prefixWord ++ tailWord_4531560).sum := by decide
  have hdescent : baseEnd_4531560 < baseStart_4531560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531610 : List Nat := [3, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2]
def baseStart_4531610 : Nat := 118140960795 + 4531610 * 2 ^ 59
def prefixEnd_4531610 : Nat := 4983230072969 + 3 ^ 40 * 4531610 * 2
def baseEnd_4531610 : Nat := 2326894068721120288734511

theorem tailTrace_4531610 : CollatzResearch.WordTrace tailWord_4531610 prefixEnd_4531610 2326894068721120288734511 := by
  unfold tailWord_4531610
  simp only [CollatzResearch.WordTrace]
  refine ⟨41320348778189595554202071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110187596741838921477872189 41320348778189595554202071)
  ·
    refine ⟨61980523167284393331303107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41320348778189595554202071 61980523167284393331303107)
    ·
      refine ⟨92970784750926589996954661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61980523167284393331303107 92970784750926589996954661)
      ·
        refine ⟨17432022140798735624428999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92970784750926589996954661 17432022140798735624428999)
        ·
          refine ⟨26148033211198103436643499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17432022140798735624428999 26148033211198103436643499)
          ·
            refine ⟨39222049816797155154965249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26148033211198103436643499 39222049816797155154965249)
            ·
              refine ⟨29416537362597866366223937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39222049816797155154965249 29416537362597866366223937)
              ·
                refine ⟨22062403021948399774667953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29416537362597866366223937 22062403021948399774667953)
                ·
                  refine ⟨16546802266461299831000965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22062403021948399774667953 16546802266461299831000965)
                  ·
                    refine ⟨3102525424961493718312681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16546802266461299831000965 3102525424961493718312681)
                    ·
                      refine ⟨2326894068721120288734511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3102525424961493718312681 2326894068721120288734511)
                      ·
                        rfl

theorem cell23_4531610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_4531610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531610 prefixEnd_4531610 := by exact prefixLift 4531610
  have htrace : WordTrace (prefixWord ++ tailWord_4531610) baseStart_4531610 baseEnd_4531610 := by
    simpa [prefixWord, tailWord_4531610, baseEnd_4531610] using wordTrace_append hprefix tailTrace_4531610
  have hstable : (prefixWord ++ tailWord_4531610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531610).length < 2 ^ (prefixWord ++ tailWord_4531610).sum := by decide
  have hdescent : baseEnd_4531610 < baseStart_4531610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531633 : List Nat := [1, 2, 2, 4, 1, 1, 1, 5, 6]
def baseStart_4531633 : Nat := 118140960795 + 4531633 * 2 ^ 59
def prefixEnd_4531633 : Nat := 4983230072969 + 3 ^ 40 * 4531633 * 2
def baseEnd_4531633 : Nat := 258545097641797077638545

theorem tailTrace_4531633 : CollatzResearch.WordTrace tailWord_4531633 prefixEnd_4531633 258545097641797077638545 := by
  unfold tailWord_4531633
  simp only [CollatzResearch.WordTrace]
  refine ⟨165282233991675057144895553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110188155994450038096597035 165282233991675057144895553)
  ·
    refine ⟨123961675493756292858671665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165282233991675057144895553 123961675493756292858671665)
    ·
      refine ⟨92971256620317219644003749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123961675493756292858671665 92971256620317219644003749)
      ·
        refine ⟨17432110616309478683250703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92971256620317219644003749 17432110616309478683250703)
        ·
          refine ⟨26148165924464218024876055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17432110616309478683250703 26148165924464218024876055)
          ·
            refine ⟨39222248886696327037314083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26148165924464218024876055 39222248886696327037314083)
            ·
              refine ⟨58833373330044490555971125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39222248886696327037314083 58833373330044490555971125)
              ·
                refine ⟨5515628749691670989622293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58833373330044490555971125 5515628749691670989622293)
                ·
                  refine ⟨258545097641797077638545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5515628749691670989622293 258545097641797077638545)
                  ·
                    rfl

theorem cell23_4531633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 5, 6].length) (baseStart_4531633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531633 prefixEnd_4531633 := by exact prefixLift 4531633
  have htrace : WordTrace (prefixWord ++ tailWord_4531633) baseStart_4531633 baseEnd_4531633 := by
    simpa [prefixWord, tailWord_4531633, baseEnd_4531633] using wordTrace_append hprefix tailTrace_4531633
  have hstable : (prefixWord ++ tailWord_4531633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531633).length < 2 ^ (prefixWord ++ tailWord_4531633).sum := by decide
  have hdescent : baseEnd_4531633 < baseStart_4531633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531644 : List Nat := [2, 2, 2, 4, 3, 1, 1, 1, 2, 1, 4]
def baseStart_4531644 : Nat := 118140960795 + 4531644 * 2 ^ 59
def prefixEnd_4531644 : Nat := 4983230072969 + 3 ^ 40 * 4531644 * 2
def baseEnd_4531644 : Nat := 2326911527063373155709355

theorem tailTrace_4531644 : CollatzResearch.WordTrace tailWord_4531644 prefixEnd_4531644 2326911527063373155709355 := by
  unfold tailWord_4531644
  simp only [CollatzResearch.WordTrace]
  refine ⟨82641317597317603011772993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110188423463090137349030657 82641317597317603011772993)
  ·
    refine ⟨61980988197988202258829745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82641317597317603011772993 61980988197988202258829745)
    ·
      refine ⟨46485741148491151694122309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61980988197988202258829745 46485741148491151694122309)
      ·
        refine ⟨8716076465342090942647933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46485741148491151694122309 8716076465342090942647933)
        ·
          refine ⟨3268528674503284103492975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8716076465342090942647933 3268528674503284103492975)
          ·
            refine ⟨4902793011754926155239463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3268528674503284103492975 4902793011754926155239463)
            ·
              refine ⟨7354189517632389232859195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4902793011754926155239463 7354189517632389232859195)
              ·
                refine ⟨11031284276448583849288793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7354189517632389232859195 11031284276448583849288793)
                ·
                  refine ⟨8273463207336437886966595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11031284276448583849288793 8273463207336437886966595)
                  ·
                    refine ⟨12410194811004656830449893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8273463207336437886966595 12410194811004656830449893)
                    ·
                      refine ⟨2326911527063373155709355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12410194811004656830449893 2326911527063373155709355)
                      ·
                        rfl

theorem cell23_4531644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_4531644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531644 prefixEnd_4531644 := by exact prefixLift 4531644
  have htrace : WordTrace (prefixWord ++ tailWord_4531644) baseStart_4531644 baseEnd_4531644 := by
    simpa [prefixWord, tailWord_4531644, baseEnd_4531644] using wordTrace_append hprefix tailTrace_4531644
  have hstable : (prefixWord ++ tailWord_4531644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531644).length < 2 ^ (prefixWord ++ tailWord_4531644).sum := by decide
  have hdescent : baseEnd_4531644 < baseStart_4531644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531670 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6]
def baseStart_4531670 : Nat := 118140960795 + 4531670 * 2 ^ 59
def prefixEnd_4531670 : Nat := 4983230072969 + 3 ^ 40 * 4531670 * 2
def baseEnd_4531670 : Nat := 2326924877560390053984235

theorem tailTrace_4531670 : CollatzResearch.WordTrace tailWord_4531670 prefixEnd_4531670 2326924877560390053984235 := by
  unfold tailWord_4531670
  simp only [CollatzResearch.WordTrace]
  refine ⟨10330223968283813278999529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110189055661694008309328309 10330223968283813278999529)
  ·
    refine ⟨7747667976212859959249647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10330223968283813278999529 7747667976212859959249647)
    ·
      refine ⟨11621501964319289938874471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7747667976212859959249647 11621501964319289938874471)
      ·
        refine ⟨17432252946478934908311707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11621501964319289938874471 17432252946478934908311707)
        ·
          refine ⟨26148379419718402362467561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17432252946478934908311707 26148379419718402362467561)
          ·
            refine ⟨19611284564788801771850671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26148379419718402362467561 19611284564788801771850671)
            ·
              refine ⟨29416926847183202657776007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19611284564788801771850671 29416926847183202657776007)
              ·
                refine ⟨44125390270774803986664011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29416926847183202657776007 44125390270774803986664011)
                ·
                  refine ⟨66188085406162205979996017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44125390270774803986664011 66188085406162205979996017)
                  ·
                    refine ⟨49641064054621654484997013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66188085406162205979996017 49641064054621654484997013)
                    ·
                      refine ⟨2326924877560390053984235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49641064054621654484997013 2326924877560390053984235)
                      ·
                        rfl

theorem cell23_4531670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_4531670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531670 prefixEnd_4531670 := by exact prefixLift 4531670
  have htrace : WordTrace (prefixWord ++ tailWord_4531670) baseStart_4531670 baseEnd_4531670 := by
    simpa [prefixWord, tailWord_4531670, baseEnd_4531670] using wordTrace_append hprefix tailTrace_4531670
  have hstable : (prefixWord ++ tailWord_4531670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531670).length < 2 ^ (prefixWord ++ tailWord_4531670).sum := by decide
  have hdescent : baseEnd_4531670 < baseStart_4531670 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531677 : List Nat := [1, 4, 3, 1, 1, 2, 1, 3, 3, 1, 3]
def baseStart_4531677 : Nat := 118140960795 + 4531677 * 2 ^ 59
def prefixEnd_4531677 : Nat := 4983230072969 + 3 ^ 40 * 4531677 * 2
def baseEnd_4531677 : Nat := 2326928471924971526596703

theorem tailTrace_4531677 : CollatzResearch.WordTrace tailWord_4531677 prefixEnd_4531677 2326928471924971526596703 := by
  unfold tailWord_4531677
  simp only [CollatzResearch.WordTrace]
  refine ⟨165283838803515652659497285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110189225869010435106331523 165283838803515652659497285)
  ·
    refine ⟨30990719775659184873655741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165283838803515652659497285 30990719775659184873655741)
    ·
      refine ⟨11621519915872194327620903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30990719775659184873655741 11621519915872194327620903)
      ·
        refine ⟨17432279873808291491431355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11621519915872194327620903 17432279873808291491431355)
        ·
          refine ⟨26148419810712437237147033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17432279873808291491431355 26148419810712437237147033)
          ·
            refine ⟨19611314858034327927860275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26148419810712437237147033 19611314858034327927860275)
            ·
              refine ⟨29416972287051491891790413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19611314858034327927860275 29416972287051491891790413)
              ·
                refine ⟨11031364607644309459421405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29416972287051491891790413 11031364607644309459421405)
                ·
                  refine ⟨4136761727866616047283027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11031364607644309459421405 4136761727866616047283027)
                  ·
                    refine ⟨6205142591799924070924541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4136761727866616047283027 6205142591799924070924541)
                    ·
                      refine ⟨2326928471924971526596703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6205142591799924070924541 2326928471924971526596703)
                      ·
                        rfl

theorem cell23_4531677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_4531677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531677 prefixEnd_4531677 := by exact prefixLift 4531677
  have htrace : WordTrace (prefixWord ++ tailWord_4531677) baseStart_4531677 baseEnd_4531677 := by
    simpa [prefixWord, tailWord_4531677, baseEnd_4531677] using wordTrace_append hprefix tailTrace_4531677
  have hstable : (prefixWord ++ tailWord_4531677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531677).length < 2 ^ (prefixWord ++ tailWord_4531677).sum := by decide
  have hdescent : baseEnd_4531677 < baseStart_4531677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531744 : List Nat := [2, 1, 1, 6, 1, 1, 4, 1, 2, 4]
def baseStart_4531744 : Nat := 118140960795 + 4531744 * 2 ^ 59
def prefixEnd_4531744 : Nat := 4983230072969 + 3 ^ 40 * 4531744 * 2
def baseEnd_4531744 : Nat := 775654291709607588152965

theorem tailTrace_4531744 : CollatzResearch.WordTrace tailWord_4531744 prefixEnd_4531744 775654291709607588152965 := by
  unfold tailWord_4531744
  simp only [CollatzResearch.WordTrace]
  refine ⟨82643141247136461551093143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110190854996181948734790857 82643141247136461551093143)
  ·
    refine ⟨123964711870704692326639715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82643141247136461551093143 123964711870704692326639715)
    ·
      refine ⟨185947067806057038489959573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123964711870704692326639715 185947067806057038489959573)
      ·
        refine ⟨8716268803408923679216855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 185947067806057038489959573 8716268803408923679216855)
        ·
          refine ⟨13074403205113385518825283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8716268803408923679216855 13074403205113385518825283)
          ·
            refine ⟨19611604807670078278237925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13074403205113385518825283 19611604807670078278237925)
            ·
              refine ⟨3677175901438139677169611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19611604807670078278237925 3677175901438139677169611)
              ·
                refine ⟨5515763852157209515754417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3677175901438139677169611 5515763852157209515754417)
                ·
                  refine ⟨4136822889117907136815813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5515763852157209515754417 4136822889117907136815813)
                  ·
                    refine ⟨775654291709607588152965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4136822889117907136815813 775654291709607588152965)
                    ·
                      rfl

theorem cell23_4531744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 4, 1, 2, 4].length) (baseStart_4531744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531744 prefixEnd_4531744 := by exact prefixLift 4531744
  have htrace : WordTrace (prefixWord ++ tailWord_4531744) baseStart_4531744 baseEnd_4531744 := by
    simpa [prefixWord, tailWord_4531744, baseEnd_4531744] using wordTrace_append hprefix tailTrace_4531744
  have hstable : (prefixWord ++ tailWord_4531744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531744).length < 2 ^ (prefixWord ++ tailWord_4531744).sum := by decide
  have hdescent : baseEnd_4531744 < baseStart_4531744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531807 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 8, 2, 2]
def baseStart_4531807 : Nat := 118140960795 + 4531807 * 2 ^ 59
def prefixEnd_4531807 : Nat := 4983230072969 + 3 ^ 40 * 4531807 * 2
def baseEnd_4531807 : Nat := 2326995224410056017971105

theorem tailTrace_4531807 : CollatzResearch.WordTrace tailWord_4531807 prefixEnd_4531807 2326995224410056017971105 := by
  unfold tailWord_4531807
  simp only [CollatzResearch.WordTrace]
  refine ⟨165288580293044684861729675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110192386862029789907819783 165288580293044684861729675)
  ·
    refine ⟨247932870439567027292594513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165288580293044684861729675 247932870439567027292594513)
    ·
      refine ⟨185949652829675270469445885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247932870439567027292594513 185949652829675270469445885)
      ·
        refine ⟨69731119811128226426042207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185949652829675270469445885 69731119811128226426042207)
        ·
          refine ⟨104596679716692339639063311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69731119811128226426042207 104596679716692339639063311)
          ·
            refine ⟨156895019575038509458594967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104596679716692339639063311 156895019575038509458594967)
            ·
              refine ⟨235342529362557764187892451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156895019575038509458594967 235342529362557764187892451)
              ·
                refine ⟨353013794043836646281838677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235342529362557764187892451 353013794043836646281838677)
                ·
                  refine ⟨4136880398951210698615297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 353013794043836646281838677 4136880398951210698615297)
                  ·
                    refine ⟨3102660299213408023961473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4136880398951210698615297 3102660299213408023961473)
                    ·
                      refine ⟨2326995224410056017971105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3102660299213408023961473 2326995224410056017971105)
                      ·
                        rfl

theorem cell23_4531807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_4531807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531807 prefixEnd_4531807 := by exact prefixLift 4531807
  have htrace : WordTrace (prefixWord ++ tailWord_4531807) baseStart_4531807 baseEnd_4531807 := by
    simpa [prefixWord, tailWord_4531807, baseEnd_4531807] using wordTrace_append hprefix tailTrace_4531807
  have hstable : (prefixWord ++ tailWord_4531807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531807).length < 2 ^ (prefixWord ++ tailWord_4531807).sum := by decide
  have hdescent : baseEnd_4531807 < baseStart_4531807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531823 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 7]
def baseStart_4531823 : Nat := 118140960795 + 4531823 * 2 ^ 59
def prefixEnd_4531823 : Nat := 4983230072969 + 3 ^ 40 * 4531823 * 2
def baseEnd_4531823 : Nat := 2327003440100527955371031

theorem tailTrace_4531823 : CollatzResearch.WordTrace tailWord_4531823 prefixEnd_4531823 2327003440100527955371031 := by
  unfold tailWord_4531823
  simp only [CollatzResearch.WordTrace]
  refine ⟨165289163860986719594312123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110192775907324479729541415 165289163860986719594312123)
  ·
    refine ⟨247933745791480079391468185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165289163860986719594312123 247933745791480079391468185)
    ·
      refine ⟨185950309343610059543601139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247933745791480079391468185 185950309343610059543601139)
      ·
        refine ⟨278925464015415089315401709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185950309343610059543601139 278925464015415089315401709)
        ·
          refine ⟨104597049005780658493275641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278925464015415089315401709 104597049005780658493275641)
          ·
            refine ⟨78447786754335493869956731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104597049005780658493275641 78447786754335493869956731)
            ·
              refine ⟨117671680131503240804935097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78447786754335493869956731 117671680131503240804935097)
              ·
                refine ⟨88253760098627430603701323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117671680131503240804935097 88253760098627430603701323)
                ·
                  refine ⟨132380640147941145905551985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88253760098627430603701323 132380640147941145905551985)
                  ·
                    refine ⟨99285480110955859429163989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 132380640147941145905551985 99285480110955859429163989)
                    ·
                      refine ⟨2327003440100527955371031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99285480110955859429163989 2327003440100527955371031)
                      ·
                        rfl

theorem cell23_4531823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 2, 7].length) (baseStart_4531823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531823 prefixEnd_4531823 := by exact prefixLift 4531823
  have htrace : WordTrace (prefixWord ++ tailWord_4531823) baseStart_4531823 baseEnd_4531823 := by
    simpa [prefixWord, tailWord_4531823, baseEnd_4531823] using wordTrace_append hprefix tailTrace_4531823
  have hstable : (prefixWord ++ tailWord_4531823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531823).length < 2 ^ (prefixWord ++ tailWord_4531823).sum := by decide
  have hdescent : baseEnd_4531823 < baseStart_4531823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531840 : List Nat := [2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 3]
def baseStart_4531840 : Nat := 118140960795 + 4531840 * 2 ^ 59
def prefixEnd_4531840 : Nat := 4983230072969 + 3 ^ 40 * 4531840 * 2
def baseEnd_4531840 : Nat := 2327012169271654388858453

theorem tailTrace_4531840 : CollatzResearch.WordTrace tailWord_4531840 prefixEnd_4531840 2327012169271654388858453 := by
  unfold tailWord_4531840
  simp only [CollatzResearch.WordTrace]
  refine ⟨82644891950962565748840487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110193189267950087665120649 82644891950962565748840487)
  ·
    refine ⟨123967337926443848623260731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82644891950962565748840487 123967337926443848623260731)
    ·
      refine ⟨185951006889665772934891097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123967337926443848623260731 185951006889665772934891097)
      ·
        refine ⟨139463255167249329701168323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185951006889665772934891097 139463255167249329701168323)
        ·
          refine ⟨209194882750873994551752485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139463255167249329701168323 209194882750873994551752485)
          ·
            refine ⟨39224040515788873978453591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 209194882750873994551752485 39224040515788873978453591)
            ·
              refine ⟨58836060773683310967680387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39224040515788873978453591 58836060773683310967680387)
              ·
                refine ⟨88254091160524966451520581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58836060773683310967680387 88254091160524966451520581)
                ·
                  refine ⟨16547642092598431209660109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88254091160524966451520581 16547642092598431209660109)
                  ·
                    refine ⟨6205365784724411703622541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16547642092598431209660109 6205365784724411703622541)
                    ·
                      refine ⟨2327012169271654388858453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6205365784724411703622541 2327012169271654388858453)
                      ·
                        rfl

theorem cell23_4531840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 3].length) (baseStart_4531840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531840 prefixEnd_4531840 := by exact prefixLift 4531840
  have htrace : WordTrace (prefixWord ++ tailWord_4531840) baseStart_4531840 baseEnd_4531840 := by
    simpa [prefixWord, tailWord_4531840, baseEnd_4531840] using wordTrace_append hprefix tailTrace_4531840
  have hstable : (prefixWord ++ tailWord_4531840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531840).length < 2 ^ (prefixWord ++ tailWord_4531840).sum := by decide
  have hdescent : baseEnd_4531840 < baseStart_4531840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531841 : List Nat := [1, 2, 4, 2, 1, 2, 3, 2, 2, 2, 2]
def baseStart_4531841 : Nat := 118140960795 + 4531841 * 2 ^ 59
def prefixEnd_4531841 : Nat := 4983230072969 + 3 ^ 40 * 4531841 * 2
def baseEnd_4531841 : Nat := 2327012682752308884945949

theorem tailTrace_4531841 : CollatzResearch.WordTrace tailWord_4531841 prefixEnd_4531841 2327012682752308884945949 := by
  unfold tailWord_4531841
  simp only [CollatzResearch.WordTrace]
  refine ⟨165289820374921508668467377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110193213583281005778978251 165289820374921508668467377)
  ·
    refine ⟨123967365281191131501350533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165289820374921508668467377 123967365281191131501350533)
    ·
      refine ⟨23243880990223337156503225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123967365281191131501350533 23243880990223337156503225)
      ·
        refine ⟨17432910742667502867377419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23243880990223337156503225 17432910742667502867377419)
        ·
          refine ⟨26149366114001254301066129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17432910742667502867377419 26149366114001254301066129)
          ·
            refine ⟨19612024585500940725799597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26149366114001254301066129 19612024585500940725799597)
            ·
              refine ⟨7354509219562852772174849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19612024585500940725799597 7354509219562852772174849)
              ·
                refine ⟨5515881914672139579131137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7354509219562852772174849 5515881914672139579131137)
                ·
                  refine ⟨4136911436004104684348353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5515881914672139579131137 4136911436004104684348353)
                  ·
                    refine ⟨3102683577003078513261265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4136911436004104684348353 3102683577003078513261265)
                    ·
                      refine ⟨2327012682752308884945949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3102683577003078513261265 2327012682752308884945949)
                      ·
                        rfl

theorem cell23_4531841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_4531841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531841 prefixEnd_4531841 := by exact prefixLift 4531841
  have htrace : WordTrace (prefixWord ++ tailWord_4531841) baseStart_4531841 baseEnd_4531841 := by
    simpa [prefixWord, tailWord_4531841, baseEnd_4531841] using wordTrace_append hprefix tailTrace_4531841
  have hstable : (prefixWord ++ tailWord_4531841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531841).length < 2 ^ (prefixWord ++ tailWord_4531841).sum := by decide
  have hdescent : baseEnd_4531841 < baseStart_4531841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531847 : List Nat := [1, 1, 4, 2, 1, 3, 2, 4, 5]
def baseStart_4531847 : Nat := 118140960795 + 4531847 * 2 ^ 59
def prefixEnd_4531847 : Nat := 4983230072969 + 3 ^ 40 * 4531847 * 2
def baseEnd_4531847 : Nat := 258557307070692873496769

theorem tailTrace_4531847 : CollatzResearch.WordTrace tailWord_4531847 prefixEnd_4531847 258557307070692873496769 := by
  unfold tailWord_4531847
  simp only [CollatzResearch.WordTrace]
  refine ⟨165290039212899771693185795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110193359475266514462123863 165290039212899771693185795)
  ·
    refine ⟨247935058819349657539778693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165290039212899771693185795 247935058819349657539778693)
    ·
      refine ⟨46487823528628060788708505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 247935058819349657539778693 46487823528628060788708505)
      ·
        refine ⟨34865867646471045591531379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46487823528628060788708505 34865867646471045591531379)
        ·
          refine ⟨52298801469706568387297069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34865867646471045591531379 52298801469706568387297069)
          ·
            refine ⟨19612050551139963145236401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52298801469706568387297069 19612050551139963145236401)
            ·
              refine ⟨14709037913354972358927301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19612050551139963145236401 14709037913354972358927301)
              ·
                refine ⟨2757944608754057317298869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14709037913354972358927301 2757944608754057317298869)
                ·
                  refine ⟨258557307070692873496769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2757944608754057317298869 258557307070692873496769)
                  ·
                    rfl

theorem cell23_4531847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 4, 5].length) (baseStart_4531847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531847 prefixEnd_4531847 := by exact prefixLift 4531847
  have htrace : WordTrace (prefixWord ++ tailWord_4531847) baseStart_4531847 baseEnd_4531847 := by
    simpa [prefixWord, tailWord_4531847, baseEnd_4531847] using wordTrace_append hprefix tailTrace_4531847
  have hstable : (prefixWord ++ tailWord_4531847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531847).length < 2 ^ (prefixWord ++ tailWord_4531847).sum := by decide
  have hdescent : baseEnd_4531847 < baseStart_4531847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531858 : List Nat := [3, 2, 3, 1, 4, 1, 1, 1, 1, 4, 2]
def baseStart_4531858 : Nat := 118140960795 + 4531858 * 2 ^ 59
def prefixEnd_4531858 : Nat := 4983230072969 + 3 ^ 40 * 4531858 * 2
def baseEnd_4531858 : Nat := 2327021411923435318433371

theorem tailTrace_4531858 : CollatzResearch.WordTrace tailWord_4531858 prefixEnd_4531858 2327021411923435318433371 := by
  unfold tailWord_4531858
  simp only [CollatzResearch.WordTrace]
  refine ⟨41322610103964980142959057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110193626943906613714557485 41322610103964980142959057)
  ·
    refine ⟨30991957577973735107219293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41322610103964980142959057 30991957577973735107219293)
    ·
      refine ⟨11621984091740150665207235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30991957577973735107219293 11621984091740150665207235)
      ·
        refine ⟨17432976137610225997810853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11621984091740150665207235 17432976137610225997810853)
        ·
          refine ⟨3268683025801917374589535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17432976137610225997810853 3268683025801917374589535)
          ·
            refine ⟨4903024538702876061884303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3268683025801917374589535 4903024538702876061884303)
            ·
              refine ⟨7354536808054314092826455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4903024538702876061884303 7354536808054314092826455)
              ·
                refine ⟨11031805212081471139239683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7354536808054314092826455 11031805212081471139239683)
                ·
                  refine ⟨16547707818122206708859525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11031805212081471139239683 16547707818122206708859525)
                  ·
                    refine ⟨3102695215897913757911161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16547707818122206708859525 3102695215897913757911161)
                    ·
                      refine ⟨2327021411923435318433371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3102695215897913757911161 2327021411923435318433371)
                      ·
                        rfl

theorem cell23_4531858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_4531858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531858 prefixEnd_4531858 := by exact prefixLift 4531858
  have htrace : WordTrace (prefixWord ++ tailWord_4531858) baseStart_4531858 baseEnd_4531858 := by
    simpa [prefixWord, tailWord_4531858, baseEnd_4531858] using wordTrace_append hprefix tailTrace_4531858
  have hstable : (prefixWord ++ tailWord_4531858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531858).length < 2 ^ (prefixWord ++ tailWord_4531858).sum := by decide
  have hdescent : baseEnd_4531858 < baseStart_4531858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531894 : List Nat := [5, 1, 3, 1, 1, 1, 1, 1, 4, 5]
def baseStart_4531894 : Nat := 118140960795 + 4531894 * 2 ^ 59
def prefixEnd_4531894 : Nat := 4983230072969 + 3 ^ 40 * 4531894 * 2
def baseEnd_4531894 : Nat := 775679965742332392527735

theorem tailTrace_4531894 : CollatzResearch.WordTrace tailWord_4531894 prefixEnd_4531894 775679965742332392527735 := by
  unfold tailWord_4531894
  simp only [CollatzResearch.WordTrace]
  refine ⟨10330734590233093670009171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110194502295819665813431157 10330734590233093670009171)
  ·
    refine ⟨15496101885349640505013757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10330734590233093670009171 15496101885349640505013757)
    ·
      refine ⟨5811038207006115189380159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15496101885349640505013757 5811038207006115189380159)
      ·
        refine ⟨8716557310509172784070239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5811038207006115189380159 8716557310509172784070239)
        ·
          refine ⟨13074835965763759176105359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8716557310509172784070239 13074835965763759176105359)
          ·
            refine ⟨19612253948645638764158039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13074835965763759176105359 19612253948645638764158039)
            ·
              refine ⟨29418380922968458146237059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19612253948645638764158039 29418380922968458146237059)
              ·
                refine ⟨44127571384452687219355589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29418380922968458146237059 44127571384452687219355589)
                ·
                  refine ⟨8273919634584878853629173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44127571384452687219355589 8273919634584878853629173)
                  ·
                    refine ⟨775679965742332392527735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8273919634584878853629173 775679965742332392527735)
                    ·
                      rfl

theorem cell23_4531894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_4531894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531894 prefixEnd_4531894 := by exact prefixLift 4531894
  have htrace : WordTrace (prefixWord ++ tailWord_4531894) baseStart_4531894 baseEnd_4531894 := by
    simpa [prefixWord, tailWord_4531894, baseEnd_4531894] using wordTrace_append hprefix tailTrace_4531894
  have hstable : (prefixWord ++ tailWord_4531894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531894).length < 2 ^ (prefixWord ++ tailWord_4531894).sum := by decide
  have hdescent : baseEnd_4531894 < baseStart_4531894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531897 : List Nat := [1, 2, 1, 4, 1, 1, 2, 1, 4, 4, 2]
def baseStart_4531897 : Nat := 118140960795 + 4531897 * 2 ^ 59
def prefixEnd_4531897 : Nat := 4983230072969 + 3 ^ 40 * 4531897 * 2
def baseEnd_4531897 : Nat := 2327041437668960665845691

theorem tailTrace_4531897 : CollatzResearch.WordTrace tailWord_4531897 prefixEnd_4531897 2327041437668960665845691 := by
  unfold tailWord_4531897
  simp only [CollatzResearch.WordTrace]
  refine ⟨165291862862718630232505945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110194575241812420155003963 165291862862718630232505945)
  ·
    refine ⟨123968897147038972674379459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165291862862718630232505945 123968897147038972674379459)
    ·
      refine ⟨185953345720558459011569189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123968897147038972674379459 185953345720558459011569189)
      ·
        refine ⟨34866252322604711064669223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 185953345720558459011569189 34866252322604711064669223)
        ·
          refine ⟨52299378483907066597003835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34866252322604711064669223 52299378483907066597003835)
          ·
            refine ⟨78449067725860599895505753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52299378483907066597003835 78449067725860599895505753)
            ·
              refine ⟨58836800794395449921629315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78449067725860599895505753 58836800794395449921629315)
              ·
                refine ⟨88255201191593174882443973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58836800794395449921629315 88255201191593174882443973)
                ·
                  refine ⟨16547850223423720290458245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88255201191593174882443973 16547850223423720290458245)
                  ·
                    refine ⟨3102721916891947554460921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16547850223423720290458245 3102721916891947554460921)
                    ·
                      refine ⟨2327041437668960665845691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3102721916891947554460921 2327041437668960665845691)
                      ·
                        rfl

theorem cell23_4531897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_4531897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531897 prefixEnd_4531897 := by exact prefixLift 4531897
  have htrace : WordTrace (prefixWord ++ tailWord_4531897) baseStart_4531897 baseEnd_4531897 := by
    simpa [prefixWord, tailWord_4531897, baseEnd_4531897] using wordTrace_append hprefix tailTrace_4531897
  have hstable : (prefixWord ++ tailWord_4531897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531897).length < 2 ^ (prefixWord ++ tailWord_4531897).sum := by decide
  have hdescent : baseEnd_4531897 < baseStart_4531897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531958 : List Nat := [5, 1, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_4531958 : Nat := 118140960795 + 4531958 * 2 ^ 59
def prefixEnd_4531958 : Nat := 4983230072969 + 3 ^ 40 * 4531958 * 2
def baseEnd_4531958 : Nat := 775690919996294975727637

theorem tailTrace_4531958 : CollatzResearch.WordTrace tailWord_4531958 prefixEnd_4531958 775690919996294975727637 := by
  unfold tailWord_4531958
  simp only [CollatzResearch.WordTrace]
  refine ⟨10330880482218602353154783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110196058476998425100317685 10330880482218602353154783)
  ·
    refine ⟨15496320723327903529732175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10330880482218602353154783 15496320723327903529732175)
    ·
      refine ⟨23244481084991855294598263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15496320723327903529732175 23244481084991855294598263)
      ·
        refine ⟨34866721627487782941897395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23244481084991855294598263 34866721627487782941897395)
        ·
          refine ⟨52300082441231674412846093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34866721627487782941897395 52300082441231674412846093)
          ·
            refine ⟨19612530915461877904817285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52300082441231674412846093 19612530915461877904817285)
            ·
              refine ⟨3677349546649102107153241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19612530915461877904817285 3677349546649102107153241)
              ·
                refine ⟨2758012159986826580364931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3677349546649102107153241 2758012159986826580364931)
                ·
                  refine ⟨4137018239980239870547397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758012159986826580364931 4137018239980239870547397)
                  ·
                    refine ⟨775690919996294975727637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4137018239980239870547397 775690919996294975727637)
                    ·
                      rfl

theorem cell23_4531958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_4531958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531958 prefixEnd_4531958 := by exact prefixLift 4531958
  have htrace : WordTrace (prefixWord ++ tailWord_4531958) baseStart_4531958 baseEnd_4531958 := by
    simpa [prefixWord, tailWord_4531958, baseEnd_4531958] using wordTrace_append hprefix tailTrace_4531958
  have hstable : (prefixWord ++ tailWord_4531958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531958).length < 2 ^ (prefixWord ++ tailWord_4531958).sum := by decide
  have hdescent : baseEnd_4531958 < baseStart_4531958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531964 : List Nat := [2, 2, 2, 1, 3, 1, 2, 3, 3, 1, 3]
def baseStart_4531964 : Nat := 118140960795 + 4531964 * 2 ^ 59
def prefixEnd_4531964 : Nat := 4983230072969 + 3 ^ 40 * 4531964 * 2
def baseEnd_4531964 : Nat := 2327075840872811903707883

theorem tailTrace_4531964 : CollatzResearch.WordTrace tailWord_4531964 prefixEnd_4531964 2327075840872811903707883 := by
  unfold tailWord_4531964
  simp only [CollatzResearch.WordTrace]
  refine ⟨82647153276737950337597473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110196204368983933783463297 82647153276737950337597473)
  ·
    refine ⟨61985364957553462753198105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82647153276737950337597473 61985364957553462753198105)
    ·
      refine ⟨46489023718165097064898579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61985364957553462753198105 46489023718165097064898579)
      ·
        refine ⟨69733535577247645597347869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46489023718165097064898579 69733535577247645597347869)
        ·
          refine ⟨26150075841467867099005451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69733535577247645597347869 26150075841467867099005451)
          ·
            refine ⟨39225113762201800648508177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26150075841467867099005451 39225113762201800648508177)
            ·
              refine ⟨29418835321651350486381133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39225113762201800648508177 29418835321651350486381133)
              ·
                refine ⟨11032063245619256432392925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29418835321651350486381133 11032063245619256432392925)
                ·
                  refine ⟨4137023717107221162147347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11032063245619256432392925 4137023717107221162147347)
                  ·
                    refine ⟨6205535575660831743221021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4137023717107221162147347 6205535575660831743221021)
                    ·
                      refine ⟨2327075840872811903707883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6205535575660831743221021 2327075840872811903707883)
                      ·
                        rfl

theorem cell23_4531964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_4531964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531964 prefixEnd_4531964 := by exact prefixLift 4531964
  have htrace : WordTrace (prefixWord ++ tailWord_4531964) baseStart_4531964 baseEnd_4531964 := by
    simpa [prefixWord, tailWord_4531964, baseEnd_4531964] using wordTrace_append hprefix tailTrace_4531964
  have hstable : (prefixWord ++ tailWord_4531964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531964).length < 2 ^ (prefixWord ++ tailWord_4531964).sum := by decide
  have hdescent : baseEnd_4531964 < baseStart_4531964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531987 : List Nat := [1, 1, 1, 2, 1, 3, 2, 1, 1, 8, 2]
def baseStart_4531987 : Nat := 118140960795 + 4531987 * 2 ^ 59
def prefixEnd_4531987 : Nat := 4983230072969 + 3 ^ 40 * 4531987 * 2
def baseEnd_4531987 : Nat := 2327087650927865313720277

theorem tailTrace_4531987 : CollatzResearch.WordTrace tailWord_4531987 prefixEnd_4531987 2327087650927865313720277 := by
  unfold tailWord_4531987
  simp only [CollatzResearch.WordTrace]
  refine ⟨165295145432392575603282215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110196763621595050402188143 165295145432392575603282215)
  ·
    refine ⟨247942718148588863404923323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165295145432392575603282215 247942718148588863404923323)
    ·
      refine ⟨371914077222883295107384985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247942718148588863404923323 371914077222883295107384985)
      ·
        refine ⟨278935557917162471330538739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371914077222883295107384985 278935557917162471330538739)
        ·
          refine ⟨418403336875743706995808109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278935557917162471330538739 418403336875743706995808109)
          ·
            refine ⟨156901251328403890123428041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 418403336875743706995808109 156901251328403890123428041)
            ·
              refine ⟨117675938496302917592571031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156901251328403890123428041 117675938496302917592571031)
              ·
                refine ⟨176513907744454376388856547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117675938496302917592571031 176513907744454376388856547)
                ·
                  refine ⟨264770861616681564583284821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176513907744454376388856547 264770861616681564583284821)
                  ·
                    refine ⟨3102783534570487084960369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 264770861616681564583284821 3102783534570487084960369)
                    ·
                      refine ⟨2327087650927865313720277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3102783534570487084960369 2327087650927865313720277)
                      ·
                        rfl

theorem cell23_4531987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 8, 2].length) (baseStart_4531987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531987 prefixEnd_4531987 := by exact prefixLift 4531987
  have htrace : WordTrace (prefixWord ++ tailWord_4531987) baseStart_4531987 baseEnd_4531987 := by
    simpa [prefixWord, tailWord_4531987, baseEnd_4531987] using wordTrace_append hprefix tailTrace_4531987
  have hstable : (prefixWord ++ tailWord_4531987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531987).length < 2 ^ (prefixWord ++ tailWord_4531987).sum := by decide
  have hdescent : baseEnd_4531987 < baseStart_4531987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4531991 : List Nat := [1, 1, 3, 4, 2, 1, 3, 1, 2, 3, 2]
def baseStart_4531991 : Nat := 118140960795 + 4531991 * 2 ^ 59
def prefixEnd_4531991 : Nat := 4983230072969 + 3 ^ 40 * 4531991 * 2
def baseEnd_4531991 : Nat := 2327089704850483298070259

theorem tailTrace_4531991 : CollatzResearch.WordTrace tailWord_4531991 prefixEnd_4531991 2327089704850483298070259 := by
  unfold tailWord_4531991
  simp only [CollatzResearch.WordTrace]
  refine ⟨165295291324378084286427827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110196860882918722857618551 165295291324378084286427827)
  ·
    refine ⟨247942936986567126429641741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165295291324378084286427827 247942936986567126429641741)
    ·
      refine ⟨92978601369962672411115653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247942936986567126429641741 92978601369962672411115653)
      ·
        refine ⟨17433487756868001077084185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92978601369962672411115653 17433487756868001077084185)
        ·
          refine ⟨13075115817651000807813139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17433487756868001077084185 13075115817651000807813139)
          ·
            refine ⟨19612673726476501211719709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13075115817651000807813139 19612673726476501211719709)
            ·
              refine ⟨7354752647428687954394891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19612673726476501211719709 7354752647428687954394891)
              ·
                refine ⟨11032128971143031931592337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7354752647428687954394891 11032128971143031931592337)
                ·
                  refine ⟨8274096728357273948694253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11032128971143031931592337 8274096728357273948694253)
                  ·
                    refine ⟨3102786273133977730760345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8274096728357273948694253 3102786273133977730760345)
                    ·
                      refine ⟨2327089704850483298070259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3102786273133977730760345 2327089704850483298070259)
                      ·
                        rfl

theorem cell23_4531991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_4531991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4531991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4531991 prefixEnd_4531991 := by exact prefixLift 4531991
  have htrace : WordTrace (prefixWord ++ tailWord_4531991) baseStart_4531991 baseEnd_4531991 := by
    simpa [prefixWord, tailWord_4531991, baseEnd_4531991] using wordTrace_append hprefix tailTrace_4531991
  have hstable : (prefixWord ++ tailWord_4531991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4531991).length < 2 ^ (prefixWord ++ tailWord_4531991).sum := by decide
  have hdescent : baseEnd_4531991 < baseStart_4531991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4531991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532001 : List Nat := [1, 2, 3, 2, 1, 5, 2, 1, 1, 5]
def baseStart_4532001 : Nat := 118140960795 + 4532001 * 2 ^ 59
def prefixEnd_4532001 : Nat := 4983230072969 + 3 ^ 40 * 4532001 * 2
def baseEnd_4532001 : Nat := 775698279885676086315071

theorem tailTrace_4532001 : CollatzResearch.WordTrace tailWord_4532001 prefixEnd_4532001 775698279885676086315071 := by
  unfold tailWord_4532001
  simp only [CollatzResearch.WordTrace]
  refine ⟨165295656054341855994291857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110197104036227903996194571 165295656054341855994291857)
  ·
    refine ⟨123971742040756391995718893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165295656054341855994291857 123971742040756391995718893)
    ·
      refine ⟨46489403265283646998394585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123971742040756391995718893 46489403265283646998394585)
      ·
        refine ⟨34867052448962735248795939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46489403265283646998394585 34867052448962735248795939)
        ·
          refine ⟨52300578673444102873193909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34867052448962735248795939 52300578673444102873193909)
          ·
            refine ⟨4903179250635384644361929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52300578673444102873193909 4903179250635384644361929)
            ·
              refine ⟨3677384437976538483271447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4903179250635384644361929 3677384437976538483271447)
              ·
                refine ⟨5516076656964807724907171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3677384437976538483271447 5516076656964807724907171)
                ·
                  refine ⟨8274114985447211587360757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5516076656964807724907171 8274114985447211587360757)
                  ·
                    refine ⟨775698279885676086315071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8274114985447211587360757 775698279885676086315071)
                    ·
                      rfl

theorem cell23_4532001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_4532001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532001 prefixEnd_4532001 := by exact prefixLift 4532001
  have htrace : WordTrace (prefixWord ++ tailWord_4532001) baseStart_4532001 baseEnd_4532001 := by
    simpa [prefixWord, tailWord_4532001, baseEnd_4532001] using wordTrace_append hprefix tailTrace_4532001
  have hstable : (prefixWord ++ tailWord_4532001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532001).length < 2 ^ (prefixWord ++ tailWord_4532001).sum := by decide
  have hdescent : baseEnd_4532001 < baseStart_4532001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532031 : List Nat := [1, 1, 2, 2, 7, 1, 1, 1, 1, 6]
def baseStart_4532031 : Nat := 118140960795 + 4532031 * 2 ^ 59
def prefixEnd_4532031 : Nat := 4983230072969 + 3 ^ 40 * 4532031 * 2
def baseEnd_4532031 : Nat := 775703414692221047190025

theorem tailTrace_4532031 : CollatzResearch.WordTrace tailWord_4532031 prefixEnd_4532031 775703414692221047190025 := by
  unfold tailWord_4532031
  simp only [CollatzResearch.WordTrace]
  refine ⟨165296750244233171117883947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110197833496155447411922631 165296750244233171117883947)
  ·
    refine ⟨247945125366349756676825921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165296750244233171117883947 247945125366349756676825921)
    ·
      refine ⟨185958844024762317507619441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247945125366349756676825921 185958844024762317507619441)
      ·
        refine ⟨139469133018571738130714581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185958844024762317507619441 139469133018571738130714581)
        ·
          refine ⟨3268807805122775112438623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 139469133018571738130714581 3268807805122775112438623)
          ·
            refine ⟨4903211707684162668657935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3268807805122775112438623 4903211707684162668657935)
            ·
              refine ⟨7354817561526244002986903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4903211707684162668657935 7354817561526244002986903)
              ·
                refine ⟨11032226342289366004480355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7354817561526244002986903 11032226342289366004480355)
                ·
                  refine ⟨16548339513434049006720533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11032226342289366004480355 16548339513434049006720533)
                  ·
                    refine ⟨775703414692221047190025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16548339513434049006720533 775703414692221047190025)
                    ·
                      rfl

theorem cell23_4532031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 1, 1, 6].length) (baseStart_4532031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532031 prefixEnd_4532031 := by exact prefixLift 4532031
  have htrace : WordTrace (prefixWord ++ tailWord_4532031) baseStart_4532031 baseEnd_4532031 := by
    simpa [prefixWord, tailWord_4532031, baseEnd_4532031] using wordTrace_append hprefix tailTrace_4532031
  have hstable : (prefixWord ++ tailWord_4532031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532031).length < 2 ^ (prefixWord ++ tailWord_4532031).sum := by decide
  have hdescent : baseEnd_4532031 < baseStart_4532031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532038 : List Nat := [6, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4]
def baseStart_4532038 : Nat := 118140960795 + 4532038 * 2 ^ 59
def prefixEnd_4532038 : Nat := 4983230072969 + 3 ^ 40 * 4532038 * 2
def baseEnd_4532038 : Nat := 2327113838441244614182543

theorem tailTrace_4532038 : CollatzResearch.WordTrace tailWord_4532038 prefixEnd_4532038 2327113838441244614182543 := by
  unfold tailWord_4532038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5165531423600244103543399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 110198003703471874208925845 5165531423600244103543399)
  ·
    refine ⟨7748297135400366155315099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5165531423600244103543399 7748297135400366155315099)
    ·
      refine ⟨11622445703100549232972649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7748297135400366155315099 11622445703100549232972649)
      ·
        refine ⟨8716834277325411924729487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11622445703100549232972649 8716834277325411924729487)
        ·
          refine ⟨13075251415988117887094231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8716834277325411924729487 13075251415988117887094231)
          ·
            refine ⟨19612877123982176830641347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13075251415988117887094231 19612877123982176830641347)
            ·
              refine ⟨29419315685973265245962021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19612877123982176830641347 29419315685973265245962021)
              ·
                refine ⟨5516121691119987233617879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29419315685973265245962021 5516121691119987233617879)
                ·
                  refine ⟨8274182536679980850426819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5516121691119987233617879 8274182536679980850426819)
                  ·
                    refine ⟨12411273805019971275640229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8274182536679980850426819 12411273805019971275640229)
                    ·
                      refine ⟨2327113838441244614182543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12411273805019971275640229 2327113838441244614182543)
                      ·
                        rfl

theorem cell23_4532038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_4532038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532038 prefixEnd_4532038 := by exact prefixLift 4532038
  have htrace : WordTrace (prefixWord ++ tailWord_4532038) baseStart_4532038 baseEnd_4532038 := by
    simpa [prefixWord, tailWord_4532038, baseEnd_4532038] using wordTrace_append hprefix tailTrace_4532038
  have hstable : (prefixWord ++ tailWord_4532038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532038).length < 2 ^ (prefixWord ++ tailWord_4532038).sum := by decide
  have hdescent : baseEnd_4532038 < baseStart_4532038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532071 : List Nat := [1, 1, 5, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_4532071 : Nat := 118140960795 + 4532071 * 2 ^ 59
def prefixEnd_4532071 : Nat := 4983230072969 + 3 ^ 40 * 4532071 * 2
def baseEnd_4532071 : Nat := 2327130783302842985069891

theorem tailTrace_4532071 : CollatzResearch.WordTrace tailWord_4532071 prefixEnd_4532071 2327130783302842985069891 := by
  unfold tailWord_4532071
  simp only [CollatzResearch.WordTrace]
  refine ⟨165298209164088257949340067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110198806109392171966226711 165298209164088257949340067)
  ·
    refine ⟨247947313746132386924010101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165298209164088257949340067 247947313746132386924010101)
    ·
      refine ⟨23245060663699911274125947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 247947313746132386924010101 23245060663699911274125947)
      ·
        refine ⟨34867590995549866911188921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23245060663699911274125947 34867590995549866911188921)
        ·
          refine ⟨26150693246662400183391691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34867590995549866911188921 26150693246662400183391691)
          ·
            refine ⟨39226039869993600275087537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26150693246662400183391691 39226039869993600275087537)
            ·
              refine ⟨29419529902495200206315653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39226039869993600275087537 29419529902495200206315653)
              ·
                refine ⟨5516161856717850038684185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29419529902495200206315653 5516161856717850038684185)
                ·
                  refine ⟨4137121392538387529013139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5516161856717850038684185 4137121392538387529013139)
                  ·
                    refine ⟨6205682088807581293519709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4137121392538387529013139 6205682088807581293519709)
                    ·
                      refine ⟨2327130783302842985069891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6205682088807581293519709 2327130783302842985069891)
                      ·
                        rfl

theorem cell23_4532071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_4532071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532071 prefixEnd_4532071 := by exact prefixLift 4532071
  have htrace : WordTrace (prefixWord ++ tailWord_4532071) baseStart_4532071 baseEnd_4532071 := by
    simpa [prefixWord, tailWord_4532071, baseEnd_4532071] using wordTrace_append hprefix tailTrace_4532071
  have hstable : (prefixWord ++ tailWord_4532071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532071).length < 2 ^ (prefixWord ++ tailWord_4532071).sum := by decide
  have hdescent : baseEnd_4532071 < baseStart_4532071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532107 : List Nat := [1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 4]
def baseStart_4532107 : Nat := 118140960795 + 4532107 * 2 ^ 59
def prefixEnd_4532107 : Nat := 4983230072969 + 3 ^ 40 * 4532107 * 2
def baseEnd_4532107 : Nat := 2327149268606404844219725

theorem tailTrace_4532107 : CollatzResearch.WordTrace tailWord_4532107 prefixEnd_4532107 2327149268606404844219725 := by
  unfold tailWord_4532107
  simp only [CollatzResearch.WordTrace]
  refine ⟨165299522191957836097650575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110199681461305224065100383 165299522191957836097650575)
  ·
    refine ⟨247949283287936754146475863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165299522191957836097650575 247949283287936754146475863)
    ·
      refine ⟨371923924931905131219713795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247949283287936754146475863 371923924931905131219713795)
      ·
        refine ⟨557885887397857696829570693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371923924931905131219713795 557885887397857696829570693)
        ·
          refine ⟨104603603887098318155544505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 557885887397857696829570693 104603603887098318155544505)
          ·
            refine ⟨78452702915323738616658379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104603603887098318155544505 78452702915323738616658379)
            ·
              refine ⟨117679054372985607924987569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78452702915323738616658379 117679054372985607924987569)
              ·
                refine ⟨88259290779739205943740677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117679054372985607924987569 88259290779739205943740677)
                ·
                  refine ⟨16548617021201101114451377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88259290779739205943740677 16548617021201101114451377)
                  ·
                    refine ⟨12411462765900825835838533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16548617021201101114451377 12411462765900825835838533)
                    ·
                      refine ⟨2327149268606404844219725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12411462765900825835838533 2327149268606404844219725)
                      ·
                        rfl

theorem cell23_4532107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 2, 4, 2, 4].length) (baseStart_4532107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532107 prefixEnd_4532107 := by exact prefixLift 4532107
  have htrace : WordTrace (prefixWord ++ tailWord_4532107) baseStart_4532107 baseEnd_4532107 := by
    simpa [prefixWord, tailWord_4532107, baseEnd_4532107] using wordTrace_append hprefix tailTrace_4532107
  have hstable : (prefixWord ++ tailWord_4532107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532107).length < 2 ^ (prefixWord ++ tailWord_4532107).sum := by decide
  have hdescent : baseEnd_4532107 < baseStart_4532107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532147 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 1, 7]
def baseStart_4532147 : Nat := 118140960795 + 4532147 * 2 ^ 59
def prefixEnd_4532147 : Nat := 4983230072969 + 3 ^ 40 * 4532147 * 2
def baseEnd_4532147 : Nat := 775723269277528229239847

theorem tailTrace_4532147 : CollatzResearch.WordTrace tailWord_4532147 prefixEnd_4532147 775723269277528229239847 := by
  unfold tailWord_4532147
  simp only [CollatzResearch.WordTrace]
  refine ⟨165300981111812922929106695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110200654074541948619404463 165300981111812922929106695)
  ·
    refine ⟨247951471667719384393660043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165300981111812922929106695 247951471667719384393660043)
    ·
      refine ⟨371927207501579076590490065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247951471667719384393660043 371927207501579076590490065)
      ·
        refine ⟨278945405626184307442867549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371927207501579076590490065 278945405626184307442867549)
        ·
          refine ⟨104604527109819115291075331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 278945405626184307442867549 104604527109819115291075331)
          ·
            refine ⟨156906790664728672936612997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104604527109819115291075331 156906790664728672936612997)
            ·
              refine ⟨29420023249636626175614937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156906790664728672936612997 29420023249636626175614937)
              ·
                refine ⟨22065017437227469631711203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29420023249636626175614937 22065017437227469631711203)
                ·
                  refine ⟨33097526155841204447566805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22065017437227469631711203 33097526155841204447566805)
                  ·
                    refine ⟨775723269277528229239847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33097526155841204447566805 775723269277528229239847)
                    ·
                      rfl

theorem cell23_4532147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 7].length) (baseStart_4532147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532147 prefixEnd_4532147 := by exact prefixLift 4532147
  have htrace : WordTrace (prefixWord ++ tailWord_4532147) baseStart_4532147 baseEnd_4532147 := by
    simpa [prefixWord, tailWord_4532147, baseEnd_4532147] using wordTrace_append hprefix tailTrace_4532147
  have hstable : (prefixWord ++ tailWord_4532147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532147).length < 2 ^ (prefixWord ++ tailWord_4532147).sum := by decide
  have hdescent : baseEnd_4532147 < baseStart_4532147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532184 : List Nat := [2, 1, 2, 2, 2, 2, 2, 1, 4, 1, 4]
def baseStart_4532184 : Nat := 118140960795 + 4532184 * 2 ^ 59
def prefixEnd_4532184 : Nat := 4983230072969 + 3 ^ 40 * 4532184 * 2
def baseEnd_4532184 : Nat := 2327188806616801042956871

theorem tailTrace_4532184 : CollatzResearch.WordTrace tailWord_4532184 prefixEnd_4532184 2327188806616801042956871 := by
  unfold tailWord_4532184
  simp only [CollatzResearch.WordTrace]
  refine ⟨82651165306339439124101803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110201553741785918832135737 82651165306339439124101803)
  ·
    refine ⟨123976747959509158686152705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82651165306339439124101803 123976747959509158686152705)
    ·
      refine ⟨92982560969631869014614529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123976747959509158686152705 92982560969631869014614529)
      ·
        refine ⟨69736920727223901760960897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92982560969631869014614529 69736920727223901760960897)
        ·
          refine ⟨52302690545417926320720673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69736920727223901760960897 52302690545417926320720673)
          ·
            refine ⟨39227017909063444740540505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52302690545417926320720673 39227017909063444740540505)
            ·
              refine ⟨29420263431797583555405379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39227017909063444740540505 29420263431797583555405379)
              ·
                refine ⟨44130395147696375333108069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29420263431797583555405379 44130395147696375333108069)
                ·
                  refine ⟨8274449090193070374957763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44130395147696375333108069 8274449090193070374957763)
                  ·
                    refine ⟨12411673635289605562436645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8274449090193070374957763 12411673635289605562436645)
                    ·
                      refine ⟨2327188806616801042956871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12411673635289605562436645 2327188806616801042956871)
                      ·
                        rfl

theorem cell23_4532184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_4532184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532184 prefixEnd_4532184 := by exact prefixLift 4532184
  have htrace : WordTrace (prefixWord ++ tailWord_4532184) baseStart_4532184 baseEnd_4532184 := by
    simpa [prefixWord, tailWord_4532184, baseEnd_4532184] using wordTrace_append hprefix tailTrace_4532184
  have hstable : (prefixWord ++ tailWord_4532184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532184).length < 2 ^ (prefixWord ++ tailWord_4532184).sum := by decide
  have hdescent : baseEnd_4532184 < baseStart_4532184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532245 : List Nat := [1, 3, 2, 1, 6, 1, 1, 1, 3, 4]
def baseStart_4532245 : Nat := 118140960795 + 4532245 * 2 ^ 59
def prefixEnd_4532245 : Nat := 4983230072969 + 3 ^ 40 * 4532245 * 2
def baseEnd_4532245 : Nat := 775740042978908434764697

theorem tailTrace_4532245 : CollatzResearch.WordTrace tailWord_4532245 prefixEnd_4532245 775740042978908434764697 := by
  unfold tailWord_4532245
  simp only [CollatzResearch.WordTrace]
  refine ⟨165304555465457885666174189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110203036976971923777449459 165304555465457885666174189)
  ·
    refine ⟨61989208299546707124815321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165304555465457885666174189 61989208299546707124815321)
    ·
      refine ⟨46491906224660030343611491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61989208299546707124815321 46491906224660030343611491)
      ·
        refine ⟨69737859336990045515417237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46491906224660030343611491 69737859336990045515417237)
        ·
          refine ⟨3268962156421408383535183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69737859336990045515417237 3268962156421408383535183)
          ·
            refine ⟨4903443234632112575302775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3268962156421408383535183 4903443234632112575302775)
            ·
              refine ⟨7355164851948168862954163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4903443234632112575302775 7355164851948168862954163)
              ·
                refine ⟨11032747277922253294431245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7355164851948168862954163 11032747277922253294431245)
                ·
                  refine ⟨4137280229220844985411717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11032747277922253294431245 4137280229220844985411717)
                  ·
                    refine ⟨775740042978908434764697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4137280229220844985411717 775740042978908434764697)
                    ·
                      rfl

theorem cell23_4532245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_4532245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532245 prefixEnd_4532245 := by exact prefixLift 4532245
  have htrace : WordTrace (prefixWord ++ tailWord_4532245) baseStart_4532245 baseEnd_4532245 := by
    simpa [prefixWord, tailWord_4532245, baseEnd_4532245] using wordTrace_append hprefix tailTrace_4532245
  have hstable : (prefixWord ++ tailWord_4532245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532245).length < 2 ^ (prefixWord ++ tailWord_4532245).sum := by decide
  have hdescent : baseEnd_4532245 < baseStart_4532245 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532251 : List Nat := [1, 1, 1, 1, 1, 1, 3, 7, 3, 1, 3]
def baseStart_4532251 : Nat := 118140960795 + 4532251 * 2 ^ 59
def prefixEnd_4532251 : Nat := 4983230072969 + 3 ^ 40 * 4532251 * 2
def baseEnd_4532251 : Nat := 2327223209820652280819063

theorem tailTrace_4532251 : CollatzResearch.WordTrace tailWord_4532251 prefixEnd_4532251 2327223209820652280819063 := by
  unfold tailWord_4532251
  simp only [CollatzResearch.WordTrace]
  refine ⟨165304774303436148690892607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110203182868957432460595071 165304774303436148690892607)
  ·
    refine ⟨247957161455154223036338911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165304774303436148690892607 247957161455154223036338911)
    ·
      refine ⟨371935742182731334554508367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247957161455154223036338911 371935742182731334554508367)
      ·
        refine ⟨557903613274097001831762551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 371935742182731334554508367 557903613274097001831762551)
        ·
          refine ⟨836855419911145502747643827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 557903613274097001831762551 836855419911145502747643827)
          ·
            refine ⟨1255283129866718254121465741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 836855419911145502747643827 1255283129866718254121465741)
            ·
              refine ⟨470731173700019345295549653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1255283129866718254121465741 470731173700019345295549653)
              ·
                refine ⟨11032761883594203405364445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 470731173700019345295549653 11032761883594203405364445)
                ·
                  refine ⟨4137285706347826277011667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11032761883594203405364445 4137285706347826277011667)
                  ·
                    refine ⟨6205928559521739415517501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4137285706347826277011667 6205928559521739415517501)
                    ·
                      refine ⟨2327223209820652280819063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6205928559521739415517501 2327223209820652280819063)
                      ·
                        rfl

theorem cell23_4532251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 7, 3, 1, 3].length) (baseStart_4532251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532251 prefixEnd_4532251 := by exact prefixLift 4532251
  have htrace : WordTrace (prefixWord ++ tailWord_4532251) baseStart_4532251 baseEnd_4532251 := by
    simpa [prefixWord, tailWord_4532251, baseEnd_4532251] using wordTrace_append hprefix tailTrace_4532251
  have hstable : (prefixWord ++ tailWord_4532251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532251).length < 2 ^ (prefixWord ++ tailWord_4532251).sum := by decide
  have hdescent : baseEnd_4532251 < baseStart_4532251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532285 : List Nat := [1, 4, 1, 3, 1, 1, 2, 5, 1, 1, 3]
def baseStart_4532285 : Nat := 118140960795 + 4532285 * 2 ^ 59
def prefixEnd_4532285 : Nat := 4983230072969 + 3 ^ 40 * 4532285 * 2
def baseEnd_4532285 : Nat := 2327240668162905147793907

theorem tailTrace_4532285 : CollatzResearch.WordTrace tailWord_4532285 prefixEnd_4532285 2327240668162905147793907 := by
  unfold tailWord_4532285
  simp only [CollatzResearch.WordTrace]
  refine ⟨165306014385312972497630309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110204009590208648331753539 165306014385312972497630309)
  ·
    refine ⟨30994877697246182343305683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165306014385312972497630309 30994877697246182343305683)
    ·
      refine ⟨46492316545869273514958525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30994877697246182343305683 46492316545869273514958525)
      ·
        refine ⟨17434618704700977568109447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46492316545869273514958525 17434618704700977568109447)
        ·
          refine ⟨26151928057051466352164171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17434618704700977568109447 26151928057051466352164171)
          ·
            refine ⟨39227892085577199528246257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26151928057051466352164171 39227892085577199528246257)
            ·
              refine ⟨29420919064182899646184693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39227892085577199528246257 29420919064182899646184693)
              ·
                refine ⟨2758211162267146841829815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29420919064182899646184693 2758211162267146841829815)
                ·
                  refine ⟨4137316743400720262744723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758211162267146841829815 4137316743400720262744723)
                  ·
                    refine ⟨6205975115101080394117085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4137316743400720262744723 6205975115101080394117085)
                    ·
                      refine ⟨2327240668162905147793907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6205975115101080394117085 2327240668162905147793907)
                      ·
                        rfl

theorem cell23_4532285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_4532285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532285 prefixEnd_4532285 := by exact prefixLift 4532285
  have htrace : WordTrace (prefixWord ++ tailWord_4532285) baseStart_4532285 baseEnd_4532285 := by
    simpa [prefixWord, tailWord_4532285, baseEnd_4532285] using wordTrace_append hprefix tailTrace_4532285
  have hstable : (prefixWord ++ tailWord_4532285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532285).length < 2 ^ (prefixWord ++ tailWord_4532285).sum := by decide
  have hdescent : baseEnd_4532285 < baseStart_4532285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532288 : List Nat := [2, 1, 1, 2, 2, 5, 3, 1, 1, 5]
def baseStart_4532288 : Nat := 118140960795 + 4532288 * 2 ^ 59
def prefixEnd_4532288 : Nat := 4983230072969 + 3 ^ 40 * 4532288 * 2
def baseEnd_4532288 : Nat := 775747402868289545352131

theorem tailTrace_4532288 : CollatzResearch.WordTrace tailWord_4532288 prefixEnd_4532288 775747402868289545352131 := by
  unfold tailWord_4532288
  simp only [CollatzResearch.WordTrace]
  refine ⟨82653061902151052004994759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110204082536201402673326345 82653061902151052004994759)
  ·
    refine ⟨123979592853226578007492139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82653061902151052004994759 123979592853226578007492139)
    ·
      refine ⟨185969389279839867011238209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123979592853226578007492139 185969389279839867011238209)
      ·
        refine ⟨139477041959879900258428657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185969389279839867011238209 139477041959879900258428657)
        ·
          refine ⟨104607781469909925193821493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139477041959879900258428657 104607781469909925193821493)
          ·
            refine ⟨9806979512804055486920765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104607781469909925193821493 9806979512804055486920765)
            ·
              refine ⟨3677617317301520807595287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9806979512804055486920765 3677617317301520807595287)
              ·
                refine ⟨5516425975952281211392931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3677617317301520807595287 5516425975952281211392931)
                ·
                  refine ⟨8274638963928421817089397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5516425975952281211392931 8274638963928421817089397)
                  ·
                    refine ⟨775747402868289545352131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8274638963928421817089397 775747402868289545352131)
                    ·
                      rfl

theorem cell23_4532288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 1, 5].length) (baseStart_4532288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532288 prefixEnd_4532288 := by exact prefixLift 4532288
  have htrace : WordTrace (prefixWord ++ tailWord_4532288) baseStart_4532288 baseEnd_4532288 := by
    simpa [prefixWord, tailWord_4532288, baseEnd_4532288] using wordTrace_append hprefix tailTrace_4532288
  have hstable : (prefixWord ++ tailWord_4532288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532288).length < 2 ^ (prefixWord ++ tailWord_4532288).sum := by decide
  have hdescent : baseEnd_4532288 < baseStart_4532288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532301 : List Nat := [1, 6, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_4532301 : Nat := 118140960795 + 4532301 * 2 ^ 59
def prefixEnd_4532301 : Nat := 4983230072969 + 3 ^ 40 * 4532301 * 2
def baseEnd_4532301 : Nat := 775749627951125695064611

theorem tailTrace_4532301 : CollatzResearch.WordTrace tailWord_4532301 prefixEnd_4532301 775749627951125695064611 := by
  unfold tailWord_4532301
  simp only [CollatzResearch.WordTrace]
  refine ⟨165306597953255007230212757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110204398635503338153475171 165306597953255007230212757)
  ·
    refine ⟨7748746779058828463916223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 165306597953255007230212757 7748746779058828463916223)
    ·
      refine ⟨11623120168588242695874335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7748746779058828463916223 11623120168588242695874335)
      ·
        refine ⟨17434680252882364043811503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11623120168588242695874335 17434680252882364043811503)
        ·
          refine ⟨26152020379323546065717255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17434680252882364043811503 26152020379323546065717255)
          ·
            refine ⟨39228030568985319098575883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26152020379323546065717255 39228030568985319098575883)
            ·
              refine ⟨58842045853477978647863825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39228030568985319098575883 58842045853477978647863825)
              ·
                refine ⟨44131534390108483985897869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58842045853477978647863825 44131534390108483985897869)
                ·
                  refine ⟨16549325396290681494711701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44131534390108483985897869 16549325396290681494711701)
                  ·
                    refine ⟨775749627951125695064611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16549325396290681494711701 775749627951125695064611)
                    ·
                      rfl

theorem cell23_4532301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_4532301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532301 prefixEnd_4532301 := by exact prefixLift 4532301
  have htrace : WordTrace (prefixWord ++ tailWord_4532301) baseStart_4532301 baseEnd_4532301 := by
    simpa [prefixWord, tailWord_4532301, baseEnd_4532301] using wordTrace_append hprefix tailTrace_4532301
  have hstable : (prefixWord ++ tailWord_4532301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532301).length < 2 ^ (prefixWord ++ tailWord_4532301).sum := by decide
  have hdescent : baseEnd_4532301 < baseStart_4532301 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532302 : List Nat := [4, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3]
def baseStart_4532302 : Nat := 118140960795 + 4532302 * 2 ^ 59
def prefixEnd_4532302 : Nat := 4983230072969 + 3 ^ 40 * 4532302 * 2
def baseEnd_4532302 : Nat := 2327249397334031581281329

theorem tailTrace_4532302 : CollatzResearch.WordTrace tailWord_4532302 prefixEnd_4532302 2327249397334031581281329 := by
  unfold tailWord_4532302
  simp only [CollatzResearch.WordTrace]
  refine ⟨20663329303281423050124895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110204422950834256267332773 20663329303281423050124895)
  ·
    refine ⟨30994993954922134575187343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20663329303281423050124895 30994993954922134575187343)
    ·
      refine ⟨46492490932383201862781015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30994993954922134575187343 46492490932383201862781015)
      ·
        refine ⟨69738736398574802794171523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46492490932383201862781015 69738736398574802794171523)
        ·
          refine ⟨104608104597862204191257285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69738736398574802794171523 104608104597862204191257285)
          ·
            refine ⟨19614019612099163285860741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104608104597862204191257285 19614019612099163285860741)
            ·
              refine ⟨3677628677268593116098889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19614019612099163285860741 3677628677268593116098889)
              ·
                refine ⟨2758221507951444837074167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3677628677268593116098889 2758221507951444837074167)
                ·
                  refine ⟨4137332261927167255611251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758221507951444837074167 4137332261927167255611251)
                  ·
                    refine ⟨6205998392890750883416877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4137332261927167255611251 6205998392890750883416877)
                    ·
                      refine ⟨2327249397334031581281329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6205998392890750883416877 2327249397334031581281329)
                      ·
                        rfl

theorem cell23_4532302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3].length) (baseStart_4532302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532302 prefixEnd_4532302 := by exact prefixLift 4532302
  have htrace : WordTrace (prefixWord ++ tailWord_4532302) baseStart_4532302 baseEnd_4532302 := by
    simpa [prefixWord, tailWord_4532302, baseEnd_4532302] using wordTrace_append hprefix tailTrace_4532302
  have hstable : (prefixWord ++ tailWord_4532302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532302).length < 2 ^ (prefixWord ++ tailWord_4532302).sum := by decide
  have hdescent : baseEnd_4532302 < baseStart_4532302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532311 : List Nat := [1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 3]
def baseStart_4532311 : Nat := 118140960795 + 4532311 * 2 ^ 59
def prefixEnd_4532311 : Nat := 4983230072969 + 3 ^ 40 * 4532311 * 2
def baseEnd_4532311 : Nat := 2327254018659922046068787

theorem tailTrace_4532311 : CollatzResearch.WordTrace tailWord_4532311 prefixEnd_4532311 2327254018659922046068787 := by
  unfold tailWord_4532311
  simp only [CollatzResearch.WordTrace]
  refine ⟨165306962683218778938076787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110204641788812519292051191 165306962683218778938076787)
  ·
    refine ⟨247960444024828168407115181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165306962683218778938076787 247960444024828168407115181)
    ·
      refine ⟨92985166509310563152668193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247960444024828168407115181 92985166509310563152668193)
      ·
        refine ⟨69738874881982922364501145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92985166509310563152668193 69738874881982922364501145)
        ·
          refine ⟨52304156161487191773375859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69738874881982922364501145 52304156161487191773375859)
          ·
            refine ⟨78456234242230787660063789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52304156161487191773375859 78456234242230787660063789)
            ·
              refine ⟨29421087840836545372523921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78456234242230787660063789 29421087840836545372523921)
              ·
                refine ⟨22065815880627409029392941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29421087840836545372523921 22065815880627409029392941)
                ·
                  refine ⟨8274680955235278386022353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22065815880627409029392941 8274680955235278386022353)
                  ·
                    refine ⟨6206010716426458789516765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8274680955235278386022353 6206010716426458789516765)
                    ·
                      refine ⟨2327254018659922046068787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6206010716426458789516765 2327254018659922046068787)
                      ·
                        rfl

theorem cell23_4532311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_4532311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532311 prefixEnd_4532311 := by exact prefixLift 4532311
  have htrace : WordTrace (prefixWord ++ tailWord_4532311) baseStart_4532311 baseEnd_4532311 := by
    simpa [prefixWord, tailWord_4532311, baseEnd_4532311] using wordTrace_append hprefix tailTrace_4532311
  have hstable : (prefixWord ++ tailWord_4532311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532311).length < 2 ^ (prefixWord ++ tailWord_4532311).sum := by decide
  have hdescent : baseEnd_4532311 < baseStart_4532311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532325 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 3, 2, 2]
def baseStart_4532325 : Nat := 118140960795 + 4532325 * 2 ^ 59
def prefixEnd_4532325 : Nat := 4983230072969 + 3 ^ 40 * 4532325 * 2
def baseEnd_4532325 : Nat := 2327261207389084991293723

theorem tailTrace_4532325 : CollatzResearch.WordTrace tailWord_4532325 prefixEnd_4532325 2327261207389084991293723 := by
  unfold tailWord_4532325
  simp only [CollatzResearch.WordTrace]
  refine ⟨165307473305168059329086429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110204982203445372886057619 165307473305168059329086429)
  ·
    refine ⟨61990302489438022248407411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165307473305168059329086429 61990302489438022248407411)
    ·
      refine ⟨92985453734157033372611117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61990302489438022248407411 92985453734157033372611117)
      ·
        refine ⟨34869545150308887514729169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92985453734157033372611117 34869545150308887514729169)
        ·
          refine ⟨26152158862731665636046877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34869545150308887514729169 26152158862731665636046877)
          ·
            refine ⟨9807059573524374613517579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26152158862731665636046877 9807059573524374613517579)
            ·
              refine ⟨14710589360286561920276369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9807059573524374613517579 14710589360286561920276369)
              ·
                refine ⟨11032942020214921440207277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14710589360286561920276369 11032942020214921440207277)
                ·
                  refine ⟨4137353257580595540077729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11032942020214921440207277 4137353257580595540077729)
                  ·
                    refine ⟨3103014943185446655058297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4137353257580595540077729 3103014943185446655058297)
                    ·
                      refine ⟨2327261207389084991293723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103014943185446655058297 2327261207389084991293723)
                      ·
                        rfl

theorem cell23_4532325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 3, 2, 2].length) (baseStart_4532325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532325 prefixEnd_4532325 := by exact prefixLift 4532325
  have htrace : WordTrace (prefixWord ++ tailWord_4532325) baseStart_4532325 baseEnd_4532325 := by
    simpa [prefixWord, tailWord_4532325, baseEnd_4532325] using wordTrace_append hprefix tailTrace_4532325
  have hstable : (prefixWord ++ tailWord_4532325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532325).length < 2 ^ (prefixWord ++ tailWord_4532325).sum := by decide
  have hdescent : baseEnd_4532325 < baseStart_4532325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532342 : List Nat := [5, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4]
def baseStart_4532342 : Nat := 118140960795 + 4532342 * 2 ^ 59
def prefixEnd_4532342 : Nat := 4983230072969 + 3 ^ 40 * 4532342 * 2
def baseEnd_4532342 : Nat := 2327269936560211424781145

theorem tailTrace_4532342 : CollatzResearch.WordTrace tailWord_4532342 prefixEnd_4532342 2327269936560211424781145 := by
  unfold tailWord_4532342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10331755834131654452028455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110205395564070980821636853 10331755834131654452028455)
  ·
    refine ⟨15497633751197481678042683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10331755834131654452028455 15497633751197481678042683)
    ·
      refine ⟨23246450626796222517064025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15497633751197481678042683 23246450626796222517064025)
      ·
        refine ⟨17434837970097166887798019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23246450626796222517064025 17434837970097166887798019)
        ·
          refine ⟨26152256955145750331697029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17434837970097166887798019 26152256955145750331697029)
          ·
            refine ⟨4903548179089828187193193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26152256955145750331697029 4903548179089828187193193)
            ·
              refine ⟨3677661134317371140394895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4903548179089828187193193 3677661134317371140394895)
              ·
                refine ⟨5516491701476056710592343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3677661134317371140394895 5516491701476056710592343)
                ·
                  refine ⟨8274737552214085065888515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5516491701476056710592343 8274737552214085065888515)
                  ·
                    refine ⟨12412106328321127598832773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8274737552214085065888515 12412106328321127598832773)
                    ·
                      refine ⟨2327269936560211424781145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12412106328321127598832773 2327269936560211424781145)
                      ·
                        rfl

theorem cell23_4532342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_4532342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532342 prefixEnd_4532342 := by exact prefixLift 4532342
  have htrace : WordTrace (prefixWord ++ tailWord_4532342) baseStart_4532342 baseEnd_4532342 := by
    simpa [prefixWord, tailWord_4532342, baseEnd_4532342] using wordTrace_append hprefix tailTrace_4532342
  have hstable : (prefixWord ++ tailWord_4532342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532342).length < 2 ^ (prefixWord ++ tailWord_4532342).sum := by decide
  have hdescent : baseEnd_4532342 < baseStart_4532342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532345 : List Nat := [1, 2, 1, 3, 4, 1, 4, 1, 1, 2, 3]
def baseStart_4532345 : Nat := 118140960795 + 4532345 * 2 ^ 59
def prefixEnd_4532345 : Nat := 4983230072969 + 3 ^ 40 * 4532345 * 2
def baseEnd_4532345 : Nat := 2327271477002174913043631

theorem tailTrace_4532345 : CollatzResearch.WordTrace tailWord_4532345 prefixEnd_4532345 2327271477002174913043631 := by
  unfold tailWord_4532345
  simp only [CollatzResearch.WordTrace]
  refine ⟨165308202765095602744814489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110205468510063735163209659 165308202765095602744814489)
  ·
    refine ⟨123981152073821702058610867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165308202765095602744814489 123981152073821702058610867)
    ·
      refine ⟨185971728110732553087916301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123981152073821702058610867 185971728110732553087916301)
      ·
        refine ⟨69739398041524707407968613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185971728110732553087916301 69739398041524707407968613)
        ·
          refine ⟨13076137132785882638994115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69739398041524707407968613 13076137132785882638994115)
          ·
            refine ⟨19614205699178823958491173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13076137132785882638994115 19614205699178823958491173)
            ·
              refine ⟨3677663568596029492217095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19614205699178823958491173 3677663568596029492217095)
              ·
                refine ⟨5516495352894044238325643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3677663568596029492217095 5516495352894044238325643)
                ·
                  refine ⟨8274743029341066357488465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5516495352894044238325643 8274743029341066357488465)
                  ·
                    refine ⟨6206057272005799768116349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8274743029341066357488465 6206057272005799768116349)
                    ·
                      refine ⟨2327271477002174913043631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6206057272005799768116349 2327271477002174913043631)
                      ·
                        rfl

theorem cell23_4532345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_4532345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532345 prefixEnd_4532345 := by exact prefixLift 4532345
  have htrace : WordTrace (prefixWord ++ tailWord_4532345) baseStart_4532345 baseEnd_4532345 := by
    simpa [prefixWord, tailWord_4532345, baseEnd_4532345] using wordTrace_append hprefix tailTrace_4532345
  have hstable : (prefixWord ++ tailWord_4532345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532345).length < 2 ^ (prefixWord ++ tailWord_4532345).sum := by decide
  have hdescent : baseEnd_4532345 < baseStart_4532345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532372 : List Nat := [2, 4, 2, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_4532372 : Nat := 118140960795 + 4532372 * 2 ^ 59
def prefixEnd_4532372 : Nat := 4983230072969 + 3 ^ 40 * 4532372 * 2
def baseEnd_4532372 : Nat := 2327285340979846307406007

theorem tailTrace_4532372 : CollatzResearch.WordTrace tailWord_4532372 prefixEnd_4532372 2327285340979846307406007 := by
  unfold tailWord_4532372
  simp only [CollatzResearch.WordTrace]
  refine ⟨82654593767998893178023685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110206125023998524237364913 82654593767998893178023685)
  ·
    refine ⟨15497736331499792470879441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82654593767998893178023685 15497736331499792470879441)
    ·
      refine ⟨11623302248624844353159581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15497736331499792470879441 11623302248624844353159581)
      ·
        refine ⟨4358738343234316632434843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11623302248624844353159581 4358738343234316632434843)
        ·
          refine ⟨6538107514851474948652265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4358738343234316632434843 6538107514851474948652265)
          ·
            refine ⟨4903580636138606211489199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6538107514851474948652265 4903580636138606211489199)
            ·
              refine ⟨7355370954207909317233799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4903580636138606211489199 7355370954207909317233799)
              ·
                refine ⟨11033056431311863975850699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7355370954207909317233799 11033056431311863975850699)
                ·
                  refine ⟨16549584646967795963776049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11033056431311863975850699 16549584646967795963776049)
                  ·
                    refine ⟨12412188485225846972832037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16549584646967795963776049 12412188485225846972832037)
                    ·
                      refine ⟨2327285340979846307406007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12412188485225846972832037 2327285340979846307406007)
                      ·
                        rfl

theorem cell23_4532372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_4532372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532372 prefixEnd_4532372 := by exact prefixLift 4532372
  have htrace : WordTrace (prefixWord ++ tailWord_4532372) baseStart_4532372 baseEnd_4532372 := by
    simpa [prefixWord, tailWord_4532372, baseEnd_4532372] using wordTrace_append hprefix tailTrace_4532372
  have hstable : (prefixWord ++ tailWord_4532372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532372).length < 2 ^ (prefixWord ++ tailWord_4532372).sum := by decide
  have hdescent : baseEnd_4532372 < baseStart_4532372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532375 : List Nat := [1, 1, 3, 3, 4, 2, 1, 1, 1, 3, 3]
def baseStart_4532375 : Nat := 118140960795 + 4532375 * 2 ^ 59
def prefixEnd_4532375 : Nat := 4983230072969 + 3 ^ 40 * 4532375 * 2
def baseEnd_4532375 : Nat := 2327286881421809795668493

theorem tailTrace_4532375 : CollatzResearch.WordTrace tailWord_4532375 prefixEnd_4532375 2327286881421809795668493 := by
  unfold tailWord_4532375
  simp only [CollatzResearch.WordTrace]
  refine ⟨165309296954986917868406579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110206197969991278578937719 165309296954986917868406579)
  ·
    refine ⟨247963945432480376802609869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165309296954986917868406579 247963945432480376802609869)
    ·
      refine ⟨92986479537180141300978701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247963945432480376802609869 92986479537180141300978701)
      ·
        refine ⟨34869929826442552987867013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92986479537180141300978701 34869929826442552987867013)
        ·
          refine ⟨6538111842457978685225065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34869929826442552987867013 6538111842457978685225065)
          ·
            refine ⟨4903583881843484013918799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6538111842457978685225065 4903583881843484013918799)
            ·
              refine ⟨7355375822765226020878199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4903583881843484013918799 7355375822765226020878199)
              ·
                refine ⟨11033063734147839031317299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7355375822765226020878199 11033063734147839031317299)
                ·
                  refine ⟨16549595601221758546975949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11033063734147839031317299 16549595601221758546975949)
                  ·
                    refine ⟨6206098350458159455115981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16549595601221758546975949 6206098350458159455115981)
                    ·
                      refine ⟨2327286881421809795668493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6206098350458159455115981 2327286881421809795668493)
                      ·
                        rfl

theorem cell23_4532375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_4532375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532375 prefixEnd_4532375 := by exact prefixLift 4532375
  have htrace : WordTrace (prefixWord ++ tailWord_4532375) baseStart_4532375 baseEnd_4532375 := by
    simpa [prefixWord, tailWord_4532375, baseEnd_4532375] using wordTrace_append hprefix tailTrace_4532375
  have hstable : (prefixWord ++ tailWord_4532375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532375).length < 2 ^ (prefixWord ++ tailWord_4532375).sum := by decide
  have hdescent : baseEnd_4532375 < baseStart_4532375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532382 : List Nat := [4, 3, 1, 1, 4, 1, 2, 7]
def baseStart_4532382 : Nat := 118140960795 + 4532382 * 2 ^ 59
def prefixEnd_4532382 : Nat := 4983230072969 + 3 ^ 40 * 4532382 * 2
def baseEnd_4532382 : Nat := 86195943547644121047443

theorem tailTrace_4532382 : CollatzResearch.WordTrace tailWord_4532382 prefixEnd_4532382 86195943547644121047443 := by
  unfold tailWord_4532382
  simp only [CollatzResearch.WordTrace]
  refine ⟨20663694033245194757988925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110206368177307705375940933 20663694033245194757988925)
  ·
    refine ⟨7748885262466948034245847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20663694033245194757988925 7748885262466948034245847)
    ·
      refine ⟨11623327893700422051368771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7748885262466948034245847 11623327893700422051368771)
      ·
        refine ⟨17434991840550633077053157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11623327893700422051368771 17434991840550633077053157)
        ·
          refine ⟨3269060970103243701947467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17434991840550633077053157 3269060970103243701947467)
          ·
            refine ⟨4903591455154865552921201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269060970103243701947467 4903591455154865552921201)
            ·
              refine ⟨3677693591366149164690901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4903591455154865552921201 3677693591366149164690901)
              ·
                refine ⟨86195943547644121047443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3677693591366149164690901 86195943547644121047443)
                ·
                  rfl

theorem cell23_4532382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 1, 2, 7].length) (baseStart_4532382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532382 prefixEnd_4532382 := by exact prefixLift 4532382
  have htrace : WordTrace (prefixWord ++ tailWord_4532382) baseStart_4532382 baseEnd_4532382 := by
    simpa [prefixWord, tailWord_4532382, baseEnd_4532382] using wordTrace_append hprefix tailTrace_4532382
  have hstable : (prefixWord ++ tailWord_4532382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532382).length < 2 ^ (prefixWord ++ tailWord_4532382).sum := by decide
  have hdescent : baseEnd_4532382 < baseStart_4532382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532385 : List Nat := [1, 2, 3, 3, 1, 2, 1, 4, 1, 3, 2]
def baseStart_4532385 : Nat := 118140960795 + 4532385 * 2 ^ 59
def prefixEnd_4532385 : Nat := 4983230072969 + 3 ^ 40 * 4532385 * 2
def baseEnd_4532385 : Nat := 2327292016228354756543447

theorem tailTrace_4532385 : CollatzResearch.WordTrace tailWord_4532385 prefixEnd_4532385 2327292016228354756543447 := by
  unfold tailWord_4532385
  simp only [CollatzResearch.WordTrace]
  refine ⟨165309661684950689576270609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110206441123300459717513739 165309661684950689576270609)
  ·
    refine ⟨123982246263713017182202957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165309661684950689576270609 123982246263713017182202957)
    ·
      refine ⟨46493342348892381443326109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123982246263713017182202957 46493342348892381443326109)
      ·
        refine ⟨17435003380834643041247291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46493342348892381443326109 17435003380834643041247291)
        ·
          refine ⟨26152505071251964561870937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17435003380834643041247291 26152505071251964561870937)
          ·
            refine ⟨19614378803438973421403203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26152505071251964561870937 19614378803438973421403203)
            ·
              refine ⟨29421568205158460132104805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19614378803438973421403203 29421568205158460132104805)
              ·
                refine ⟨5516544038467211274769651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29421568205158460132104805 5516544038467211274769651)
                ·
                  refine ⟨8274816057700816912154477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5516544038467211274769651 8274816057700816912154477)
                  ·
                    refine ⟨3103056021637806342057929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8274816057700816912154477 3103056021637806342057929)
                    ·
                      refine ⟨2327292016228354756543447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103056021637806342057929 2327292016228354756543447)
                      ·
                        rfl

theorem cell23_4532385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 4, 1, 3, 2].length) (baseStart_4532385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532385 prefixEnd_4532385 := by exact prefixLift 4532385
  have htrace : WordTrace (prefixWord ++ tailWord_4532385) baseStart_4532385 baseEnd_4532385 := by
    simpa [prefixWord, tailWord_4532385, baseEnd_4532385] using wordTrace_append hprefix tailTrace_4532385
  have hstable : (prefixWord ++ tailWord_4532385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532385).length < 2 ^ (prefixWord ++ tailWord_4532385).sum := by decide
  have hdescent : baseEnd_4532385 < baseStart_4532385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532415 : List Nat := [1, 1, 2, 2, 2, 2, 1, 6, 2, 2, 2]
def baseStart_4532415 : Nat := 118140960795 + 4532415 * 2 ^ 59
def prefixEnd_4532415 : Nat := 4983230072969 + 3 ^ 40 * 4532415 * 2
def baseEnd_4532415 : Nat := 2327307420647989639168309

theorem tailTrace_4532415 : CollatzResearch.WordTrace tailWord_4532415 prefixEnd_4532415 2327307420647989639168309 := by
  unfold tailWord_4532415
  simp only [CollatzResearch.WordTrace]
  refine ⟨165310755874842004699862699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110207170583228003133241799 165310755874842004699862699)
  ·
    refine ⟨247966133812263007049794049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165310755874842004699862699 247966133812263007049794049)
    ·
      refine ⟨185974600359197255287345537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247966133812263007049794049 185974600359197255287345537)
      ·
        refine ⟨139480950269397941465509153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185974600359197255287345537 139480950269397941465509153)
        ·
          refine ⟨104610712702048456099131865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139480950269397941465509153 104610712702048456099131865)
          ·
            refine ⟨78458034526536342074348899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104610712702048456099131865 78458034526536342074348899)
            ·
              refine ⟨117687051789804513111523349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78458034526536342074348899 117687051789804513111523349)
              ·
                refine ⟨5516580552647086552102657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117687051789804513111523349 5516580552647086552102657)
                ·
                  refine ⟨4137435414485314914076993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5516580552647086552102657 4137435414485314914076993)
                  ·
                    refine ⟨3103076560863986185557745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4137435414485314914076993 3103076560863986185557745)
                    ·
                      refine ⟨2327307420647989639168309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103076560863986185557745 2327307420647989639168309)
                      ·
                        rfl

theorem cell23_4532415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 2, 2, 2].length) (baseStart_4532415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532415 prefixEnd_4532415 := by exact prefixLift 4532415
  have htrace : WordTrace (prefixWord ++ tailWord_4532415) baseStart_4532415 baseEnd_4532415 := by
    simpa [prefixWord, tailWord_4532415, baseEnd_4532415] using wordTrace_append hprefix tailTrace_4532415
  have hstable : (prefixWord ++ tailWord_4532415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532415).length < 2 ^ (prefixWord ++ tailWord_4532415).sum := by decide
  have hdescent : baseEnd_4532415 < baseStart_4532415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532421 : List Nat := [1, 3, 1, 1, 1, 1, 7, 1, 7]
def baseStart_4532421 : Nat := 118140960795 + 4532421 * 2 ^ 59
def prefixEnd_4532421 : Nat := 4983230072969 + 3 ^ 40 * 4532421 * 2
def baseEnd_4532421 : Nat := 258590055725768512854809

theorem tailTrace_4532421 : CollatzResearch.WordTrace tailWord_4532421 prefixEnd_4532421 258590055725768512854809 := by
  unfold tailWord_4532421
  simp only [CollatzResearch.WordTrace]
  refine ⟨165310974712820267724581117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110207316475213511816387411 165310974712820267724581117)
  ·
    refine ⟨61991615517307600396717919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165310974712820267724581117 61991615517307600396717919)
    ·
      refine ⟨92987423275961400595076879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61991615517307600396717919 92987423275961400595076879)
      ·
        refine ⟨139481134913942100892615319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92987423275961400595076879 139481134913942100892615319)
        ·
          refine ⟨209221702370913151338922979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139481134913942100892615319 209221702370913151338922979)
          ·
            refine ⟨313832553556369727008384469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209221702370913151338922979 313832553556369727008384469)
            ·
              refine ⟨7355450473977415476759011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 313832553556369727008384469 7355450473977415476759011)
              ·
                refine ⟨11033175710966123215138517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7355450473977415476759011 11033175710966123215138517)
                ·
                  refine ⟨258590055725768512854809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11033175710966123215138517 258590055725768512854809)
                  ·
                    rfl

theorem cell23_4532421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 7, 1, 7].length) (baseStart_4532421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532421 prefixEnd_4532421 := by exact prefixLift 4532421
  have htrace : WordTrace (prefixWord ++ tailWord_4532421) baseStart_4532421 baseEnd_4532421 := by
    simpa [prefixWord, tailWord_4532421, baseEnd_4532421] using wordTrace_append hprefix tailTrace_4532421
  have hstable : (prefixWord ++ tailWord_4532421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532421).length < 2 ^ (prefixWord ++ tailWord_4532421).sum := by decide
  have hdescent : baseEnd_4532421 < baseStart_4532421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532431 : List Nat := [1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 3]
def baseStart_4532431 : Nat := 118140960795 + 4532431 * 2 ^ 59
def prefixEnd_4532431 : Nat := 4983230072969 + 3 ^ 40 * 4532431 * 2
def baseEnd_4532431 : Nat := 2327315636338461576568235

theorem tailTrace_4532431 : CollatzResearch.WordTrace tailWord_4532431 prefixEnd_4532431 2327315636338461576568235 := by
  unfold tailWord_4532431
  simp only [CollatzResearch.WordTrace]
  refine ⟨165311339442784039432445147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110207559628522692954963431 165311339442784039432445147)
  ·
    refine ⟨247967009164176059148667721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165311339442784039432445147 247967009164176059148667721)
    ·
      refine ⟨185975256873132044361500791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247967009164176059148667721 185975256873132044361500791)
      ·
        refine ⟨278962885309698066542251187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185975256873132044361500791 278962885309698066542251187)
        ·
          refine ⟨418444327964547099813376781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278962885309698066542251187 418444327964547099813376781)
          ·
            refine ⟨156916622986705162430016293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 418444327964547099813376781 156916622986705162430016293)
            ·
              refine ⟨29421866810007217955628055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 156916622986705162430016293 29421866810007217955628055)
              ·
                refine ⟨44132800215010826933442083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29421866810007217955628055 44132800215010826933442083)
                ·
                  refine ⟨66199200322516240400163125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44132800215010826933442083 66199200322516240400163125)
                  ·
                    refine ⟨6206175030235897537515293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66199200322516240400163125 6206175030235897537515293)
                    ·
                      refine ⟨2327315636338461576568235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6206175030235897537515293 2327315636338461576568235)
                      ·
                        rfl

theorem cell23_4532431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 5, 3].length) (baseStart_4532431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532431 prefixEnd_4532431 := by exact prefixLift 4532431
  have htrace : WordTrace (prefixWord ++ tailWord_4532431) baseStart_4532431 baseEnd_4532431 := by
    simpa [prefixWord, tailWord_4532431, baseEnd_4532431] using wordTrace_append hprefix tailTrace_4532431
  have hstable : (prefixWord ++ tailWord_4532431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532431).length < 2 ^ (prefixWord ++ tailWord_4532431).sum := by decide
  have hdescent : baseEnd_4532431 < baseStart_4532431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532478 : List Nat := [4, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5]
def baseStart_4532478 : Nat := 118140960795 + 4532478 * 2 ^ 59
def prefixEnd_4532478 : Nat := 4983230072969 + 3 ^ 40 * 4532478 * 2
def baseEnd_4532478 : Nat := 2327339769929222892680519

theorem tailTrace_4532478 : CollatzResearch.WordTrace tailWord_4532478 prefixEnd_4532478 2327339769929222892680519 := by
  unfold tailWord_4532478
  simp only [CollatzResearch.WordTrace]
  refine ⟨20664131709201720807425761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110208702449075844306270725 20664131709201720807425761)
  ·
    refine ⟨15498098781901290605569321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20664131709201720807425761 15498098781901290605569321)
    ·
      refine ⟨11623574086425967954176991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15498098781901290605569321 11623574086425967954176991)
      ·
        refine ⟨17435361129638951931265487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11623574086425967954176991 17435361129638951931265487)
        ·
          refine ⟨26153041694458427896898231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17435361129638951931265487 26153041694458427896898231)
          ·
            refine ⟨39229562541687641845347347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26153041694458427896898231 39229562541687641845347347)
            ·
              refine ⟨58844343812531462768021021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39229562541687641845347347 58844343812531462768021021)
              ·
                refine ⟨22066628929699298538007883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58844343812531462768021021 22066628929699298538007883)
                ·
                  refine ⟨33099943394548947807011825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22066628929699298538007883 33099943394548947807011825)
                  ·
                    refine ⟨24824957545911710855258869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33099943394548947807011825 24824957545911710855258869)
                    ·
                      refine ⟨2327339769929222892680519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24824957545911710855258869 2327339769929222892680519)
                      ·
                        rfl

theorem cell23_4532478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_4532478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532478 prefixEnd_4532478 := by exact prefixLift 4532478
  have htrace : WordTrace (prefixWord ++ tailWord_4532478) baseStart_4532478 baseEnd_4532478 := by
    simpa [prefixWord, tailWord_4532478, baseEnd_4532478] using wordTrace_append hprefix tailTrace_4532478
  have hstable : (prefixWord ++ tailWord_4532478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532478).length < 2 ^ (prefixWord ++ tailWord_4532478).sum := by decide
  have hdescent : baseEnd_4532478 < baseStart_4532478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532531 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 8]
def baseStart_4532531 : Nat := 118140960795 + 4532531 * 2 ^ 59
def prefixEnd_4532531 : Nat := 4983230072969 + 3 ^ 40 * 4532531 * 2
def baseEnd_4532531 : Nat := 2327366984403911185317775

theorem tailTrace_4532531 : CollatzResearch.WordTrace tailWord_4532531 prefixEnd_4532531 2327366984403911185317775 := by
  unfold tailWord_4532531
  simp only [CollatzResearch.WordTrace]
  refine ⟨165314986742421756511085447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110209991161614504340723631 165314986742421756511085447)
  ·
    refine ⟨247972480113632634766628171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165314986742421756511085447 247972480113632634766628171)
    ·
      refine ⟨371958720170448952149942257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247972480113632634766628171 371958720170448952149942257)
      ·
        refine ⟨278969040127836714112456693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371958720170448952149942257 278969040127836714112456693)
        ·
          refine ⟨26153347511984691948042815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 278969040127836714112456693 26153347511984691948042815)
          ·
            refine ⟨39230021267977037922064223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26153347511984691948042815 39230021267977037922064223)
            ·
              refine ⟨58845031901965556883096335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39230021267977037922064223 58845031901965556883096335)
              ·
                refine ⟨88267547852948335324644503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58845031901965556883096335 88267547852948335324644503)
                ·
                  refine ⟨132401321779422502986966755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88267547852948335324644503 132401321779422502986966755)
                  ·
                    refine ⟨198601982669133754480450133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 132401321779422502986966755 198601982669133754480450133)
                    ·
                      refine ⟨2327366984403911185317775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 198601982669133754480450133 2327366984403911185317775)
                      ·
                        rfl

theorem cell23_4532531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_4532531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532531 prefixEnd_4532531 := by exact prefixLift 4532531
  have htrace : WordTrace (prefixWord ++ tailWord_4532531) baseStart_4532531 baseEnd_4532531 := by
    simpa [prefixWord, tailWord_4532531, baseEnd_4532531] using wordTrace_append hprefix tailTrace_4532531
  have hstable : (prefixWord ++ tailWord_4532531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532531).length < 2 ^ (prefixWord ++ tailWord_4532531).sum := by decide
  have hdescent : baseEnd_4532531 < baseStart_4532531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532532 : List Nat := [2, 5, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_4532532 : Nat := 118140960795 + 4532532 * 2 ^ 59
def prefixEnd_4532532 : Nat := 4983230072969 + 3 ^ 40 * 4532532 * 2
def baseEnd_4532532 : Nat := 775789165961521893801757

theorem tailTrace_4532532 : CollatzResearch.WordTrace tailWord_4532532 prefixEnd_4532532 775789165961521893801757 := by
  unfold tailWord_4532532
  simp only [CollatzResearch.WordTrace]
  refine ⟨82657511607709066840935925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110210015476945422454581233 82657511607709066840935925)
  ·
    refine ⟨7749141713222725016337743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82657511607709066840935925 7749141713222725016337743)
    ·
      refine ⟨11623712569834087524506615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7749141713222725016337743 11623712569834087524506615)
      ·
        refine ⟨17435568854751131286759923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11623712569834087524506615 17435568854751131286759923)
        ·
          refine ⟨26153353282126696930139885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17435568854751131286759923 26153353282126696930139885)
          ·
            refine ⟨9807507480797511348802457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26153353282126696930139885 9807507480797511348802457)
            ·
              refine ⟨7355630610598133511601843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9807507480797511348802457 7355630610598133511601843)
              ·
                refine ⟨11033445915897200267402765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7355630610598133511601843 11033445915897200267402765)
                ·
                  refine ⟨4137542218461450100276037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11033445915897200267402765 4137542218461450100276037)
                  ·
                    refine ⟨775789165961521893801757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4137542218461450100276037 775789165961521893801757)
                    ·
                      rfl

theorem cell23_4532532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_4532532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532532 prefixEnd_4532532 := by exact prefixLift 4532532
  have htrace : WordTrace (prefixWord ++ tailWord_4532532) baseStart_4532532 baseEnd_4532532 := by
    simpa [prefixWord, tailWord_4532532, baseEnd_4532532] using wordTrace_append hprefix tailTrace_4532532
  have hstable : (prefixWord ++ tailWord_4532532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532532).length < 2 ^ (prefixWord ++ tailWord_4532532).sum := by decide
  have hdescent : baseEnd_4532532 < baseStart_4532532 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532612 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_4532612 : Nat := 118140960795 + 4532612 * 2 ^ 59
def prefixEnd_4532612 : Nat := 4983230072969 + 3 ^ 40 * 4532612 * 2
def baseEnd_4532612 : Nat := 2327408576336925368404903

theorem tailTrace_4532612 : CollatzResearch.WordTrace tailWord_4532612 prefixEnd_4532612 2327408576336925368404903 := by
  unfold tailWord_4532612
  simp only [CollatzResearch.WordTrace]
  refine ⟨82658970527564153672392045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110211960703418871563189393 82658970527564153672392045)
  ·
    refine ⟨30997113947836557627147017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82658970527564153672392045 30997113947836557627147017)
    ·
      refine ⟨23247835460877418220360263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30997113947836557627147017 23247835460877418220360263)
      ·
        refine ⟨34871753191316127330540395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23247835460877418220360263 34871753191316127330540395)
        ·
          refine ⟨52307629786974190995810593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34871753191316127330540395 52307629786974190995810593)
          ·
            refine ⟨39230722340230643246857945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52307629786974190995810593 39230722340230643246857945)
            ·
              refine ⟨29423041755172982435143459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39230722340230643246857945 29423041755172982435143459)
              ·
                refine ⟨44134562632759473652715189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29423041755172982435143459 44134562632759473652715189)
                ·
                  refine ⟨4137615246821200654942049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44134562632759473652715189 4137615246821200654942049)
                  ·
                    refine ⟨3103211435115900491206537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4137615246821200654942049 3103211435115900491206537)
                    ·
                      refine ⟨2327408576336925368404903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103211435115900491206537 2327408576336925368404903)
                      ·
                        rfl

theorem cell23_4532612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_4532612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532612 prefixEnd_4532612 := by exact prefixLift 4532612
  have htrace : WordTrace (prefixWord ++ tailWord_4532612) baseStart_4532612 baseEnd_4532612 := by
    simpa [prefixWord, tailWord_4532612, baseEnd_4532612] using wordTrace_append hprefix tailTrace_4532612
  have hstable : (prefixWord ++ tailWord_4532612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532612).length < 2 ^ (prefixWord ++ tailWord_4532612).sum := by decide
  have hdescent : baseEnd_4532612 < baseStart_4532612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532615 : List Nat := [1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_4532615 : Nat := 118140960795 + 4532615 * 2 ^ 59
def prefixEnd_4532615 : Nat := 4983230072969 + 3 ^ 40 * 4532615 * 2
def baseEnd_4532615 : Nat := 2327410116778888856667389

theorem tailTrace_4532615 : CollatzResearch.WordTrace tailWord_4532615 prefixEnd_4532615 2327410116778888856667389 := by
  unfold tailWord_4532615
  simp only [CollatzResearch.WordTrace]
  refine ⟨165318050474117438857143299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110212033649411625904762199 165318050474117438857143299)
  ·
    refine ⟨247977075711176158285714949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165318050474117438857143299 247977075711176158285714949)
    ·
      refine ⟨46495701695845529678571553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 247977075711176158285714949 46495701695845529678571553)
      ·
        refine ⟨34871776271884147258928665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46495701695845529678571553 34871776271884147258928665)
        ·
          refine ⟨26153832203913110444196499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34871776271884147258928665 26153832203913110444196499)
          ·
            refine ⟨39230748305869665666294749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26153832203913110444196499 39230748305869665666294749)
            ·
              refine ⟨14711530614701124624860531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39230748305869665666294749 14711530614701124624860531)
              ·
                refine ⟨22067295922051686937290797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14711530614701124624860531 22067295922051686937290797)
                ·
                  refine ⟨8275235970769382601484049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22067295922051686937290797 8275235970769382601484049)
                  ·
                    refine ⟨6206426978077036951113037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8275235970769382601484049 6206426978077036951113037)
                    ·
                      refine ⟨2327410116778888856667389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6206426978077036951113037 2327410116778888856667389)
                      ·
                        rfl

theorem cell23_4532615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_4532615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532615 prefixEnd_4532615 := by exact prefixLift 4532615
  have htrace : WordTrace (prefixWord ++ tailWord_4532615) baseStart_4532615 baseEnd_4532615 := by
    simpa [prefixWord, tailWord_4532615, baseEnd_4532615] using wordTrace_append hprefix tailTrace_4532615
  have hstable : (prefixWord ++ tailWord_4532615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532615).length < 2 ^ (prefixWord ++ tailWord_4532615).sum := by decide
  have hdescent : baseEnd_4532615 < baseStart_4532615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532629 : List Nat := [1, 3, 2, 1, 1, 2, 1, 7, 1, 2, 2]
def baseStart_4532629 : Nat := 118140960795 + 4532629 * 2 ^ 59
def prefixEnd_4532629 : Nat := 4983230072969 + 3 ^ 40 * 4532629 * 2
def baseEnd_4532629 : Nat := 2327417305508051801892325

theorem tailTrace_4532629 : CollatzResearch.WordTrace tailWord_4532629 prefixEnd_4532629 2327417305508051801892325 := by
  unfold tailWord_4532629
  simp only [CollatzResearch.WordTrace]
  refine ⟨165318561096066719248152941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110212374064044479498768627 165318561096066719248152941)
  ·
    refine ⟨61994460411025019718057353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165318561096066719248152941 61994460411025019718057353)
    ·
      refine ⟨46495845308268764788543015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61994460411025019718057353 46495845308268764788543015)
      ·
        refine ⟨69743767962403147182814523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46495845308268764788543015 69743767962403147182814523)
        ·
          refine ⟨104615651943604720774221785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69743767962403147182814523 104615651943604720774221785)
          ·
            refine ⟨78461738957703540580666339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104615651943604720774221785 78461738957703540580666339)
            ·
              refine ⟨117692608436555310870999509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78461738957703540580666339 117692608436555310870999509)
              ·
                refine ⟨2758420510231765098539051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 117692608436555310870999509 2758420510231765098539051)
                ·
                  refine ⟨4137630765347647647808577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758420510231765098539051 4137630765347647647808577)
                  ·
                    refine ⟨3103223074010735735856433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4137630765347647647808577 3103223074010735735856433)
                    ·
                      refine ⟨2327417305508051801892325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103223074010735735856433 2327417305508051801892325)
                      ·
                        rfl

theorem cell23_4532629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_4532629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532629 prefixEnd_4532629 := by exact prefixLift 4532629
  have htrace : WordTrace (prefixWord ++ tailWord_4532629) baseStart_4532629 baseEnd_4532629 := by
    simpa [prefixWord, tailWord_4532629, baseEnd_4532629] using wordTrace_append hprefix tailTrace_4532629
  have hstable : (prefixWord ++ tailWord_4532629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532629).length < 2 ^ (prefixWord ++ tailWord_4532629).sum := by decide
  have hdescent : baseEnd_4532629 < baseStart_4532629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532632 : List Nat := [2, 1, 2, 5, 1, 3, 1, 1, 1, 1, 5]
def baseStart_4532632 : Nat := 118140960795 + 4532632 * 2 ^ 59
def prefixEnd_4532632 : Nat := 4983230072969 + 3 ^ 40 * 4532632 * 2
def baseEnd_4532632 : Nat := 2327418845950015290154811

theorem tailTrace_4532632 : CollatzResearch.WordTrace tailWord_4532632 prefixEnd_4532632 2327418845950015290154811 := by
  unfold tailWord_4532632
  simp only [CollatzResearch.WordTrace]
  refine ⟨82659335257527925380256075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110212447010037233840341433 82659335257527925380256075)
  ·
    refine ⟨123989002886291888070384113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82659335257527925380256075 123989002886291888070384113)
    ·
      refine ⟨92991752164718916052788085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123989002886291888070384113 92991752164718916052788085)
      ·
        refine ⟨8717976765442398379948883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92991752164718916052788085 8717976765442398379948883)
        ·
          refine ⟨13076965148163597569923325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8717976765442398379948883 13076965148163597569923325)
          ·
            refine ⟨4903861930561349088721247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13076965148163597569923325 4903861930561349088721247)
            ·
              refine ⟨7355792895842023633081871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4903861930561349088721247 7355792895842023633081871)
              ·
                refine ⟨11033689343763035449622807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7355792895842023633081871 11033689343763035449622807)
                ·
                  refine ⟨16550534015644553174434211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11033689343763035449622807 16550534015644553174434211)
                  ·
                    refine ⟨24825801023466829761651317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16550534015644553174434211 24825801023466829761651317)
                    ·
                      refine ⟨2327418845950015290154811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24825801023466829761651317 2327418845950015290154811)
                      ·
                        rfl

theorem cell23_4532632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_4532632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532632 prefixEnd_4532632 := by exact prefixLift 4532632
  have htrace : WordTrace (prefixWord ++ tailWord_4532632) baseStart_4532632 baseEnd_4532632 := by
    simpa [prefixWord, tailWord_4532632, baseEnd_4532632] using wordTrace_append hprefix tailTrace_4532632
  have hstable : (prefixWord ++ tailWord_4532632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532632).length < 2 ^ (prefixWord ++ tailWord_4532632).sum := by decide
  have hdescent : baseEnd_4532632 < baseStart_4532632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532672 : List Nat := [2, 1, 1, 2, 3, 1, 1, 6, 1, 3, 2]
def baseStart_4532672 : Nat := 118140960795 + 4532672 * 2 ^ 59
def prefixEnd_4532672 : Nat := 4983230072969 + 3 ^ 40 * 4532672 * 2
def baseEnd_4532672 : Nat := 2327439385176195133654627

theorem tailTrace_4532672 : CollatzResearch.WordTrace tailWord_4532672 prefixEnd_4532672 2327439385176195133654627 := by
  unfold tailWord_4532672
  simp only [CollatzResearch.WordTrace]
  refine ⟨82660064717455468795984135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110213419623273958394645513 82660064717455468795984135)
  ·
    refine ⟨123990097076183203193976203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82660064717455468795984135 123990097076183203193976203)
    ·
      refine ⟨185985145614274804790964305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123990097076183203193976203 185985145614274804790964305)
      ·
        refine ⟨139488859210706103593223229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185985145614274804790964305 139488859210706103593223229)
        ·
          refine ⟨52308322204014788847458711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139488859210706103593223229 52308322204014788847458711)
          ·
            refine ⟨78462483306022183271188067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52308322204014788847458711 78462483306022183271188067)
            ·
              refine ⟨117693724959033274906782101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78462483306022183271188067 117693724959033274906782101)
              ·
                refine ⟨5516893357454684761255411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117693724959033274906782101 5516893357454684761255411)
                ·
                  refine ⟨8275340036182027141883117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5516893357454684761255411 8275340036182027141883117)
                  ·
                    refine ⟨3103252513568260178206169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8275340036182027141883117 3103252513568260178206169)
                    ·
                      refine ⟨2327439385176195133654627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103252513568260178206169 2327439385176195133654627)
                      ·
                        rfl

theorem cell23_4532672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 6, 1, 3, 2].length) (baseStart_4532672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532672 prefixEnd_4532672 := by exact prefixLift 4532672
  have htrace : WordTrace (prefixWord ++ tailWord_4532672) baseStart_4532672 baseEnd_4532672 := by
    simpa [prefixWord, tailWord_4532672, baseEnd_4532672] using wordTrace_append hprefix tailTrace_4532672
  have hstable : (prefixWord ++ tailWord_4532672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532672).length < 2 ^ (prefixWord ++ tailWord_4532672).sum := by decide
  have hdescent : baseEnd_4532672 < baseStart_4532672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532755 : List Nat := [1, 1, 1, 2, 1, 5, 3, 2, 2, 5]
def baseStart_4532755 : Nat := 118140960795 + 4532755 * 2 ^ 59
def prefixEnd_4532755 : Nat := 4983230072969 + 3 ^ 40 * 4532755 * 2
def baseEnd_4532755 : Nat := 775827334690172769638915

theorem tailTrace_4532755 : CollatzResearch.WordTrace tailWord_4532755 prefixEnd_4532755 775827334690172769638915 := by
  unfold tailWord_4532755
  simp only [CollatzResearch.WordTrace]
  refine ⟨165323156693610242767239719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110215437795740161844826479 165323156693610242767239719)
  ·
    refine ⟨247984735040415364150859579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165323156693610242767239719 247984735040415364150859579)
    ·
      refine ⟨371977102560623046226289369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247984735040415364150859579 371977102560623046226289369)
      ·
        refine ⟨278982826920467284669717027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 371977102560623046226289369 278982826920467284669717027)
        ·
          refine ⟨418474240380700927004575541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278982826920467284669717027 418474240380700927004575541)
          ·
            refine ⟨39231960035690711906678957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 418474240380700927004575541 39231960035690711906678957)
            ·
              refine ⟨14711985013384016965004609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39231960035690711906678957 14711985013384016965004609)
              ·
                refine ⟨11033988760038012723753457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14711985013384016965004609 11033988760038012723753457)
                ·
                  refine ⟨8275491570028509542815093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11033988760038012723753457 8275491570028509542815093)
                  ·
                    refine ⟨775827334690172769638915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8275491570028509542815093 775827334690172769638915)
                    ·
                      rfl

theorem cell23_4532755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 2, 2, 5].length) (baseStart_4532755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532755 prefixEnd_4532755 := by exact prefixLift 4532755
  have htrace : WordTrace (prefixWord ++ tailWord_4532755) baseStart_4532755 baseEnd_4532755 := by
    simpa [prefixWord, tailWord_4532755, baseEnd_4532755] using wordTrace_append hprefix tailTrace_4532755
  have hstable : (prefixWord ++ tailWord_4532755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532755).length < 2 ^ (prefixWord ++ tailWord_4532755).sum := by decide
  have hdescent : baseEnd_4532755 < baseStart_4532755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532759 : List Nat := [1, 1, 3, 6, 1, 2, 1, 1, 7]
def baseStart_4532759 : Nat := 118140960795 + 4532759 * 2 ^ 59
def prefixEnd_4532759 : Nat := 4983230072969 + 3 ^ 40 * 4532759 * 2
def baseEnd_4532759 : Nat := 258609339777015143696303

theorem tailTrace_4532759 : CollatzResearch.WordTrace tailWord_4532759 prefixEnd_4532759 258609339777015143696303 := by
  unfold tailWord_4532759
  simp only [CollatzResearch.WordTrace]
  refine ⟨165323302585595751450385331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110215535057063834300256887 165323302585595751450385331)
  ·
    refine ⟨247984953878393627175577997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165323302585595751450385331 247984953878393627175577997)
    ·
      refine ⟨92994357704397610190841749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247984953878393627175577997 92994357704397610190841749)
      ·
        refine ⟨4359110517393637977695707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 92994357704397610190841749 4359110517393637977695707)
        ·
          refine ⟨6538665776090456966543561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4359110517393637977695707 6538665776090456966543561)
          ·
            refine ⟨4903999332067842724907671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6538665776090456966543561 4903999332067842724907671)
            ·
              refine ⟨7355998998101764087361507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4903999332067842724907671 7355998998101764087361507)
              ·
                refine ⟨11033998497152646131042261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7355998998101764087361507 11033998497152646131042261)
                ·
                  refine ⟨258609339777015143696303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11033998497152646131042261 258609339777015143696303)
                  ·
                    rfl

theorem cell23_4532759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 2, 1, 1, 7].length) (baseStart_4532759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532759 prefixEnd_4532759 := by exact prefixLift 4532759
  have htrace : WordTrace (prefixWord ++ tailWord_4532759) baseStart_4532759 baseEnd_4532759 := by
    simpa [prefixWord, tailWord_4532759, baseEnd_4532759] using wordTrace_append hprefix tailTrace_4532759
  have hstable : (prefixWord ++ tailWord_4532759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532759).length < 2 ^ (prefixWord ++ tailWord_4532759).sum := by decide
  have hdescent : baseEnd_4532759 < baseStart_4532759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532765 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 7]
def baseStart_4532765 : Nat := 118140960795 + 4532765 * 2 ^ 59
def prefixEnd_4532765 : Nat := 4983230072969 + 3 ^ 40 * 4532765 * 2
def baseEnd_4532765 : Nat := 2327487138877063269791699

theorem tailTrace_4532765 : CollatzResearch.WordTrace tailWord_4532765 prefixEnd_4532765 2327487138877063269791699 := by
  unfold tailWord_4532765
  simp only [CollatzResearch.WordTrace]
  refine ⟨165323521423574014475103749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110215680949049342983402499 165323521423574014475103749)
  ·
    refine ⟨30998160266920127714081953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165323521423574014475103749 30998160266920127714081953)
    ·
      refine ⟨23248620200190095785561465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30998160266920127714081953 23248620200190095785561465)
      ·
        refine ⟨17436465150142571839171099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23248620200190095785561465 17436465150142571839171099)
        ·
          refine ⟨26154697725213857758756649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17436465150142571839171099 26154697725213857758756649)
          ·
            refine ⟨19616023293910393319067487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26154697725213857758756649 19616023293910393319067487)
            ·
              refine ⟨29424034940865589978601231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19616023293910393319067487 29424034940865589978601231)
              ·
                refine ⟨44136052411298384967901847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29424034940865589978601231 44136052411298384967901847)
                ·
                  refine ⟨66204078616947577451852771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44136052411298384967901847 66204078616947577451852771)
                  ·
                    refine ⟨99306117925421366177779157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66204078616947577451852771 99306117925421366177779157)
                    ·
                      refine ⟨2327487138877063269791699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99306117925421366177779157 2327487138877063269791699)
                      ·
                        rfl

theorem cell23_4532765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_4532765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532765 prefixEnd_4532765 := by exact prefixLift 4532765
  have htrace : WordTrace (prefixWord ++ tailWord_4532765) baseStart_4532765 baseEnd_4532765 := by
    simpa [prefixWord, tailWord_4532765, baseEnd_4532765] using wordTrace_append hprefix tailTrace_4532765
  have hstable : (prefixWord ++ tailWord_4532765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532765).length < 2 ^ (prefixWord ++ tailWord_4532765).sum := by decide
  have hdescent : baseEnd_4532765 < baseStart_4532765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532792 : List Nat := [2, 1, 2, 1, 4, 1, 4, 1, 2, 1, 4]
def baseStart_4532792 : Nat := 118140960795 + 4532792 * 2 ^ 59
def prefixEnd_4532792 : Nat := 4983230072969 + 3 ^ 40 * 4532792 * 2
def baseEnd_4532792 : Nat := 2327501002854734664154075

theorem tailTrace_4532792 : CollatzResearch.WordTrace tailWord_4532792 prefixEnd_4532792 2327501002854734664154075 := by
  unfold tailWord_4532792
  simp only [CollatzResearch.WordTrace]
  refine ⟨82662253097238099043168315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110216337462984132057557753 82662253097238099043168315)
  ·
    refine ⟨123993379645857148564752473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82662253097238099043168315 123993379645857148564752473)
    ·
      refine ⟨92995034734392861423564355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123993379645857148564752473 92995034734392861423564355)
      ·
        refine ⟨139492552101589292135346533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92995034734392861423564355 139492552101589292135346533)
        ·
          refine ⟨26154853519047992275377475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139492552101589292135346533 26154853519047992275377475)
          ·
            refine ⟨39232280278571988413066213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26154853519047992275377475 39232280278571988413066213)
            ·
              refine ⟨7356052552232247827449915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39232280278571988413066213 7356052552232247827449915)
              ·
                refine ⟨11034078828348371741174873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7356052552232247827449915 11034078828348371741174873)
                ·
                  refine ⟨8275559121261278805881155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11034078828348371741174873 8275559121261278805881155)
                  ·
                    refine ⟨12413338681891918208821733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8275559121261278805881155 12413338681891918208821733)
                    ·
                      refine ⟨2327501002854734664154075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12413338681891918208821733 2327501002854734664154075)
                      ·
                        rfl

theorem cell23_4532792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_4532792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532792 prefixEnd_4532792 := by exact prefixLift 4532792
  have htrace : WordTrace (prefixWord ++ tailWord_4532792) baseStart_4532792 baseEnd_4532792 := by
    simpa [prefixWord, tailWord_4532792, baseEnd_4532792] using wordTrace_append hprefix tailTrace_4532792
  have hstable : (prefixWord ++ tailWord_4532792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532792).length < 2 ^ (prefixWord ++ tailWord_4532792).sum := by decide
  have hdescent : baseEnd_4532792 < baseStart_4532792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532812 : List Nat := [2, 2, 1, 3, 1, 2, 1, 4, 2, 2, 3]
def baseStart_4532812 : Nat := 118140960795 + 4532812 * 2 ^ 59
def prefixEnd_4532812 : Nat := 4983230072969 + 3 ^ 40 * 4532812 * 2
def baseEnd_4532812 : Nat := 2327511272467824585903983

theorem tailTrace_4532812 : CollatzResearch.WordTrace tailWord_4532812 prefixEnd_4532812 2327511272467824585903983 := by
  unfold tailWord_4532812
  simp only [CollatzResearch.WordTrace]
  refine ⟨82662617827201870751032345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110216823769602494334709793 82662617827201870751032345)
  ·
    refine ⟨61996963370401403063274259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82662617827201870751032345 61996963370401403063274259)
    ·
      refine ⟨92995445055602104594911389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61996963370401403063274259 92995445055602104594911389)
      ·
        refine ⟨34873291895850789223091771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92995445055602104594911389 34873291895850789223091771)
        ·
          refine ⟨52309937843776183834637657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34873291895850789223091771 52309937843776183834637657)
          ·
            refine ⟨39232453382832137875978243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52309937843776183834637657 39232453382832137875978243)
            ·
              refine ⟨58848680074248206813967365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39232453382832137875978243 58848680074248206813967365)
              ·
                refine ⟨11034127513921538777618881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58848680074248206813967365 11034127513921538777618881)
                ·
                  refine ⟨8275595635441154083214161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11034127513921538777618881 8275595635441154083214161)
                  ·
                    refine ⟨6206696726580865562410621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8275595635441154083214161 6206696726580865562410621)
                    ·
                      refine ⟨2327511272467824585903983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6206696726580865562410621 2327511272467824585903983)
                      ·
                        rfl

theorem cell23_4532812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_4532812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532812 prefixEnd_4532812 := by exact prefixLift 4532812
  have htrace : WordTrace (prefixWord ++ tailWord_4532812) baseStart_4532812 baseEnd_4532812 := by
    simpa [prefixWord, tailWord_4532812, baseEnd_4532812] using wordTrace_append hprefix tailTrace_4532812
  have hstable : (prefixWord ++ tailWord_4532812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532812).length < 2 ^ (prefixWord ++ tailWord_4532812).sum := by decide
  have hdescent : baseEnd_4532812 < baseStart_4532812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532815 : List Nat := [1, 1, 2, 1, 1, 2, 5, 4, 6]
def baseStart_4532815 : Nat := 118140960795 + 4532815 * 2 ^ 59
def prefixEnd_4532815 : Nat := 4983230072969 + 3 ^ 40 * 4532815 * 2
def baseEnd_4532815 : Nat := 258612534767754230462941

theorem tailTrace_4532815 : CollatzResearch.WordTrace tailWord_4532815 prefixEnd_4532815 258612534767754230462941 := by
  unfold tailWord_4532815
  simp only [CollatzResearch.WordTrace]
  refine ⟨165325345073392873014423899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110216896715595248676282599 165325345073392873014423899)
  ·
    refine ⟨247988017610089309521635849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165325345073392873014423899 247988017610089309521635849)
    ·
      refine ⟨185991013207566982141226887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 247988017610089309521635849 185991013207566982141226887)
      ·
        refine ⟨278986519811350473211840331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 185991013207566982141226887 278986519811350473211840331)
        ·
          refine ⟨418479779717025709817760497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 278986519811350473211840331 418479779717025709817760497)
          ·
            refine ⟨313859834787769282363320373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418479779717025709817760497 313859834787769282363320373)
            ·
              refine ⟨29424359511353370221561285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 313859834787769282363320373 29424359511353370221561285)
              ·
                refine ⟨5517067408378756916542741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29424359511353370221561285 5517067408378756916542741)
                ·
                  refine ⟨258612534767754230462941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5517067408378756916542741 258612534767754230462941)
                  ·
                    rfl

theorem cell23_4532815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 4, 6].length) (baseStart_4532815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532815 prefixEnd_4532815 := by exact prefixLift 4532815
  have htrace : WordTrace (prefixWord ++ tailWord_4532815) baseStart_4532815 baseEnd_4532815 := by
    simpa [prefixWord, tailWord_4532815, baseEnd_4532815] using wordTrace_append hprefix tailTrace_4532815
  have hstable : (prefixWord ++ tailWord_4532815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532815).length < 2 ^ (prefixWord ++ tailWord_4532815).sum := by decide
  have hdescent : baseEnd_4532815 < baseStart_4532815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532825 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 4, 5, 3]
def baseStart_4532825 : Nat := 118140960795 + 4532825 * 2 ^ 59
def prefixEnd_4532825 : Nat := 4983230072969 + 3 ^ 40 * 4532825 * 2
def baseEnd_4532825 : Nat := 2327517947716333035041423

theorem tailTrace_4532825 : CollatzResearch.WordTrace tailWord_4532825 prefixEnd_4532825 2327517947716333035041423 := by
  unfold tailWord_4532825
  simp only [CollatzResearch.WordTrace]
  refine ⟨165325709803356644722287929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110217139868904429814858619 165325709803356644722287929)
  ·
    refine ⟨123994282352517483541715947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165325709803356644722287929 123994282352517483541715947)
    ·
      refine ⟨185991423528776225312573921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123994282352517483541715947 185991423528776225312573921)
      ·
        refine ⟨139493567646582168984430441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185991423528776225312573921 139493567646582168984430441)
        ·
          refine ⟨104620175734936626738322831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139493567646582168984430441 104620175734936626738322831)
          ·
            refine ⟨156930263602404940107484247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104620175734936626738322831 156930263602404940107484247)
            ·
              refine ⟨235395395403607410161226371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156930263602404940107484247 235395395403607410161226371)
              ·
                refine ⟨353093093105411115241839557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235395395403607410161226371 353093093105411115241839557)
                ·
                  refine ⟨66204954957264584107844917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 353093093105411115241839557 66204954957264584107844917)
                  ·
                    refine ⟨6206714527243554760110461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66204954957264584107844917 6206714527243554760110461)
                    ·
                      refine ⟨2327517947716333035041423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6206714527243554760110461 2327517947716333035041423)
                      ·
                        rfl

theorem cell23_4532825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_4532825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532825 prefixEnd_4532825 := by exact prefixLift 4532825
  have htrace : WordTrace (prefixWord ++ tailWord_4532825) baseStart_4532825 baseEnd_4532825 := by
    simpa [prefixWord, tailWord_4532825, baseEnd_4532825] using wordTrace_append hprefix tailTrace_4532825
  have hstable : (prefixWord ++ tailWord_4532825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532825).length < 2 ^ (prefixWord ++ tailWord_4532825).sum := by decide
  have hdescent : baseEnd_4532825 < baseStart_4532825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532846 : List Nat := [4, 1, 2, 2, 2, 3, 1, 1, 2, 2, 3]
def baseStart_4532846 : Nat := 118140960795 + 4532846 * 2 ^ 59
def prefixEnd_4532846 : Nat := 4983230072969 + 3 ^ 40 * 4532846 * 2
def baseEnd_4532846 : Nat := 2327528730810077452878827

theorem tailTrace_4532846 : CollatzResearch.WordTrace tailWord_4532846 prefixEnd_4532846 2327528730810077452878827 := by
  unfold tailWord_4532846
  simp only [CollatzResearch.WordTrace]
  refine ⟨20665809467035070663600299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110217650490853710205868261 20665809467035070663600299)
  ·
    refine ⟨30998714200552605995400449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20665809467035070663600299 30998714200552605995400449)
    ·
      refine ⟨23249035650414454496550337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30998714200552605995400449 23249035650414454496550337)
      ·
        refine ⟨17436776737810840872412753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23249035650414454496550337 17436776737810840872412753)
        ·
          refine ⟨13077582553358130654309565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17436776737810840872412753 13077582553358130654309565)
          ·
            refine ⟨4904093457509298995366087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13077582553358130654309565 4904093457509298995366087)
            ·
              refine ⟨7356140186263948493049131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4904093457509298995366087 7356140186263948493049131)
              ·
                refine ⟨11034210279395922739573697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7356140186263948493049131 11034210279395922739573697)
                ·
                  refine ⟨8275657709546942054680273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11034210279395922739573697 8275657709546942054680273)
                  ·
                    refine ⟨6206743282160206541010205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8275657709546942054680273 6206743282160206541010205)
                    ·
                      refine ⟨2327528730810077452878827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6206743282160206541010205 2327528730810077452878827)
                      ·
                        rfl

theorem cell23_4532846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_4532846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532846 prefixEnd_4532846 := by exact prefixLift 4532846
  have htrace : WordTrace (prefixWord ++ tailWord_4532846) baseStart_4532846 baseEnd_4532846 := by
    simpa [prefixWord, tailWord_4532846, baseEnd_4532846] using wordTrace_append hprefix tailTrace_4532846
  have hstable : (prefixWord ++ tailWord_4532846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532846).length < 2 ^ (prefixWord ++ tailWord_4532846).sum := by decide
  have hdescent : baseEnd_4532846 < baseStart_4532846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532853 : List Nat := [1, 3, 4, 2, 2, 1, 2, 3, 1, 4]
def baseStart_4532853 : Nat := 118140960795 + 4532853 * 2 ^ 59
def prefixEnd_4532853 : Nat := 4983230072969 + 3 ^ 40 * 4532853 * 2
def baseEnd_4532853 : Nat := 775844108391552975163765

theorem tailTrace_4532853 : CollatzResearch.WordTrace tailWord_4532853 prefixEnd_4532853 775844108391552975163765 := by
  unfold tailWord_4532853
  simp only [CollatzResearch.WordTrace]
  refine ⟨165326731047255205504307213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110217820698170137002871475 165326731047255205504307213)
  ·
    refine ⟨61997524142720702064115205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165326731047255205504307213 61997524142720702064115205)
    ·
      refine ⟨11624535776760131637021601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61997524142720702064115205 11624535776760131637021601)
      ·
        refine ⟨8718401832570098727766201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11624535776760131637021601 8718401832570098727766201)
        ·
          refine ⟨6538801374427574045824651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8718401832570098727766201 6538801374427574045824651)
          ·
            refine ⟨9808202061641361068736977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6538801374427574045824651 9808202061641361068736977)
            ·
              refine ⟨7356151546231020801552733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9808202061641361068736977 7356151546231020801552733)
              ·
                refine ⟨2758556829836632800582275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7356151546231020801552733 2758556829836632800582275)
                ·
                  refine ⟨4137835244754949200873413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758556829836632800582275 4137835244754949200873413)
                  ·
                    refine ⟨775844108391552975163765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4137835244754949200873413 775844108391552975163765)
                    ·
                      rfl

theorem cell23_4532853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_4532853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532853 prefixEnd_4532853 := by exact prefixLift 4532853
  have htrace : WordTrace (prefixWord ++ tailWord_4532853) baseStart_4532853 baseEnd_4532853 := by
    simpa [prefixWord, tailWord_4532853, baseEnd_4532853] using wordTrace_append hprefix tailTrace_4532853
  have hstable : (prefixWord ++ tailWord_4532853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532853).length < 2 ^ (prefixWord ++ tailWord_4532853).sum := by decide
  have hdescent : baseEnd_4532853 < baseStart_4532853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532899 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 5, 2, 2]
def baseStart_4532899 : Nat := 118140960795 + 4532899 * 2 ^ 59
def prefixEnd_4532899 : Nat := 4983230072969 + 3 ^ 40 * 4532899 * 2
def baseEnd_4532899 : Nat := 2327555945284765745516083

theorem tailTrace_4532899 : CollatzResearch.WordTrace tailWord_4532899 prefixEnd_4532899 2327555945284765745516083 := by
  unfold tailWord_4532899
  simp only [CollatzResearch.WordTrace]
  refine ⟨165328408805088555360481751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110218939203392370240321167 165328408805088555360481751)
  ·
    refine ⟨247992613207632833040722627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165328408805088555360481751 247992613207632833040722627)
    ·
      refine ⟨371988919811449249561083941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 247992613207632833040722627 371988919811449249561083941)
      ·
        refine ⟨69747922464646734292703239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 371988919811449249561083941 69747922464646734292703239)
        ·
          refine ⟨104621883696970101439054859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69747922464646734292703239 104621883696970101439054859)
          ·
            refine ⟨156932825545455152158582289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104621883696970101439054859 156932825545455152158582289)
            ·
              refine ⟨117699619159091364118936717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156932825545455152158582289 117699619159091364118936717)
              ·
                refine ⟨44137357184659261544601269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117699619159091364118936717 44137357184659261544601269)
                ·
                  refine ⟨4137877236061805769806369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44137357184659261544601269 4137877236061805769806369)
                  ·
                    refine ⟨3103407927046354327354777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4137877236061805769806369 3103407927046354327354777)
                    ·
                      refine ⟨2327555945284765745516083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103407927046354327354777 2327555945284765745516083)
                      ·
                        rfl

theorem cell23_4532899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_4532899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532899 prefixEnd_4532899 := by exact prefixLift 4532899
  have htrace : WordTrace (prefixWord ++ tailWord_4532899) baseStart_4532899 baseEnd_4532899 := by
    simpa [prefixWord, tailWord_4532899, baseEnd_4532899] using wordTrace_append hprefix tailTrace_4532899
  have hstable : (prefixWord ++ tailWord_4532899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532899).length < 2 ^ (prefixWord ++ tailWord_4532899).sum := by decide
  have hdescent : baseEnd_4532899 < baseStart_4532899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532909 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_4532909 : Nat := 118140960795 + 4532909 * 2 ^ 59
def prefixEnd_4532909 : Nat := 4983230072969 + 3 ^ 40 * 4532909 * 2
def baseEnd_4532909 : Nat := 775853693363770235463679

theorem tailTrace_4532909 : CollatzResearch.WordTrace tailWord_4532909 prefixEnd_4532909 775853693363770235463679 := by
  unfold tailWord_4532909
  simp only [CollatzResearch.WordTrace]
  refine ⟨165328773535052327068345781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110219182356701551378897187 165328773535052327068345781)
  ·
    refine ⟨15499572518911155662657417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165328773535052327068345781 15499572518911155662657417)
    ·
      refine ⟨11624679389183366746993063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15499572518911155662657417 11624679389183366746993063)
      ·
        refine ⟨17437019083775050120489595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11624679389183366746993063 17437019083775050120489595)
        ·
          refine ⟨26155528625662575180734393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17437019083775050120489595 26155528625662575180734393)
          ·
            refine ⟨19616646469246931385550795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26155528625662575180734393 19616646469246931385550795)
            ·
              refine ⟨29424969703870397078326193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19616646469246931385550795 29424969703870397078326193)
              ·
                refine ⟨22068727277902797808744645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29424969703870397078326193 22068727277902797808744645)
                ·
                  refine ⟨4137886364606774589139621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22068727277902797808744645 4137886364606774589139621)
                  ·
                    refine ⟨775853693363770235463679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4137886364606774589139621 775853693363770235463679)
                    ·
                      rfl

theorem cell23_4532909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_4532909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532909 prefixEnd_4532909 := by exact prefixLift 4532909
  have htrace : WordTrace (prefixWord ++ tailWord_4532909) baseStart_4532909 baseEnd_4532909 := by
    simpa [prefixWord, tailWord_4532909, baseEnd_4532909] using wordTrace_append hprefix tailTrace_4532909
  have hstable : (prefixWord ++ tailWord_4532909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532909).length < 2 ^ (prefixWord ++ tailWord_4532909).sum := by decide
  have hdescent : baseEnd_4532909 < baseStart_4532909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532910 : List Nat := [4, 1, 4, 1, 1, 1, 3, 3, 1, 1, 3]
def baseStart_4532910 : Nat := 118140960795 + 4532910 * 2 ^ 59
def prefixEnd_4532910 : Nat := 4983230072969 + 3 ^ 40 * 4532910 * 2
def baseEnd_4532910 : Nat := 2327561593571965202478533

theorem tailTrace_4532910 : CollatzResearch.WordTrace tailWord_4532910 prefixEnd_4532910 2327561593571965202478533 := by
  unfold tailWord_4532910
  simp only [CollatzResearch.WordTrace]
  refine ⟨20666101251006088029891523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110219206672032469492754789 20666101251006088029891523)
  ·
    refine ⟨30999151876509132044837285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20666101251006088029891523 30999151876509132044837285)
    ·
      refine ⟨5812340976845462258406991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30999151876509132044837285 5812340976845462258406991)
      ·
        refine ⟨8718511465268193387610487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5812340976845462258406991 8718511465268193387610487)
        ·
          refine ⟨13077767197902290081415731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8718511465268193387610487 13077767197902290081415731)
          ·
            refine ⟨19616650796853435122123597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13077767197902290081415731 19616650796853435122123597)
            ·
              refine ⟨7356244048820038170796349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19616650796853435122123597 7356244048820038170796349)
              ·
                refine ⟨2758591518307514314048631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7356244048820038170796349 2758591518307514314048631)
                ·
                  refine ⟨4137887277461271471072947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758591518307514314048631 4137887277461271471072947)
                  ·
                    refine ⟨6206830916191907206609421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4137887277461271471072947 6206830916191907206609421)
                    ·
                      refine ⟨2327561593571965202478533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6206830916191907206609421 2327561593571965202478533)
                      ·
                        rfl

theorem cell23_4532910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_4532910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532910 prefixEnd_4532910 := by exact prefixLift 4532910
  have htrace : WordTrace (prefixWord ++ tailWord_4532910) baseStart_4532910 baseEnd_4532910 := by
    simpa [prefixWord, tailWord_4532910, baseEnd_4532910] using wordTrace_append hprefix tailTrace_4532910
  have hstable : (prefixWord ++ tailWord_4532910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532910).length < 2 ^ (prefixWord ++ tailWord_4532910).sum := by decide
  have hdescent : baseEnd_4532910 < baseStart_4532910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532919 : List Nat := [1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 5]
def baseStart_4532919 : Nat := 118140960795 + 4532919 * 2 ^ 59
def prefixEnd_4532919 : Nat := 4983230072969 + 3 ^ 40 * 4532919 * 2
def baseEnd_4532919 : Nat := 2327566214897855667265991

theorem tailTrace_4532919 : CollatzResearch.WordTrace tailWord_4532919 prefixEnd_4532919 2327566214897855667265991 := by
  unfold tailWord_4532919
  simp only [CollatzResearch.WordTrace]
  refine ⟨165329138265016098776209811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110219425510010732517473207 165329138265016098776209811)
  ·
    refine ⟨247993707397524148164314717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165329138265016098776209811 247993707397524148164314717)
    ·
      refine ⟨92997640274071555561618019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 247993707397524148164314717 92997640274071555561618019)
      ·
        refine ⟨139496460411107333342427029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92997640274071555561618019 139496460411107333342427029)
        ·
          refine ⟨6538896581770656250426267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 139496460411107333342427029 6538896581770656250426267)
          ·
            refine ⟨9808344872655984375639401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6538896581770656250426267 9808344872655984375639401)
            ·
              refine ⟨7356258654491988281729551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9808344872655984375639401 7356258654491988281729551)
              ·
                refine ⟨11034387981737982422594327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7356258654491988281729551 11034387981737982422594327)
                ·
                  refine ⟨16551581972606973633891491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11034387981737982422594327 16551581972606973633891491)
                  ·
                    refine ⟨24827372958910460450837237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16551581972606973633891491 24827372958910460450837237)
                    ·
                      refine ⟨2327566214897855667265991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24827372958910460450837237 2327566214897855667265991)
                      ·
                        rfl

theorem cell23_4532919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_4532919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532919 prefixEnd_4532919 := by exact prefixLift 4532919
  have htrace : WordTrace (prefixWord ++ tailWord_4532919) baseStart_4532919 baseEnd_4532919 := by
    simpa [prefixWord, tailWord_4532919, baseEnd_4532919] using wordTrace_append hprefix tailTrace_4532919
  have hstable : (prefixWord ++ tailWord_4532919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532919).length < 2 ^ (prefixWord ++ tailWord_4532919).sum := by decide
  have hdescent : baseEnd_4532919 < baseStart_4532919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532989 : List Nat := [1, 4, 1, 1, 1, 1, 3, 2, 3, 4, 2]
def baseStart_4532989 : Nat := 118140960795 + 4532989 * 2 ^ 59
def prefixEnd_4532989 : Nat := 4983230072969 + 3 ^ 40 * 4532989 * 2
def baseEnd_4532989 : Nat := 2327602158543670393390669

theorem tailTrace_4532989 : CollatzResearch.WordTrace tailWord_4532989 prefixEnd_4532989 2327602158543670393390669 := by
  unfold tailWord_4532989
  simp only [CollatzResearch.WordTrace]
  refine ⟨165331691374762500731258021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110221127583175000487505347 165331691374762500731258021)
  ·
    refine ⟨30999692132767968887110879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165331691374762500731258021 30999692132767968887110879)
    ·
      refine ⟨46499538199151953330666319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30999692132767968887110879 46499538199151953330666319)
      ·
        refine ⟨69749307298727929995999479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46499538199151953330666319 69749307298727929995999479)
        ·
          refine ⟨104623960948091894993999219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69749307298727929995999479 104623960948091894993999219)
          ·
            refine ⟨156935941422137842490998829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104623960948091894993999219 156935941422137842490998829)
            ·
              refine ⟨58850978033301690934124561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156935941422137842490998829 58850978033301690934124561)
              ·
                refine ⟨44138233524976268200593421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58850978033301690934124561 44138233524976268200593421)
                ·
                  refine ⟨16551837571866100575222533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44138233524976268200593421 16551837571866100575222533)
                  ·
                    refine ⟨3103469544724893857854225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16551837571866100575222533 3103469544724893857854225)
                    ·
                      refine ⟨2327602158543670393390669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103469544724893857854225 2327602158543670393390669)
                      ·
                        rfl

theorem cell23_4532989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 2, 3, 4, 2].length) (baseStart_4532989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532989 prefixEnd_4532989 := by exact prefixLift 4532989
  have htrace : WordTrace (prefixWord ++ tailWord_4532989) baseStart_4532989 baseEnd_4532989 := by
    simpa [prefixWord, tailWord_4532989, baseEnd_4532989] using wordTrace_append hprefix tailTrace_4532989
  have hstable : (prefixWord ++ tailWord_4532989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532989).length < 2 ^ (prefixWord ++ tailWord_4532989).sum := by decide
  have hdescent : baseEnd_4532989 < baseStart_4532989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4532999 : List Nat := [1, 1, 4, 4, 1, 2, 1, 1, 2, 6]
def baseStart_4532999 : Nat := 118140960795 + 4532999 * 2 ^ 59
def prefixEnd_4532999 : Nat := 4983230072969 + 3 ^ 40 * 4532999 * 2
def baseEnd_4532999 : Nat := 775869097783405118088541

theorem tailTrace_4532999 : CollatzResearch.WordTrace tailWord_4532999 prefixEnd_4532999 775869097783405118088541 := by
  unfold tailWord_4532999
  simp only [CollatzResearch.WordTrace]
  refine ⟨165332056104726272439122051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110221370736484181626081367 165332056104726272439122051)
  ·
    refine ⟨247998084157089408658683077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165332056104726272439122051 247998084157089408658683077)
    ·
      refine ⟨46499640779454264123503077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 247998084157089408658683077 46499640779454264123503077)
      ·
        refine ⟨8718682646147674523156827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46499640779454264123503077 8718682646147674523156827)
        ·
          refine ⟨13078023969221511784735241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8718682646147674523156827 13078023969221511784735241)
          ·
            refine ⟨9808517976916133838551431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13078023969221511784735241 9808517976916133838551431)
            ·
              refine ⟨14712776965374200757827147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9808517976916133838551431 14712776965374200757827147)
              ·
                refine ⟨22069165448061301136740721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14712776965374200757827147 22069165448061301136740721)
                ·
                  refine ⟨16551874086045975852555541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22069165448061301136740721 16551874086045975852555541)
                  ·
                    refine ⟨775869097783405118088541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16551874086045975852555541 775869097783405118088541)
                    ·
                      rfl

theorem cell23_4532999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_4532999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4532999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4532999 prefixEnd_4532999 := by exact prefixLift 4532999
  have htrace : WordTrace (prefixWord ++ tailWord_4532999) baseStart_4532999 baseEnd_4532999 := by
    simpa [prefixWord, tailWord_4532999, baseEnd_4532999] using wordTrace_append hprefix tailTrace_4532999
  have hstable : (prefixWord ++ tailWord_4532999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4532999).length < 2 ^ (prefixWord ++ tailWord_4532999).sum := by decide
  have hdescent : baseEnd_4532999 < baseStart_4532999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4532999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533006 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2]
def baseStart_4533006 : Nat := 118140960795 + 4533006 * 2 ^ 59
def prefixEnd_4533006 : Nat := 4983230072969 + 3 ^ 40 * 4533006 * 2
def baseEnd_4533006 : Nat := 2327610887714796826878091

theorem tailTrace_4533006 : CollatzResearch.WordTrace tailWord_4533006 prefixEnd_4533006 2327610887714796826878091 := by
  unfold tailWord_4533006
  simp only [CollatzResearch.WordTrace]
  refine ⟨20666538926962614079328359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110221540943800608423084581 20666538926962614079328359)
  ·
    refine ⟨30999808390443921118992539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20666538926962614079328359 30999808390443921118992539)
    ·
      refine ⟨46499712585665881678488809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30999808390443921118992539 46499712585665881678488809)
      ·
        refine ⟨34874784439249411258866607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46499712585665881678488809 34874784439249411258866607)
        ·
          refine ⟨52312176658874116888299911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34874784439249411258866607 52312176658874116888299911)
          ·
            refine ⟨78468264988311175332449867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52312176658874116888299911 78468264988311175332449867)
            ·
              refine ⟨117702397482466762998674801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78468264988311175332449867 117702397482466762998674801)
              ·
                refine ⟨88276798111850072249006101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117702397482466762998674801 88276798111850072249006101)
                ·
                  refine ⟨4137974911492972136672161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88276798111850072249006101 4137974911492972136672161)
                  ·
                    refine ⟨3103481183619729102504121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4137974911492972136672161 3103481183619729102504121)
                    ·
                      refine ⟨2327610887714796826878091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103481183619729102504121 2327610887714796826878091)
                      ·
                        rfl

theorem cell23_4533006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 6, 2, 2].length) (baseStart_4533006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533006 prefixEnd_4533006 := by exact prefixLift 4533006
  have htrace : WordTrace (prefixWord ++ tailWord_4533006) baseStart_4533006 baseEnd_4533006 := by
    simpa [prefixWord, tailWord_4533006, baseEnd_4533006] using wordTrace_append hprefix tailTrace_4533006
  have hstable : (prefixWord ++ tailWord_4533006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533006).length < 2 ^ (prefixWord ++ tailWord_4533006).sum := by decide
  have hdescent : baseEnd_4533006 < baseStart_4533006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533052 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_4533052 : Nat := 118140960795 + 4533052 * 2 ^ 59
def prefixEnd_4533052 : Nat := 4983230072969 + 3 ^ 40 * 4533052 * 2
def baseEnd_4533052 : Nat := 2327634507824903646902879

theorem tailTrace_4533052 : CollatzResearch.WordTrace tailWord_4533052 prefixEnd_4533052 2327634507824903646902879 := by
  unfold tailWord_4533052
  simp only [CollatzResearch.WordTrace]
  refine ⟨82666994586767131245400705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110222659449022841660534273 82666994586767131245400705)
  ·
    refine ⟨62000245940075348434050529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82666994586767131245400705 62000245940075348434050529)
    ·
      refine ⟨46500184455056511325537897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62000245940075348434050529 46500184455056511325537897)
      ·
        refine ⟨34875138341292383494153423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46500184455056511325537897 34875138341292383494153423)
        ·
          refine ⟨52312707511938575241230135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34875138341292383494153423 52312707511938575241230135)
          ·
            refine ⟨78469061267907862861845203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52312707511938575241230135 78469061267907862861845203)
            ·
              refine ⟨117703591901861794292767805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78469061267907862861845203 117703591901861794292767805)
              ·
                refine ⟨44138846963198172859787927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117703591901861794292767805 44138846963198172859787927)
                ·
                  refine ⟨66208270444797259289681891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44138846963198172859787927 66208270444797259289681891)
                  ·
                    refine ⟨99312405667195888934522837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66208270444797259289681891 99312405667195888934522837)
                    ·
                      refine ⟨2327634507824903646902879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99312405667195888934522837 2327634507824903646902879)
                      ·
                        rfl

theorem cell23_4533052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_4533052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533052 prefixEnd_4533052 := by exact prefixLift 4533052
  have htrace : WordTrace (prefixWord ++ tailWord_4533052) baseStart_4533052 baseEnd_4533052 := by
    simpa [prefixWord, tailWord_4533052, baseEnd_4533052] using wordTrace_append hprefix tailTrace_4533052
  have hstable : (prefixWord ++ tailWord_4533052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533052).length < 2 ^ (prefixWord ++ tailWord_4533052).sum := by decide
  have hdescent : baseEnd_4533052 < baseStart_4533052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533057 : List Nat := [1, 2, 5, 3, 2, 1, 1, 1, 1, 4, 2]
def baseStart_4533057 : Nat := 118140960795 + 4533057 * 2 ^ 59
def prefixEnd_4533057 : Nat := 4983230072969 + 3 ^ 40 * 4533057 * 2
def baseEnd_4533057 : Nat := 2327637075228176127340357

theorem tailTrace_4533057 : CollatzResearch.WordTrace tailWord_4533057 prefixEnd_4533057 2327637075228176127340357 := by
  unfold tailWord_4533057
  simp only [CollatzResearch.WordTrace]
  refine ⟨165334171538516148344733425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110222781025677432229822283 165334171538516148344733425)
  ·
    refine ⟨124000628653887111258550069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165334171538516148344733425 124000628653887111258550069)
    ·
      refine ⟨11625058936301916680489069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124000628653887111258550069 11625058936301916680489069)
      ·
        refine ⟨4359397101113218755183401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11625058936301916680489069 4359397101113218755183401)
        ·
          refine ⟨3269547825834914066387551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4359397101113218755183401 3269547825834914066387551)
          ·
            refine ⟨4904321738752371099581327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269547825834914066387551 4904321738752371099581327)
            ·
              refine ⟨7356482608128556649371991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4904321738752371099581327 7356482608128556649371991)
              ·
                refine ⟨11034723912192834974057987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7356482608128556649371991 11034723912192834974057987)
                ·
                  refine ⟨16552085868289252461086981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11034723912192834974057987 16552085868289252461086981)
                  ·
                    refine ⟨3103516100304234836453809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16552085868289252461086981 3103516100304234836453809)
                    ·
                      refine ⟨2327637075228176127340357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103516100304234836453809 2327637075228176127340357)
                      ·
                        rfl

theorem cell23_4533057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_4533057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533057 prefixEnd_4533057 := by exact prefixLift 4533057
  have htrace : WordTrace (prefixWord ++ tailWord_4533057) baseStart_4533057 baseEnd_4533057 := by
    simpa [prefixWord, tailWord_4533057, baseEnd_4533057] using wordTrace_append hprefix tailTrace_4533057
  have hstable : (prefixWord ++ tailWord_4533057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533057).length < 2 ^ (prefixWord ++ tailWord_4533057).sum := by decide
  have hdescent : baseEnd_4533057 < baseStart_4533057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533079 : List Nat := [1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 4]
def baseStart_4533079 : Nat := 118140960795 + 4533079 * 2 ^ 59
def prefixEnd_4533079 : Nat := 4983230072969 + 3 ^ 40 * 4533079 * 2
def baseEnd_4533079 : Nat := 2327648371802575041265255

theorem tailTrace_4533079 : CollatzResearch.WordTrace tailWord_4533079 prefixEnd_4533079 2327648371802575041265255 := by
  unfold tailWord_4533079
  simp only [CollatzResearch.WordTrace]
  refine ⟨165334973944436446102034291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110223315962957630734689527 165334973944436446102034291)
  ·
    refine ⟨248002460916654669153051437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165334973944436446102034291 248002460916654669153051437)
    ·
      refine ⟨93000922843745500932394289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248002460916654669153051437 93000922843745500932394289)
      ·
        refine ⟨69750692132809125699295717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93000922843745500932394289 69750692132809125699295717)
        ·
          refine ⟨13078254774901711068617947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69750692132809125699295717 13078254774901711068617947)
          ·
            refine ⟨19617382162352566602926921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13078254774901711068617947 19617382162352566602926921)
            ·
              refine ⟨14713036621764424952195191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19617382162352566602926921 14713036621764424952195191)
              ·
                refine ⟨22069554932646637428292787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14713036621764424952195191 22069554932646637428292787)
                ·
                  refine ⟨33104332398969956142439181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22069554932646637428292787 33104332398969956142439181)
                  ·
                    refine ⟨12414124649613733553414693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33104332398969956142439181 12414124649613733553414693)
                    ·
                      refine ⟨2327648371802575041265255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12414124649613733553414693 2327648371802575041265255)
                      ·
                        rfl

theorem cell23_4533079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_4533079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533079 prefixEnd_4533079 := by exact prefixLift 4533079
  have htrace : WordTrace (prefixWord ++ tailWord_4533079) baseStart_4533079 baseEnd_4533079 := by
    simpa [prefixWord, tailWord_4533079, baseEnd_4533079] using wordTrace_append hprefix tailTrace_4533079
  have hstable : (prefixWord ++ tailWord_4533079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533079).length < 2 ^ (prefixWord ++ tailWord_4533079).sum := by decide
  have hdescent : baseEnd_4533079 < baseStart_4533079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533096 : List Nat := [2, 1, 4, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_4533096 : Nat := 118140960795 + 4533096 * 2 ^ 59
def prefixEnd_4533096 : Nat := 4983230072969 + 3 ^ 40 * 4533096 * 2
def baseEnd_4533096 : Nat := 2327657100973701474752677

theorem tailTrace_4533096 : CollatzResearch.WordTrace tailWord_4533096 prefixEnd_4533096 2327657100973701474752677 := by
  unfold tailWord_4533096
  simp only [CollatzResearch.WordTrace]
  refine ⟨82667796992687429002701571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110223729323583238670268761 82667796992687429002701571)
  ·
    refine ⟨124001695489031143504052357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82667796992687429002701571 124001695489031143504052357)
    ·
      refine ⟨23250317904193339407009817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124001695489031143504052357 23250317904193339407009817)
      ·
        refine ⟨17437738428145004555257363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23250317904193339407009817 17437738428145004555257363)
        ·
          refine ⟨26156607642217506832886045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17437738428145004555257363 26156607642217506832886045)
          ·
            refine ⟨9808727865831565062332267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26156607642217506832886045 9808727865831565062332267)
            ·
              refine ⟨14713091798747347593498401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9808727865831565062332267 14713091798747347593498401)
              ·
                refine ⟨11034818849060510695123801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14713091798747347593498401 11034818849060510695123801)
                ·
                  refine ⟨8276114136795383021342851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11034818849060510695123801 8276114136795383021342851)
                  ·
                    refine ⟨12414171205193074532014277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8276114136795383021342851 12414171205193074532014277)
                    ·
                      refine ⟨2327657100973701474752677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12414171205193074532014277 2327657100973701474752677)
                      ·
                        rfl

theorem cell23_4533096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_4533096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533096 prefixEnd_4533096 := by exact prefixLift 4533096
  have htrace : WordTrace (prefixWord ++ tailWord_4533096) baseStart_4533096 baseEnd_4533096 := by
    simpa [prefixWord, tailWord_4533096, baseEnd_4533096] using wordTrace_append hprefix tailTrace_4533096
  have hstable : (prefixWord ++ tailWord_4533096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533096).length < 2 ^ (prefixWord ++ tailWord_4533096).sum := by decide
  have hdescent : baseEnd_4533096 < baseStart_4533096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533099 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 3]
def baseStart_4533099 : Nat := 118140960795 + 4533099 * 2 ^ 59
def prefixEnd_4533099 : Nat := 4983230072969 + 3 ^ 40 * 4533099 * 2
def baseEnd_4533099 : Nat := 2327658641415664963015163

theorem tailTrace_4533099 : CollatzResearch.WordTrace tailWord_4533099 prefixEnd_4533099 2327658641415664963015163 := by
  unfold tailWord_4533099
  simp only [CollatzResearch.WordTrace]
  refine ⟨165335703404363989517762351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110223802269575993011841567 165335703404363989517762351)
  ·
    refine ⟨248003555106545984276643527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165335703404363989517762351 248003555106545984276643527)
    ·
      refine ⟨372005332659818976414965291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248003555106545984276643527 372005332659818976414965291)
      ·
        refine ⟨558007998989728464622447937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372005332659818976414965291 558007998989728464622447937)
        ·
          refine ⟨418505999242296348466835953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558007998989728464622447937 418505999242296348466835953)
          ·
            refine ⟨313879499431722261350126965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418505999242296348466835953 313879499431722261350126965)
            ·
              refine ⟨29426203071723962001574403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 313879499431722261350126965 29426203071723962001574403)
              ·
                refine ⟨44139304607585943002361605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29426203071723962001574403 44139304607585943002361605)
                ·
                  refine ⟨8276119613922364312942801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44139304607585943002361605 8276119613922364312942801)
                  ·
                    refine ⟨6207089710441773234707101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8276119613922364312942801 6207089710441773234707101)
                    ·
                      refine ⟨2327658641415664963015163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6207089710441773234707101 2327658641415664963015163)
                      ·
                        rfl

theorem cell23_4533099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 4, 2, 3].length) (baseStart_4533099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533099 prefixEnd_4533099 := by exact prefixLift 4533099
  have htrace : WordTrace (prefixWord ++ tailWord_4533099) baseStart_4533099 baseEnd_4533099 := by
    simpa [prefixWord, tailWord_4533099, baseEnd_4533099] using wordTrace_append hprefix tailTrace_4533099
  have hstable : (prefixWord ++ tailWord_4533099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533099).length < 2 ^ (prefixWord ++ tailWord_4533099).sum := by decide
  have hdescent : baseEnd_4533099 < baseStart_4533099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533106 : List Nat := [3, 2, 1, 2, 1, 1, 5, 1, 3, 4]
def baseStart_4533106 : Nat := 118140960795 + 4533106 * 2 ^ 59
def prefixEnd_4533106 : Nat := 4983230072969 + 3 ^ 40 * 4533106 * 2
def baseEnd_4533106 : Nat := 775887411926748811875877

theorem tailTrace_4533106 : CollatzResearch.WordTrace tailWord_4533106 prefixEnd_4533106 775887411926748811875877 := by
  unfold tailWord_4533106
  simp only [CollatzResearch.WordTrace]
  refine ⟨41333989678834657428316793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110223972476892419808844781 41333989678834657428316793)
  ·
    refine ⟨31000492259125993071237595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41333989678834657428316793 31000492259125993071237595)
    ·
      refine ⟨46500738388688989606856393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31000492259125993071237595 46500738388688989606856393)
      ·
        refine ⟨34875553791516742205142295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46500738388688989606856393 34875553791516742205142295)
        ·
          refine ⟨52313330687275113307713443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34875553791516742205142295 52313330687275113307713443)
          ·
            refine ⟨78469996030912669961570165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52313330687275113307713443 78469996030912669961570165)
            ·
              refine ⟨7356562127898062808897203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78469996030912669961570165 7356562127898062808897203)
              ·
                refine ⟨11034843191847094213345805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7356562127898062808897203 11034843191847094213345805)
                ·
                  refine ⟨4138066196942660330004677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11034843191847094213345805 4138066196942660330004677)
                  ·
                    refine ⟨775887411926748811875877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4138066196942660330004677 775887411926748811875877)
                    ·
                      rfl

theorem cell23_4533106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 5, 1, 3, 4].length) (baseStart_4533106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533106 prefixEnd_4533106 := by exact prefixLift 4533106
  have htrace : WordTrace (prefixWord ++ tailWord_4533106) baseStart_4533106 baseEnd_4533106 := by
    simpa [prefixWord, tailWord_4533106, baseEnd_4533106] using wordTrace_append hprefix tailTrace_4533106
  have hstable : (prefixWord ++ tailWord_4533106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533106).length < 2 ^ (prefixWord ++ tailWord_4533106).sum := by decide
  have hdescent : baseEnd_4533106 < baseStart_4533106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533163 : List Nat := [1, 1, 1, 1, 2, 1, 1, 10, 1, 1, 3]
def baseStart_4533163 : Nat := 118140960795 + 4533163 * 2 ^ 59
def prefixEnd_4533163 : Nat := 4983230072969 + 3 ^ 40 * 4533163 * 2
def baseEnd_4533163 : Nat := 2327691504177552712614869

theorem tailTrace_4533163 : CollatzResearch.WordTrace tailWord_4533163 prefixEnd_4533163 2327691504177552712614869 := by
  unfold tailWord_4533163
  simp only [CollatzResearch.WordTrace]
  refine ⟨165338037676132128448092143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110225358450754752298728095 165338037676132128448092143)
  ·
    refine ⟨248007056514198192672138215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165338037676132128448092143 248007056514198192672138215)
    ·
      refine ⟨372010584771297289008207323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248007056514198192672138215 372010584771297289008207323)
      ·
        refine ⟨558015877156945933512310985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372010584771297289008207323 558015877156945933512310985)
        ·
          refine ⟨418511907867709450134233239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558015877156945933512310985 418511907867709450134233239)
          ·
            refine ⟨627767861801564175201349859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 418511907867709450134233239 627767861801564175201349859)
            ·
              refine ⟨941651792702346262802024789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627767861801564175201349859 941651792702346262802024789)
              ·
                refine ⟨2758745486432655066802807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 941651792702346262802024789 2758745486432655066802807)
                ·
                  refine ⟨4138118229648982600204211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758745486432655066802807 4138118229648982600204211)
                  ·
                    refine ⟨6207177344473473900306317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4138118229648982600204211 6207177344473473900306317)
                    ·
                      refine ⟨2327691504177552712614869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6207177344473473900306317 2327691504177552712614869)
                      ·
                        rfl

theorem cell23_4533163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 10, 1, 1, 3].length) (baseStart_4533163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533163 prefixEnd_4533163 := by exact prefixLift 4533163
  have htrace : WordTrace (prefixWord ++ tailWord_4533163) baseStart_4533163 baseEnd_4533163 := by
    simpa [prefixWord, tailWord_4533163, baseEnd_4533163] using wordTrace_append hprefix tailTrace_4533163
  have hstable : (prefixWord ++ tailWord_4533163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533163).length < 2 ^ (prefixWord ++ tailWord_4533163).sum := by decide
  have hdescent : baseEnd_4533163 < baseStart_4533163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533196 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 4, 4]
def baseStart_4533196 : Nat := 118140960795 + 4533196 * 2 ^ 59
def prefixEnd_4533196 : Nat := 4983230072969 + 3 ^ 40 * 4533196 * 2
def baseEnd_4533196 : Nat := 775902816346383694500739

theorem tailTrace_4533196 : CollatzResearch.WordTrace tailWord_4533196 prefixEnd_4533196 775902816346383694500739 := by
  unfold tailWord_4533196
  simp only [CollatzResearch.WordTrace]
  refine ⟨82669620642506287542021721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110226160856675050056028961 82669620642506287542021721)
  ·
    refine ⟨62002215481879715656516291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82669620642506287542021721 62002215481879715656516291)
    ·
      refine ⟨93003323222819573484774437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62002215481879715656516291 93003323222819573484774437)
      ·
        refine ⟨17438123104278670028395207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93003323222819573484774437 17438123104278670028395207)
        ·
          refine ⟨26157184656418005042592811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17438123104278670028395207 26157184656418005042592811)
          ·
            refine ⟨39235776984627007563889217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26157184656418005042592811 39235776984627007563889217)
            ·
              refine ⟨29426832738470255672916913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39235776984627007563889217 29426832738470255672916913)
              ·
                refine ⟨22070124553852691754687685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29426832738470255672916913 22070124553852691754687685)
                ·
                  refine ⟨4138148353847379704003941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22070124553852691754687685 4138148353847379704003941)
                  ·
                    refine ⟨775902816346383694500739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4138148353847379704003941 775902816346383694500739)
                    ·
                      rfl

theorem cell23_4533196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 4, 4].length) (baseStart_4533196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533196 prefixEnd_4533196 := by exact prefixLift 4533196
  have htrace : WordTrace (prefixWord ++ tailWord_4533196) baseStart_4533196 baseEnd_4533196 := by
    simpa [prefixWord, tailWord_4533196, baseEnd_4533196] using wordTrace_append hprefix tailTrace_4533196
  have hstable : (prefixWord ++ tailWord_4533196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533196).length < 2 ^ (prefixWord ++ tailWord_4533196).sum := by decide
  have hdescent : baseEnd_4533196 < baseStart_4533196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533209 : List Nat := [1, 2, 1, 2, 5, 2, 10]
def baseStart_4533209 : Nat := 118140960795 + 4533209 * 2 ^ 59
def prefixEnd_4533209 : Nat := 4983230072969 + 3 ^ 40 * 4533209 * 2
def baseEnd_4533209 : Nat := 28737223756637772007897

theorem tailTrace_4533209 : CollatzResearch.WordTrace tailWord_4533209 prefixEnd_4533209 28737223756637772007897 := by
  unfold tailWord_4533209
  simp only [CollatzResearch.WordTrace]
  refine ⟨165339715433965478304266681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110226476955976985536177787 165339715433965478304266681)
  ·
    refine ⟨124004786575474108728200011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165339715433965478304266681 124004786575474108728200011)
    ·
      refine ⟨186007179863211163092300017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124004786575474108728200011 186007179863211163092300017)
      ·
        refine ⟨139505384897408372319225013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186007179863211163092300017 139505384897408372319225013)
        ·
          refine ⟨13078629834132034904927345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139505384897408372319225013 13078629834132034904927345)
          ·
            refine ⟨9808972375599026178695509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13078629834132034904927345 9808972375599026178695509)
            ·
              refine ⟨28737223756637772007897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9808972375599026178695509 28737223756637772007897)
              ·
                rfl

theorem cell23_4533209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 10].length) (baseStart_4533209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533209 prefixEnd_4533209 := by exact prefixLift 4533209
  have htrace : WordTrace (prefixWord ++ tailWord_4533209) baseStart_4533209 baseEnd_4533209 := by
    simpa [prefixWord, tailWord_4533209, baseEnd_4533209] using wordTrace_append hprefix tailTrace_4533209
  have hstable : (prefixWord ++ tailWord_4533209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533209).length < 2 ^ (prefixWord ++ tailWord_4533209).sum := by decide
  have hdescent : baseEnd_4533209 < baseStart_4533209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533213 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_4533213 : Nat := 118140960795 + 4533213 * 2 ^ 59
def prefixEnd_4533213 : Nat := 4983230072969 + 3 ^ 40 * 4533213 * 2
def baseEnd_4533213 : Nat := 775905726070092505663213

theorem tailTrace_4533213 : CollatzResearch.WordTrace tailWord_4533213 prefixEnd_4533213 775905726070092505663213 := by
  unfold tailWord_4533213
  simp only [CollatzResearch.WordTrace]
  refine ⟨165339861325950986987412293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110226574217300657991608195 165339861325950986987412293)
  ·
    refine ⟨31001223998615810060139805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165339861325950986987412293 31001223998615810060139805)
    ·
      refine ⟨11625458999480928772552427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31001223998615810060139805 11625458999480928772552427)
      ·
        refine ⟨17438188499221393158828641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11625458999480928772552427 17438188499221393158828641)
        ·
          refine ⟨13078641374416044869121481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17438188499221393158828641 13078641374416044869121481)
          ·
            refine ⟨9808981030812033651841111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13078641374416044869121481 9808981030812033651841111)
            ·
              refine ⟨14713471546218050477761667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9808981030812033651841111 14713471546218050477761667)
              ·
                refine ⟨22070207319327075716642501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14713471546218050477761667 22070207319327075716642501)
                ·
                  refine ⟨4138163872373826696870469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22070207319327075716642501 4138163872373826696870469)
                  ·
                    refine ⟨775905726070092505663213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4138163872373826696870469 775905726070092505663213)
                    ·
                      rfl

theorem cell23_4533213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_4533213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533213 prefixEnd_4533213 := by exact prefixLift 4533213
  have htrace : WordTrace (prefixWord ++ tailWord_4533213) baseStart_4533213 baseEnd_4533213 := by
    simpa [prefixWord, tailWord_4533213, baseEnd_4533213] using wordTrace_append hprefix tailTrace_4533213
  have hstable : (prefixWord ++ tailWord_4533213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533213).length < 2 ^ (prefixWord ++ tailWord_4533213).sum := by decide
  have hdescent : baseEnd_4533213 < baseStart_4533213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533230 : List Nat := [4, 1, 2, 1, 5, 1, 1, 1, 1, 6]
def baseStart_4533230 : Nat := 118140960795 + 4533230 * 2 ^ 59
def prefixEnd_4533230 : Nat := 4983230072969 + 3 ^ 40 * 4533230 * 2
def baseEnd_4533230 : Nat := 775908635793801316825687

theorem tailTrace_4533230 : CollatzResearch.WordTrace tailWord_4533230 prefixEnd_4533230 775908635793801316825687 := by
  unfold tailWord_4533230
  simp only [CollatzResearch.WordTrace]
  refine ⟨20667560170861174861347643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110226987577926265927187429 20667560170861174861347643)
  ·
    refine ⟨31001340256291762292021465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20667560170861174861347643 31001340256291762292021465)
    ·
      refine ⟨23251005192218821719016099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31001340256291762292021465 23251005192218821719016099)
      ·
        refine ⟨34876507788328232578524149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23251005192218821719016099 34876507788328232578524149)
        ·
          refine ⟨3269672605155771804236639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34876507788328232578524149 3269672605155771804236639)
          ·
            refine ⟨4904508907733657706354959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269672605155771804236639 4904508907733657706354959)
            ·
              refine ⟨7356763361600486559532439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4904508907733657706354959 7356763361600486559532439)
              ·
                refine ⟨11035145042400729839298659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7356763361600486559532439 11035145042400729839298659)
                ·
                  refine ⟨16552717563601094758947989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11035145042400729839298659 16552717563601094758947989)
                  ·
                    refine ⟨775908635793801316825687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16552717563601094758947989 775908635793801316825687)
                    ·
                      rfl

theorem cell23_4533230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_4533230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533230 prefixEnd_4533230 := by exact prefixLift 4533230
  have htrace : WordTrace (prefixWord ++ tailWord_4533230) baseStart_4533230 baseEnd_4533230 := by
    simpa [prefixWord, tailWord_4533230, baseEnd_4533230] using wordTrace_append hprefix tailTrace_4533230
  have hstable : (prefixWord ++ tailWord_4533230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533230).length < 2 ^ (prefixWord ++ tailWord_4533230).sum := by decide
  have hdescent : baseEnd_4533230 < baseStart_4533230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533233 : List Nat := [1, 2, 2, 2, 4, 3, 1, 1, 1, 2, 4]
def baseStart_4533233 : Nat := 118140960795 + 4533233 * 2 ^ 59
def prefixEnd_4533233 : Nat := 4983230072969 + 3 ^ 40 * 4533233 * 2
def baseEnd_4533233 : Nat := 2327727447823367438739547

theorem tailTrace_4533233 : CollatzResearch.WordTrace tailWord_4533233 prefixEnd_4533233 2327727447823367438739547 := by
  unfold tailWord_4533233
  simp only [CollatzResearch.WordTrace]
  refine ⟨165340590785878530403140353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110227060523919020268760235 165340590785878530403140353)
  ·
    refine ⟨124005443089408897802355265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165340590785878530403140353 124005443089408897802355265)
    ·
      refine ⟨93004082317056673351766449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124005443089408897802355265 93004082317056673351766449)
      ·
        refine ⟨69753061737792505013824837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93004082317056673351766449 69753061737792505013824837)
        ·
          refine ⟨13078699075836094690092157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69753061737792505013824837 13078699075836094690092157)
          ·
            refine ⟨4904512153438535508784559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13078699075836094690092157 4904512153438535508784559)
            ·
              refine ⟨7356768230157803263176839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4904512153438535508784559 7356768230157803263176839)
              ·
                refine ⟨11035152345236704894765259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7356768230157803263176839 11035152345236704894765259)
                ·
                  refine ⟨16552728517855057342147889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11035152345236704894765259 16552728517855057342147889)
                  ·
                    refine ⟨12414546388391293006610917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16552728517855057342147889 12414546388391293006610917)
                    ·
                      refine ⟨2327727447823367438739547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12414546388391293006610917 2327727447823367438739547)
                      ·
                        rfl

theorem cell23_4533233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_4533233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533233 prefixEnd_4533233 := by exact prefixLift 4533233
  have htrace : WordTrace (prefixWord ++ tailWord_4533233) baseStart_4533233 baseEnd_4533233 := by
    simpa [prefixWord, tailWord_4533233, baseEnd_4533233] using wordTrace_append hprefix tailTrace_4533233
  have hstable : (prefixWord ++ tailWord_4533233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533233).length < 2 ^ (prefixWord ++ tailWord_4533233).sum := by decide
  have hdescent : baseEnd_4533233 < baseStart_4533233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533237 : List Nat := [1, 3, 5, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4533237 : Nat := 118140960795 + 4533237 * 2 ^ 59
def prefixEnd_4533237 : Nat := 4983230072969 + 3 ^ 40 * 4533237 * 2
def baseEnd_4533237 : Nat := 2327729501745985423089529

theorem tailTrace_4533237 : CollatzResearch.WordTrace tailWord_4533237 prefixEnd_4533237 2327729501745985423089529 := by
  unfold tailWord_4533237
  simp only [CollatzResearch.WordTrace]
  refine ⟨165340736677864039086285965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110227157785242692724190643 165340736677864039086285965)
  ·
    refine ⟨62002776254199014657357237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165340736677864039086285965 62002776254199014657357237)
    ·
      refine ⟨5812760273831157624127241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62002776254199014657357237 5812760273831157624127241)
      ·
        refine ⟨4359570205373368218095431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5812760273831157624127241 4359570205373368218095431)
        ·
          refine ⟨6539355308060052327143147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4359570205373368218095431 6539355308060052327143147)
          ·
            refine ⟨9809032962090078490714721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6539355308060052327143147 9809032962090078490714721)
            ·
              refine ⟨7356774721567558868036041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9809032962090078490714721 7356774721567558868036041)
              ·
                refine ⟨5517581041175669151027031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7356774721567558868036041 5517581041175669151027031)
                ·
                  refine ⟨8276371561763503726540547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5517581041175669151027031 8276371561763503726540547)
                  ·
                    refine ⟨12414557342645255589810821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8276371561763503726540547 12414557342645255589810821)
                    ·
                      refine ⟨2327729501745985423089529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12414557342645255589810821 2327729501745985423089529)
                      ·
                        rfl

theorem cell23_4533237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4533237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533237 prefixEnd_4533237 := by exact prefixLift 4533237
  have htrace : WordTrace (prefixWord ++ tailWord_4533237) baseStart_4533237 baseEnd_4533237 := by
    simpa [prefixWord, tailWord_4533237, baseEnd_4533237] using wordTrace_append hprefix tailTrace_4533237
  have hstable : (prefixWord ++ tailWord_4533237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533237).length < 2 ^ (prefixWord ++ tailWord_4533237).sum := by decide
  have hdescent : baseEnd_4533237 < baseStart_4533237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533287 : List Nat := [1, 1, 7, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_4533287 : Nat := 118140960795 + 4533287 * 2 ^ 59
def prefixEnd_4533287 : Nat := 4983230072969 + 3 ^ 40 * 4533287 * 2
def baseEnd_4533287 : Nat := 2327755175778710227464299

theorem tailTrace_4533287 : CollatzResearch.WordTrace tailWord_4533287 prefixEnd_4533287 2327755175778710227464299 := by
  unfold tailWord_4533287
  simp only [CollatzResearch.WordTrace]
  refine ⟨165342560327682897625606115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110228373551788598417070743 165342560327682897625606115)
  ·
    refine ⟨248013840491524346438409173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165342560327682897625606115 248013840491524346438409173)
    ·
      refine ⟨5812824386520101869650215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 248013840491524346438409173 5812824386520101869650215)
      ·
        refine ⟨8719236579780152804475323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5812824386520101869650215 8719236579780152804475323)
        ·
          refine ⟨13078854869670229206712985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8719236579780152804475323 13078854869670229206712985)
          ·
            refine ⟨9809141152252671905034739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13078854869670229206712985 9809141152252671905034739)
            ·
              refine ⟨14713711728379007857552109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9809141152252671905034739 14713711728379007857552109)
              ·
                refine ⟨5517641898142127946582041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14713711728379007857552109 5517641898142127946582041)
                ·
                  refine ⟨4138231423606595959936531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5517641898142127946582041 4138231423606595959936531)
                  ·
                    refine ⟨6207347135409893939904797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4138231423606595959936531 6207347135409893939904797)
                    ·
                      refine ⟨2327755175778710227464299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6207347135409893939904797 2327755175778710227464299)
                      ·
                        rfl

theorem cell23_4533287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_4533287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533287 prefixEnd_4533287 := by exact prefixLift 4533287
  have htrace : WordTrace (prefixWord ++ tailWord_4533287) baseStart_4533287 baseEnd_4533287 := by
    simpa [prefixWord, tailWord_4533287, baseEnd_4533287] using wordTrace_append hprefix tailTrace_4533287
  have hstable : (prefixWord ++ tailWord_4533287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533287).length < 2 ^ (prefixWord ++ tailWord_4533287).sum := by decide
  have hdescent : baseEnd_4533287 < baseStart_4533287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533299 : List Nat := [1, 1, 1, 2, 4, 1, 1, 3, 9]
def baseStart_4533299 : Nat := 118140960795 + 4533299 * 2 ^ 59
def prefixEnd_4533299 : Nat := 4983230072969 + 3 ^ 40 * 4533299 * 2
def baseEnd_4533299 : Nat := 258640148616284908946027

theorem tailTrace_4533299 : CollatzResearch.WordTrace tailWord_4533299 prefixEnd_4533299 258640148616284908946027 := by
  unfold tailWord_4533299
  simp only [CollatzResearch.WordTrace]
  refine ⟨165342998003639423675042951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110228665335759615783361967 165342998003639423675042951)
  ·
    refine ⟨248014497005459135512564427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165342998003639423675042951 248014497005459135512564427)
    ·
      refine ⟨372021745508188703268846641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248014497005459135512564427 372021745508188703268846641)
      ·
        refine ⟨279016309131141527451634981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372021745508188703268846641 279016309131141527451634981)
        ·
          refine ⟨52315557962089036397181559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 279016309131141527451634981 52315557962089036397181559)
          ·
            refine ⟨78473336943133554595772339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52315557962089036397181559 78473336943133554595772339)
            ·
              refine ⟨117710005414700331893658509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78473336943133554595772339 117710005414700331893658509)
              ·
                refine ⟨44141252030512624460121941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117710005414700331893658509 44141252030512624460121941)
                ·
                  refine ⟨258640148616284908946027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44141252030512624460121941 258640148616284908946027)
                  ·
                    rfl

theorem cell23_4533299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 3, 9].length) (baseStart_4533299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533299 prefixEnd_4533299 := by exact prefixLift 4533299
  have htrace : WordTrace (prefixWord ++ tailWord_4533299) baseStart_4533299 baseEnd_4533299 := by
    simpa [prefixWord, tailWord_4533299, baseEnd_4533299] using wordTrace_append hprefix tailTrace_4533299
  have hstable : (prefixWord ++ tailWord_4533299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533299).length < 2 ^ (prefixWord ++ tailWord_4533299).sum := by decide
  have hdescent : baseEnd_4533299 < baseStart_4533299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533310 : List Nat := [4, 2, 1, 3, 1, 1, 1, 1, 3, 4, 2]
def baseStart_4533310 : Nat := 118140960795 + 4533310 * 2 ^ 59
def prefixEnd_4533310 : Nat := 4983230072969 + 3 ^ 40 * 4533310 * 2
def baseEnd_4533310 : Nat := 2327766985833763637476693

theorem tailTrace_4533310 : CollatzResearch.WordTrace tailWord_4533310 prefixEnd_4533310 2327766985833763637476693 := by
  unfold tailWord_4533310
  simp only [CollatzResearch.WordTrace]
  refine ⟨20667924900824946569211673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110228932804399715035795589 20667924900824946569211673)
  ·
    refine ⟨15500943675618709926908755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20667924900824946569211673 15500943675618709926908755)
    ·
      refine ⟨23251415513428064890363133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15500943675618709926908755 23251415513428064890363133)
      ·
        refine ⟨8719280817535524333886175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23251415513428064890363133 8719280817535524333886175)
        ·
          refine ⟨13078921226303286500829263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8719280817535524333886175 13078921226303286500829263)
          ·
            refine ⟨19618381839454929751243895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13078921226303286500829263 19618381839454929751243895)
            ·
              refine ⟨29427572759182394626865843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19618381839454929751243895 29427572759182394626865843)
              ·
                refine ⟨44141359138773591940298765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29427572759182394626865843 44141359138773591940298765)
                ·
                  refine ⟨16553009677040096977612037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44141359138773591940298765 16553009677040096977612037)
                  ·
                    refine ⟨3103689314445018183302257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16553009677040096977612037 3103689314445018183302257)
                    ·
                      refine ⟨2327766985833763637476693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103689314445018183302257 2327766985833763637476693)
                      ·
                        rfl

theorem cell23_4533310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_4533310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533310 prefixEnd_4533310 := by exact prefixLift 4533310
  have htrace : WordTrace (prefixWord ++ tailWord_4533310) baseStart_4533310 baseEnd_4533310 := by
    simpa [prefixWord, tailWord_4533310, baseEnd_4533310] using wordTrace_append hprefix tailTrace_4533310
  have hstable : (prefixWord ++ tailWord_4533310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533310).length < 2 ^ (prefixWord ++ tailWord_4533310).sum := by decide
  have hdescent : baseEnd_4533310 < baseStart_4533310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533333 : List Nat := [1, 3, 2, 2, 1, 2, 3, 4, 5]
def baseStart_4533333 : Nat := 118140960795 + 4533333 * 2 ^ 59
def prefixEnd_4533333 : Nat := 4983230072969 + 3 ^ 40 * 4533333 * 2
def baseEnd_4533333 : Nat := 258642088432090783054343

theorem tailTrace_4533333 : CollatzResearch.WordTrace tailWord_4533333 prefixEnd_4533333 258642088432090783054343 := by
  unfold tailWord_4533333
  simp only [CollatzResearch.WordTrace]
  refine ⟨165344238085516247481780653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110229492057010831654520435 165344238085516247481780653)
  ·
    refine ⟨62004089282068592805667745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165344238085516247481780653 62004089282068592805667745)
    ·
      refine ⟨46503066961551444604250809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62004089282068592805667745 46503066961551444604250809)
      ·
        refine ⟨34877300221163583453188107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46503066961551444604250809 34877300221163583453188107)
        ·
          refine ⟨52315950331745375179782161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34877300221163583453188107 52315950331745375179782161)
          ·
            refine ⟨39236962748809031384836621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52315950331745375179782161 39236962748809031384836621)
            ·
              refine ⟨14713861030803386769313733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39236962748809031384836621 14713861030803386769313733)
              ·
                refine ⟨2758848943275635019246325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14713861030803386769313733 2758848943275635019246325)
                ·
                  refine ⟨258642088432090783054343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2758848943275635019246325 258642088432090783054343)
                  ·
                    rfl

theorem cell23_4533333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 4, 5].length) (baseStart_4533333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533333 prefixEnd_4533333 := by exact prefixLift 4533333
  have htrace : WordTrace (prefixWord ++ tailWord_4533333) baseStart_4533333 baseEnd_4533333 := by
    simpa [prefixWord, tailWord_4533333, baseEnd_4533333] using wordTrace_append hprefix tailTrace_4533333
  have hstable : (prefixWord ++ tailWord_4533333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533333).length < 2 ^ (prefixWord ++ tailWord_4533333).sum := by decide
  have hdescent : baseEnd_4533333 < baseStart_4533333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533400 : List Nat := [2, 1, 2, 4, 2, 1, 2, 1, 2, 4, 2]
def baseStart_4533400 : Nat := 118140960795 + 4533400 * 2 ^ 59
def prefixEnd_4533400 : Nat := 4983230072969 + 3 ^ 40 * 4533400 * 2
def baseEnd_4533400 : Nat := 2327813199092668285351279

theorem tailTrace_4533400 : CollatzResearch.WordTrace tailWord_4533400 prefixEnd_4533400 2327813199092668285351279 := by
  unfold tailWord_4533400
  simp only [CollatzResearch.WordTrace]
  refine ⟨82673340888136758962234827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110231121184182345282979769 82673340888136758962234827)
  ·
    refine ⟨124010011332205138443352241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82673340888136758962234827 124010011332205138443352241)
    ·
      refine ⟨93007508499153853832514181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124010011332205138443352241 93007508499153853832514181)
      ·
        refine ⟨17438907843591347593596409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93007508499153853832514181 17438907843591347593596409)
        ·
          refine ⟨13079180882693510695197307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17438907843591347593596409 13079180882693510695197307)
          ·
            refine ⟨19618771324040266042795961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13079180882693510695197307 19618771324040266042795961)
            ·
              refine ⟨14714078493030199532096971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19618771324040266042795961 14714078493030199532096971)
              ·
                refine ⟨22071117739545299298145457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14714078493030199532096971 22071117739545299298145457)
                ·
                  refine ⟨16553338304658974473609093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22071117739545299298145457 16553338304658974473609093)
                  ·
                    refine ⟨3103750932123557713801705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16553338304658974473609093 3103750932123557713801705)
                    ·
                      refine ⟨2327813199092668285351279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103750932123557713801705 2327813199092668285351279)
                      ·
                        rfl

theorem cell23_4533400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_4533400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533400 prefixEnd_4533400 := by exact prefixLift 4533400
  have htrace : WordTrace (prefixWord ++ tailWord_4533400) baseStart_4533400 baseEnd_4533400 := by
    simpa [prefixWord, tailWord_4533400, baseEnd_4533400] using wordTrace_append hprefix tailTrace_4533400
  have hstable : (prefixWord ++ tailWord_4533400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533400).length < 2 ^ (prefixWord ++ tailWord_4533400).sum := by decide
  have hdescent : baseEnd_4533400 < baseStart_4533400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533443 : List Nat := [1, 1, 1, 3, 1, 1, 1, 4, 3, 5, 2]
def baseStart_4533443 : Nat := 118140960795 + 4533443 * 2 ^ 59
def prefixEnd_4533443 : Nat := 4983230072969 + 3 ^ 40 * 4533443 * 2
def baseEnd_4533443 : Nat := 2327835278760811617113581

theorem tailTrace_4533443 : CollatzResearch.WordTrace tailWord_4533443 prefixEnd_4533443 2327835278760811617113581 := by
  unfold tailWord_4533443
  simp only [CollatzResearch.WordTrace]
  refine ⟨165348250115117736268284983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110232166743411824178856655 165348250115117736268284983)
  ·
    refine ⟨248022375172676604402427475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165348250115117736268284983 248022375172676604402427475)
    ·
      refine ⟨372033562759014906603641213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248022375172676604402427475 372033562759014906603641213)
      ·
        refine ⟨139512586034630589976365455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 372033562759014906603641213 139512586034630589976365455)
        ·
          refine ⟨209268879051945884964548183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139512586034630589976365455 209268879051945884964548183)
          ·
            refine ⟨313903318577918827446822275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209268879051945884964548183 313903318577918827446822275)
            ·
              refine ⟨470854977866878241170233413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313903318577918827446822275 470854977866878241170233413)
              ·
                refine ⟨88285308350039670219418765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 470854977866878241170233413 88285308350039670219418765)
                ·
                  refine ⟨33106990631264876332282037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88285308350039670219418765 33106990631264876332282037)
                  ·
                    refine ⟨3103780371681082156151441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33106990631264876332282037 3103780371681082156151441)
                    ·
                      refine ⟨2327835278760811617113581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103780371681082156151441 2327835278760811617113581)
                      ·
                        rfl

theorem cell23_4533443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 3, 5, 2].length) (baseStart_4533443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533443 prefixEnd_4533443 := by exact prefixLift 4533443
  have htrace : WordTrace (prefixWord ++ tailWord_4533443) baseStart_4533443 baseEnd_4533443 := by
    simpa [prefixWord, tailWord_4533443, baseEnd_4533443] using wordTrace_append hprefix tailTrace_4533443
  have hstable : (prefixWord ++ tailWord_4533443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533443).length < 2 ^ (prefixWord ++ tailWord_4533443).sum := by decide
  have hdescent : baseEnd_4533443 < baseStart_4533443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533444 : List Nat := [2, 3, 3, 1, 4, 1, 1, 1, 3, 4]
def baseStart_4533444 : Nat := 118140960795 + 4533444 * 2 ^ 59
def prefixEnd_4533444 : Nat := 4983230072969 + 3 ^ 40 * 4533444 * 2
def baseEnd_4533444 : Nat := 775945264080488704400359

theorem tailTrace_4533444 : CollatzResearch.WordTrace tailWord_4533444 prefixEnd_4533444 775945264080488704400359 := by
  unfold tailWord_4533444
  simp only [CollatzResearch.WordTrace]
  refine ⟨82674143294057056719535693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110232191058742742292714257 82674143294057056719535693)
  ·
    refine ⟨31002803735271396269825885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82674143294057056719535693 31002803735271396269825885)
    ·
      refine ⟨11626051400726773601184707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31002803735271396269825885 11626051400726773601184707)
      ·
        refine ⟨17439077101090160401777061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11626051400726773601184707 17439077101090160401777061)
        ·
          refine ⟨3269826956454405075333199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17439077101090160401777061 3269826956454405075333199)
          ·
            refine ⟨4904740434681607612999799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269826956454405075333199 4904740434681607612999799)
            ·
              refine ⟨7357110652022411419499699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4904740434681607612999799 7357110652022411419499699)
              ·
                refine ⟨11035665978033617129249549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7357110652022411419499699 11035665978033617129249549)
                ·
                  refine ⟨4138374741762606423468581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11035665978033617129249549 4138374741762606423468581)
                  ·
                    refine ⟨775945264080488704400359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4138374741762606423468581 775945264080488704400359)
                    ·
                      rfl

theorem cell23_4533444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_4533444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533444 prefixEnd_4533444 := by exact prefixLift 4533444
  have htrace : WordTrace (prefixWord ++ tailWord_4533444) baseStart_4533444 baseEnd_4533444 := by
    simpa [prefixWord, tailWord_4533444, baseEnd_4533444] using wordTrace_append hprefix tailTrace_4533444
  have hstable : (prefixWord ++ tailWord_4533444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533444).length < 2 ^ (prefixWord ++ tailWord_4533444).sum := by decide
  have hdescent : baseEnd_4533444 < baseStart_4533444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533483 : List Nat := [1, 1, 1, 1, 2, 7, 1, 2, 1, 6]
def baseStart_4533483 : Nat := 118140960795 + 4533483 * 2 ^ 59
def prefixEnd_4533483 : Nat := 4983230072969 + 3 ^ 40 * 4533483 * 2
def baseEnd_4533483 : Nat := 775951939328997153537799

theorem tailTrace_4533483 : CollatzResearch.WordTrace tailWord_4533483 prefixEnd_4533483 775951939328997153537799 := by
  unfold tailWord_4533483
  simp only [CollatzResearch.WordTrace]
  refine ⟨165349709034972823099741103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110233139356648548733160735 165349709034972823099741103)
  ·
    refine ⟨248024563552459234649611655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165349709034972823099741103 248024563552459234649611655)
    ·
      refine ⟨372036845328688851974417483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248024563552459234649611655 372036845328688851974417483)
      ·
        refine ⟨558055267993033277961626225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372036845328688851974417483 558055267993033277961626225)
        ·
          refine ⟨418541450994774958471219669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558055267993033277961626225 418541450994774958471219669)
          ·
            refine ⟨9809565257690038089169211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 418541450994774958471219669 9809565257690038089169211)
            ·
              refine ⟨14714347886535057133753817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9809565257690038089169211 14714347886535057133753817)
              ·
                refine ⟨11035760914901292850315363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14714347886535057133753817 11035760914901292850315363)
                ·
                  refine ⟨16553641372351939275473045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11035760914901292850315363 16553641372351939275473045)
                  ·
                    refine ⟨775951939328997153537799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16553641372351939275473045 775951939328997153537799)
                    ·
                      rfl

theorem cell23_4533483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 2, 1, 6].length) (baseStart_4533483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533483 prefixEnd_4533483 := by exact prefixLift 4533483
  have htrace : WordTrace (prefixWord ++ tailWord_4533483) baseStart_4533483 baseEnd_4533483 := by
    simpa [prefixWord, tailWord_4533483, baseEnd_4533483] using wordTrace_append hprefix tailTrace_4533483
  have hstable : (prefixWord ++ tailWord_4533483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533483).length < 2 ^ (prefixWord ++ tailWord_4533483).sum := by decide
  have hdescent : baseEnd_4533483 < baseStart_4533483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533487 : List Nat := [1, 1, 2, 1, 7, 1, 3, 1, 1, 5]
def baseStart_4533487 : Nat := 118140960795 + 4533487 * 2 ^ 59
def prefixEnd_4533487 : Nat := 4983230072969 + 3 ^ 40 * 4533487 * 2
def baseEnd_4533487 : Nat := 775952623969869814987793

theorem tailTrace_4533487 : CollatzResearch.WordTrace tailWord_4533487 prefixEnd_4533487 775952623969869814987793 := by
  unfold tailWord_4533487
  simp only [CollatzResearch.WordTrace]
  refine ⟨165349854926958331782886715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110233236617972221188591143 165349854926958331782886715)
  ·
    refine ⟨248024782390437497674330073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165349854926958331782886715 248024782390437497674330073)
    ·
      refine ⟨186018586792828123255747555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248024782390437497674330073 186018586792828123255747555)
      ·
        refine ⟨279027880189242184883621333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186018586792828123255747555 279027880189242184883621333)
        ·
          refine ⟨6539715941935363708209875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 279027880189242184883621333 6539715941935363708209875)
          ·
            refine ⟨9809573912903045562314813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6539715941935363708209875 9809573912903045562314813)
            ·
              refine ⟨3678590217338642085868055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9809573912903045562314813 3678590217338642085868055)
              ·
                refine ⟨5517885326007963128802083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3678590217338642085868055 5517885326007963128802083)
                ·
                  refine ⟨8276827989011944693203125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5517885326007963128802083 8276827989011944693203125)
                  ·
                    refine ⟨775952623969869814987793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8276827989011944693203125 775952623969869814987793)
                    ·
                      rfl

theorem cell23_4533487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 3, 1, 1, 5].length) (baseStart_4533487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533487 prefixEnd_4533487 := by exact prefixLift 4533487
  have htrace : WordTrace (prefixWord ++ tailWord_4533487) baseStart_4533487 baseEnd_4533487 := by
    simpa [prefixWord, tailWord_4533487, baseEnd_4533487] using wordTrace_append hprefix tailTrace_4533487
  have hstable : (prefixWord ++ tailWord_4533487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533487).length < 2 ^ (prefixWord ++ tailWord_4533487).sum := by decide
  have hdescent : baseEnd_4533487 < baseStart_4533487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533530 : List Nat := [3, 1, 1, 3, 3, 2, 3, 7]
def baseStart_4533530 : Nat := 118140960795 + 4533530 * 2 ^ 59
def prefixEnd_4533530 : Nat := 4983230072969 + 3 ^ 40 * 4533530 * 2
def baseEnd_4533530 : Nat := 86217775984361213952803

theorem tailTrace_4533530 : CollatzResearch.WordTrace tailWord_4533530 prefixEnd_4533530 86217775984361213952803 := by
  unfold tailWord_4533530
  simp only [CollatzResearch.WordTrace]
  refine ⟨41337855816450637531675511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110234282177201700084468029 41337855816450637531675511)
  ·
    refine ⟨62006783724675956297513267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41337855816450637531675511 62006783724675956297513267)
    ·
      refine ⟨93010175587013934446269901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62006783724675956297513267 93010175587013934446269901)
      ·
        refine ⟨34878815845130225417351213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93010175587013934446269901 34878815845130225417351213)
        ·
          refine ⟨13079555941923834531506705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34878815845130225417351213 13079555941923834531506705)
          ·
            refine ⟨9809666956442875898630029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13079555941923834531506705 9809666956442875898630029)
            ·
              refine ⟨3678625108666078461986261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9809666956442875898630029 3678625108666078461986261)
              ·
                refine ⟨86217775984361213952803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3678625108666078461986261 86217775984361213952803)
                ·
                  rfl

theorem cell23_4533530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 3, 7].length) (baseStart_4533530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533530 prefixEnd_4533530 := by exact prefixLift 4533530
  have htrace : WordTrace (prefixWord ++ tailWord_4533530) baseStart_4533530 baseEnd_4533530 := by
    simpa [prefixWord, tailWord_4533530, baseEnd_4533530] using wordTrace_append hprefix tailTrace_4533530
  have hstable : (prefixWord ++ tailWord_4533530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533530).length < 2 ^ (prefixWord ++ tailWord_4533530).sum := by decide
  have hdescent : baseEnd_4533530 < baseStart_4533530 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533540 : List Nat := [2, 3, 1, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_4533540 : Nat := 118140960795 + 4533540 * 2 ^ 59
def prefixEnd_4533540 : Nat := 4983230072969 + 3 ^ 40 * 4533540 * 2
def baseEnd_4533540 : Nat := 2327885086384297737600635

theorem tailTrace_4533540 : CollatzResearch.WordTrace tailWord_4533540 prefixEnd_4533540 2327885086384297737600635 := by
  unfold tailWord_4533540
  simp only [CollatzResearch.WordTrace]
  refine ⟨82675893997883160917283037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110234525330510881223044049 82675893997883160917283037)
  ·
    refine ⟨31003460249206185343981139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82675893997883160917283037 31003460249206185343981139)
    ·
      refine ⟨46505190373809278015971709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31003460249206185343981139 46505190373809278015971709)
      ·
        refine ⟨17439446390178479255989391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46505190373809278015971709 17439446390178479255989391)
        ·
          refine ⟨26159169585267718883984087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17439446390178479255989391 26159169585267718883984087)
          ·
            refine ⟨39238754377901578325976131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26159169585267718883984087 39238754377901578325976131)
            ·
              refine ⟨58858131566852367488964197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39238754377901578325976131 58858131566852367488964197)
              ·
                refine ⟨11035899668784818904180787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58858131566852367488964197 11035899668784818904180787)
                ·
                  refine ⟨16553849503177228356271181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11035899668784818904180787 16553849503177228356271181)
                  ·
                    refine ⟨6207693563691460633601693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16553849503177228356271181 6207693563691460633601693)
                    ·
                      refine ⟨2327885086384297737600635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6207693563691460633601693 2327885086384297737600635)
                      ·
                        rfl

theorem cell23_4533540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_4533540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533540 prefixEnd_4533540 := by exact prefixLift 4533540
  have htrace : WordTrace (prefixWord ++ tailWord_4533540) baseStart_4533540 baseEnd_4533540 := by
    simpa [prefixWord, tailWord_4533540, baseEnd_4533540] using wordTrace_append hprefix tailTrace_4533540
  have hstable : (prefixWord ++ tailWord_4533540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533540).length < 2 ^ (prefixWord ++ tailWord_4533540).sum := by decide
  have hdescent : baseEnd_4533540 < baseStart_4533540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533541 : List Nat := [1, 3, 1, 2, 4, 2, 2, 3, 1, 2, 2]
def baseStart_4533541 : Nat := 118140960795 + 4533541 * 2 ^ 59
def prefixEnd_4533541 : Nat := 4983230072969 + 3 ^ 40 * 4533541 * 2
def baseEnd_4533541 : Nat := 2327885599864952233688131

theorem tailTrace_4533541 : CollatzResearch.WordTrace tailWord_4533541 prefixEnd_4533541 2327885599864952233688131 := by
  unfold tailWord_4533541
  simp only [CollatzResearch.WordTrace]
  refine ⟨165351824468762699005352477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110234549645841799336901651 165351824468762699005352477)
  ·
    refine ⟨62006934175786012127007179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165351824468762699005352477 62006934175786012127007179)
    ·
      refine ⟨93010401263679018190510769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62006934175786012127007179 93010401263679018190510769)
      ·
        refine ⟨69757800947759263642883077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93010401263679018190510769 69757800947759263642883077)
        ·
          refine ⟨13079587677704861933040577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69757800947759263642883077 13079587677704861933040577)
          ·
            refine ⟨9809690758278646449780433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13079587677704861933040577 9809690758278646449780433)
            ·
              refine ⟨7357268068708984837335325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9809690758278646449780433 7357268068708984837335325)
              ·
                refine ⟨2758975525765869314000747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7357268068708984837335325 2758975525765869314000747)
                ·
                  refine ⟨4138463288648803971001121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758975525765869314000747 4138463288648803971001121)
                  ·
                    refine ⟨3103847466486602978250841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4138463288648803971001121 3103847466486602978250841)
                    ·
                      refine ⟨2327885599864952233688131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103847466486602978250841 2327885599864952233688131)
                      ·
                        rfl

theorem cell23_4533541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 3, 1, 2, 2].length) (baseStart_4533541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533541 prefixEnd_4533541 := by exact prefixLift 4533541
  have htrace : WordTrace (prefixWord ++ tailWord_4533541) baseStart_4533541 baseEnd_4533541 := by
    simpa [prefixWord, tailWord_4533541, baseEnd_4533541] using wordTrace_append hprefix tailTrace_4533541
  have hstable : (prefixWord ++ tailWord_4533541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533541).length < 2 ^ (prefixWord ++ tailWord_4533541).sum := by decide
  have hdescent : baseEnd_4533541 < baseStart_4533541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533544 : List Nat := [2, 1, 5, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_4533544 : Nat := 118140960795 + 4533544 * 2 ^ 59
def prefixEnd_4533544 : Nat := 4983230072969 + 3 ^ 40 * 4533544 * 2
def baseEnd_4533544 : Nat := 2327887140306915721950617

theorem tailTrace_4533544 : CollatzResearch.WordTrace tailWord_4533544 prefixEnd_4533544 2327887140306915721950617 := by
  unfold tailWord_4533544
  simp only [CollatzResearch.WordTrace]
  refine ⟨82675966943875915258855843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110234622591834553678474457 82675966943875915258855843)
  ·
    refine ⟨124013950415813872888283765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82675966943875915258855843 124013950415813872888283765)
    ·
      refine ⟨11626307851482550583276603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124013950415813872888283765 11626307851482550583276603)
      ·
        refine ⟨17439461777223825874914905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11626307851482550583276603 17439461777223825874914905)
        ·
          refine ⟨13079596332917869406186179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17439461777223825874914905 13079596332917869406186179)
          ·
            refine ⟨19619394499376804109279269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13079596332917869406186179 19619394499376804109279269)
            ·
              refine ⟨3678636468633150770489863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19619394499376804109279269 3678636468633150770489863)
              ·
                refine ⟨5517954702949726155734795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3678636468633150770489863 5517954702949726155734795)
                ·
                  refine ⟨8276932054424589233602193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5517954702949726155734795 8276932054424589233602193)
                  ·
                    refine ⟨6207699040818441925201645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8276932054424589233602193 6207699040818441925201645)
                    ·
                      refine ⟨2327887140306915721950617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6207699040818441925201645 2327887140306915721950617)
                      ·
                        rfl

theorem cell23_4533544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_4533544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533544 prefixEnd_4533544 := by exact prefixLift 4533544
  have htrace : WordTrace (prefixWord ++ tailWord_4533544) baseStart_4533544 baseEnd_4533544 := by
    simpa [prefixWord, tailWord_4533544, baseEnd_4533544] using wordTrace_append hprefix tailTrace_4533544
  have hstable : (prefixWord ++ tailWord_4533544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533544).length < 2 ^ (prefixWord ++ tailWord_4533544).sum := by decide
  have hdescent : baseEnd_4533544 < baseStart_4533544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533557 : List Nat := [1, 3, 3, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_4533557 : Nat := 118140960795 + 4533557 * 2 ^ 59
def prefixEnd_4533557 : Nat := 4983230072969 + 3 ^ 40 * 4533557 * 2
def baseEnd_4533557 : Nat := 2327893815555424171088057

theorem tailTrace_4533557 : CollatzResearch.WordTrace tailWord_4533557 prefixEnd_4533557 2327893815555424171088057 := by
  unfold tailWord_4533557
  simp only [CollatzResearch.WordTrace]
  refine ⟨165352408036704733737934925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110234938691136489158623283 165352408036704733737934925)
  ·
    refine ⟨62007153013764275151725597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165352408036704733737934925 62007153013764275151725597)
    ·
      refine ⟨23252682380161603181897099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62007153013764275151725597 23252682380161603181897099)
      ·
        refine ⟨34879023570242404772845649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23252682380161603181897099 34879023570242404772845649)
        ·
          refine ⟨26159267677681803579634237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34879023570242404772845649 26159267677681803579634237)
          ·
            refine ⟨9809725379130676342362839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26159267677681803579634237 9809725379130676342362839)
            ·
              refine ⟨14714588068696014513544259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9809725379130676342362839 14714588068696014513544259)
              ·
                refine ⟨22071882103044021770316389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14714588068696014513544259 22071882103044021770316389)
                ·
                  refine ⟨4138477894320754081934323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22071882103044021770316389 4138477894320754081934323)
                  ·
                    refine ⟨6207716841481131122901485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4138477894320754081934323 6207716841481131122901485)
                    ·
                      refine ⟨2327893815555424171088057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6207716841481131122901485 2327893815555424171088057)
                      ·
                        rfl

theorem cell23_4533557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_4533557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533557 prefixEnd_4533557 := by exact prefixLift 4533557
  have htrace : WordTrace (prefixWord ++ tailWord_4533557) baseStart_4533557 baseEnd_4533557 := by
    simpa [prefixWord, tailWord_4533557, baseEnd_4533557] using wordTrace_append hprefix tailTrace_4533557
  have hstable : (prefixWord ++ tailWord_4533557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533557).length < 2 ^ (prefixWord ++ tailWord_4533557).sum := by decide
  have hdescent : baseEnd_4533557 < baseStart_4533557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533558 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_4533558 : Nat := 118140960795 + 4533558 * 2 ^ 59
def prefixEnd_4533558 : Nat := 4983230072969 + 3 ^ 40 * 4533558 * 2
def baseEnd_4533558 : Nat := 2327894329036078667175553

theorem tailTrace_4533558 : CollatzResearch.WordTrace tailWord_4533558 prefixEnd_4533558 2327894329036078667175553 := by
  unfold tailWord_4533558
  simp only [CollatzResearch.WordTrace]
  refine ⟨10334527781856319431795083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110234963006467407272480885 10334527781856319431795083)
  ·
    refine ⟨15501791672784479147692625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10334527781856319431795083 15501791672784479147692625)
    ·
      refine ⟨11626343754588359360769469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15501791672784479147692625 11626343754588359360769469)
      ·
        refine ⟨4359878907970634760288551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11626343754588359360769469 4359878907970634760288551)
        ·
          refine ⟨6539818361955952140432827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4359878907970634760288551 6539818361955952140432827)
          ·
            refine ⟨9809727542933928210649241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6539818361955952140432827 9809727542933928210649241)
            ·
              refine ⟨7357295657200446157986931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9809727542933928210649241 7357295657200446157986931)
              ·
                refine ⟨11035943485800669236980397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7357295657200446157986931 11035943485800669236980397)
                ·
                  refine ⟨4138478807175250963867649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11035943485800669236980397 4138478807175250963867649)
                  ·
                    refine ⟨3103859105381438222900737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4138478807175250963867649 3103859105381438222900737)
                    ·
                      refine ⟨2327894329036078667175553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103859105381438222900737 2327894329036078667175553)
                      ·
                        rfl

theorem cell23_4533558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_4533558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533558 prefixEnd_4533558 := by exact prefixLift 4533558
  have htrace : WordTrace (prefixWord ++ tailWord_4533558) baseStart_4533558 baseEnd_4533558 := by
    simpa [prefixWord, tailWord_4533558, baseEnd_4533558] using wordTrace_append hprefix tailTrace_4533558
  have hstable : (prefixWord ++ tailWord_4533558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533558).length < 2 ^ (prefixWord ++ tailWord_4533558).sum := by decide
  have hdescent : baseEnd_4533558 < baseStart_4533558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533581 : List Nat := [1, 6, 1, 3, 2, 1, 2, 7]
def baseStart_4533581 : Nat := 118140960795 + 4533581 * 2 ^ 59
def prefixEnd_4533581 : Nat := 4983230072969 + 3 ^ 40 * 4533581 * 2
def baseEnd_4533581 : Nat := 86218745892264151006961

theorem tailTrace_4533581 : CollatzResearch.WordTrace tailWord_4533581 prefixEnd_4533581 86218745892264151006961 := by
  unfold tailWord_4533581
  simp only [CollatzResearch.WordTrace]
  refine ⟨165353283388617785836808597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110235522259078523891205731 165353283388617785836808597)
  ·
    refine ⟨7750935158841458711100403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 165353283388617785836808597 7750935158841458711100403)
    ·
      refine ⟨11626402738262188066650605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7750935158841458711100403 11626402738262188066650605)
      ·
        refine ⟨4359901026848320524993977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11626402738262188066650605 4359901026848320524993977)
        ·
          refine ⟨3269925770136240393745483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4359901026848320524993977 3269925770136240393745483)
          ·
            refine ⟨4904888655204360590618225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269925770136240393745483 4904888655204360590618225)
            ·
              refine ⟨3678666491403270442963669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4904888655204360590618225 3678666491403270442963669)
              ·
                refine ⟨86218745892264151006961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3678666491403270442963669 86218745892264151006961)
                ·
                  rfl

theorem cell23_4533581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 2, 7].length) (baseStart_4533581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533581 prefixEnd_4533581 := by exact prefixLift 4533581
  have htrace : WordTrace (prefixWord ++ tailWord_4533581) baseStart_4533581 baseEnd_4533581 := by
    simpa [prefixWord, tailWord_4533581, baseEnd_4533581] using wordTrace_append hprefix tailTrace_4533581
  have hstable : (prefixWord ++ tailWord_4533581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533581).length < 2 ^ (prefixWord ++ tailWord_4533581).sum := by decide
  have hdescent : baseEnd_4533581 < baseStart_4533581 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533583 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 3]
def baseStart_4533583 : Nat := 118140960795 + 4533583 * 2 ^ 59
def prefixEnd_4533583 : Nat := 4983230072969 + 3 ^ 40 * 4533583 * 2
def baseEnd_4533583 : Nat := 2327907166052441069362937

theorem tailTrace_4533583 : CollatzResearch.WordTrace tailWord_4533583 prefixEnd_4533583 2327907166052441069362937 := by
  unfold tailWord_4533583
  simp only [CollatzResearch.WordTrace]
  refine ⟨165353356334610540178381403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110235570889740360118920935 165353356334610540178381403)
  ·
    refine ⟨248030034501915810267572105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165353356334610540178381403 248030034501915810267572105)
    ·
      refine ⟨186022525876436857700679079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248030034501915810267572105 186022525876436857700679079)
      ·
        refine ⟨279033788814655286551018619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186022525876436857700679079 279033788814655286551018619)
        ·
          refine ⟨418550683221982929826527929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279033788814655286551018619 418550683221982929826527929)
          ·
            refine ⟨313913012416487197369895947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418550683221982929826527929 313913012416487197369895947)
            ·
              refine ⟨470869518624730796054843921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313913012416487197369895947 470869518624730796054843921)
              ·
                refine ⟨353152138968548097041132941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 470869518624730796054843921 353152138968548097041132941)
                ·
                  refine ⟨132432052113205536390424853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 353152138968548097041132941 132432052113205536390424853)
                  ·
                    refine ⟨6207752442806509518301165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 132432052113205536390424853 6207752442806509518301165)
                    ·
                      refine ⟨2327907166052441069362937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6207752442806509518301165 2327907166052441069362937)
                      ·
                        rfl

theorem cell23_4533583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 6, 3].length) (baseStart_4533583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533583 prefixEnd_4533583 := by exact prefixLift 4533583
  have htrace : WordTrace (prefixWord ++ tailWord_4533583) baseStart_4533583 baseEnd_4533583 := by
    simpa [prefixWord, tailWord_4533583, baseEnd_4533583] using wordTrace_append hprefix tailTrace_4533583
  have hstable : (prefixWord ++ tailWord_4533583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533583).length < 2 ^ (prefixWord ++ tailWord_4533583).sum := by decide
  have hdescent : baseEnd_4533583 < baseStart_4533583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533593 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 1, 4, 4]
def baseStart_4533593 : Nat := 118140960795 + 4533593 * 2 ^ 59
def prefixEnd_4533593 : Nat := 4983230072969 + 3 ^ 40 * 4533593 * 2
def baseEnd_4533593 : Nat := 2327912300858986030237891

theorem tailTrace_4533593 : CollatzResearch.WordTrace tailWord_4533593 prefixEnd_4533593 2327912300858986030237891 := by
  unfold tailWord_4533593
  simp only [CollatzResearch.WordTrace]
  refine ⟨165353721064574311886245433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110235814043049541257496955 165353721064574311886245433)
  ·
    refine ⟨124015290798430733914684075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165353721064574311886245433 124015290798430733914684075)
    ·
      refine ⟨186022936197646100872026113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124015290798430733914684075 186022936197646100872026113)
      ·
        refine ⟨139517202148234575654019585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186022936197646100872026113 139517202148234575654019585)
        ·
          refine ⟨104637901611175931740514689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139517202148234575654019585 104637901611175931740514689)
          ·
            refine ⟨78478426208381948805386017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104637901611175931740514689 78478426208381948805386017)
            ·
              refine ⟨58858819656286461604039513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78478426208381948805386017 58858819656286461604039513)
              ·
                refine ⟨44144114742214846203029635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58858819656286461604039513 44144114742214846203029635)
                ·
                  refine ⟨66216172113322269304544453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44144114742214846203029635 66216172113322269304544453)
                  ·
                    refine ⟨12415532271247925494602085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 66216172113322269304544453 12415532271247925494602085)
                    ·
                      refine ⟨2327912300858986030237891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12415532271247925494602085 2327912300858986030237891)
                      ·
                        rfl

theorem cell23_4533593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_4533593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533593 prefixEnd_4533593 := by exact prefixLift 4533593
  have htrace : WordTrace (prefixWord ++ tailWord_4533593) baseStart_4533593 baseEnd_4533593 := by
    simpa [prefixWord, tailWord_4533593, baseEnd_4533593] using wordTrace_append hprefix tailTrace_4533593
  have hstable : (prefixWord ++ tailWord_4533593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533593).length < 2 ^ (prefixWord ++ tailWord_4533593).sum := by decide
  have hdescent : baseEnd_4533593 < baseStart_4533593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533600 : List Nat := [2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 5]
def baseStart_4533600 : Nat := 118140960795 + 4533600 * 2 ^ 59
def prefixEnd_4533600 : Nat := 4983230072969 + 3 ^ 40 * 4533600 * 2
def baseEnd_4533600 : Nat := 2327915895223567502850359

theorem tailTrace_4533600 : CollatzResearch.WordTrace tailWord_4533600 prefixEnd_4533600 2327915895223567502850359 := by
  unfold tailWord_4533600
  simp only [CollatzResearch.WordTrace]
  refine ⟨82676988187774476040875127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110235984250365968054500169 82676988187774476040875127)
  ·
    refine ⟨124015482281661714061312691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82676988187774476040875127 124015482281661714061312691)
    ·
      refine ⟨186023223422492571091969037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124015482281661714061312691 186023223422492571091969037)
      ·
        refine ⟨69758708783434714159488389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186023223422492571091969037 69758708783434714159488389)
        ·
          refine ⟨13079757896894008904904073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69758708783434714159488389 13079757896894008904904073)
          ·
            refine ⟨9809818422670506678678055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13079757896894008904904073 9809818422670506678678055)
            ·
              refine ⟨14714727634005760018017083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9809818422670506678678055 14714727634005760018017083)
              ·
                refine ⟨22072091451008640027025625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14714727634005760018017083 22072091451008640027025625)
                ·
                  refine ⟨16554068588256480020269219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22072091451008640027025625 16554068588256480020269219)
                  ·
                    refine ⟨24831102882384720030403829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16554068588256480020269219 24831102882384720030403829)
                    ·
                      refine ⟨2327915895223567502850359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24831102882384720030403829 2327915895223567502850359)
                      ·
                        rfl

theorem cell23_4533600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_4533600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533600 prefixEnd_4533600 := by exact prefixLift 4533600
  have htrace : WordTrace (prefixWord ++ tailWord_4533600) baseStart_4533600 baseEnd_4533600 := by
    simpa [prefixWord, tailWord_4533600, baseEnd_4533600] using wordTrace_append hprefix tailTrace_4533600
  have hstable : (prefixWord ++ tailWord_4533600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533600).length < 2 ^ (prefixWord ++ tailWord_4533600).sum := by decide
  have hdescent : baseEnd_4533600 < baseStart_4533600 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533643 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 7]
def baseStart_4533643 : Nat := 118140960795 + 4533643 * 2 ^ 59
def prefixEnd_4533643 : Nat := 4983230072969 + 3 ^ 40 * 4533643 * 2
def baseEnd_4533643 : Nat := 2327937974891710834612661

theorem tailTrace_4533643 : CollatzResearch.WordTrace tailWord_4533643 prefixEnd_4533643 2327937974891710834612661 := by
  unfold tailWord_4533643
  simp only [CollatzResearch.WordTrace]
  refine ⟨165355544714393170425565583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110237029809595446950377055 165355544714393170425565583)
  ·
    refine ⟨248033317071589755638348375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165355544714393170425565583 248033317071589755638348375)
    ·
      refine ⟨372049975607384633457522563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248033317071589755638348375 372049975607384633457522563)
      ·
        refine ⟨558074963411076950186283845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372049975607384633457522563 558074963411076950186283845)
        ·
          refine ⟨104639055639576928159928221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 558074963411076950186283845 104639055639576928159928221)
          ·
            refine ⟨39239645864841348059973083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104639055639576928159928221 39239645864841348059973083)
            ·
              refine ⟨58859468797262022089959625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39239645864841348059973083 58859468797262022089959625)
              ·
                refine ⟨44144601597946516567469719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58859468797262022089959625 44144601597946516567469719)
                ·
                  refine ⟨66216902396919774851204579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44144601597946516567469719 66216902396919774851204579)
                  ·
                    refine ⟨99325353595379662276806869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 66216902396919774851204579 99325353595379662276806869)
                    ·
                      refine ⟨2327937974891710834612661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 99325353595379662276806869 2327937974891710834612661)
                      ·
                        rfl

theorem cell23_4533643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 1, 7].length) (baseStart_4533643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533643 prefixEnd_4533643 := by exact prefixLift 4533643
  have htrace : WordTrace (prefixWord ++ tailWord_4533643) baseStart_4533643 baseEnd_4533643 := by
    simpa [prefixWord, tailWord_4533643, baseEnd_4533643] using wordTrace_append hprefix tailTrace_4533643
  have hstable : (prefixWord ++ tailWord_4533643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533643).length < 2 ^ (prefixWord ++ tailWord_4533643).sum := by decide
  have hdescent : baseEnd_4533643 < baseStart_4533643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533677 : List Nat := [1, 5, 2, 2, 1, 1, 2, 1, 1, 2, 5]
def baseStart_4533677 : Nat := 118140960795 + 4533677 * 2 ^ 59
def prefixEnd_4533677 : Nat := 4983230072969 + 3 ^ 40 * 4533677 * 2
def baseEnd_4533677 : Nat := 2327955433233963701587505

theorem tailTrace_4533677 : CollatzResearch.WordTrace tailWord_4533677 prefixEnd_4533677 2327955433233963701587505 := by
  unfold tailWord_4533677
  simp only [CollatzResearch.WordTrace]
  refine ⟨165356784796269994232303285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110237856530846662821535523 165356784796269994232303285)
  ·
    refine ⟨15502198574650311959278433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165356784796269994232303285 15502198574650311959278433)
    ·
      refine ⟨11626648930987733969458825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15502198574650311959278433 11626648930987733969458825)
      ·
        refine ⟨8719986698240800477094119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11626648930987733969458825 8719986698240800477094119)
        ·
          refine ⟨13079980047361200715641179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8719986698240800477094119 13079980047361200715641179)
          ·
            refine ⟨19619970071041801073461769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13079980047361200715641179 19619970071041801073461769)
            ·
              refine ⟨14714977553281350805096327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19619970071041801073461769 14714977553281350805096327)
              ·
                refine ⟨22072466329922026207644491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14714977553281350805096327 22072466329922026207644491)
                ·
                  refine ⟨33108699494883039311466737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22072466329922026207644491 33108699494883039311466737)
                  ·
                    refine ⟨24831524621162279483600053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33108699494883039311466737 24831524621162279483600053)
                    ·
                      refine ⟨2327955433233963701587505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24831524621162279483600053 2327955433233963701587505)
                      ·
                        rfl

theorem cell23_4533677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_4533677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533677 prefixEnd_4533677 := by exact prefixLift 4533677
  have htrace : WordTrace (prefixWord ++ tailWord_4533677) baseStart_4533677 baseEnd_4533677 := by
    simpa [prefixWord, tailWord_4533677, baseEnd_4533677] using wordTrace_append hprefix tailTrace_4533677
  have hstable : (prefixWord ++ tailWord_4533677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533677).length < 2 ^ (prefixWord ++ tailWord_4533677).sum := by decide
  have hdescent : baseEnd_4533677 < baseStart_4533677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533687 : List Nat := [1, 1, 3, 1, 3, 2, 3, 1, 2, 4, 2]
def baseStart_4533687 : Nat := 118140960795 + 4533687 * 2 ^ 59
def prefixEnd_4533687 : Nat := 4983230072969 + 3 ^ 40 * 4533687 * 2
def baseEnd_4533687 : Nat := 2327960568040508662462459

theorem tailTrace_4533687 : CollatzResearch.WordTrace tailWord_4533687 prefixEnd_4533687 2327960568040508662462459 := by
  unfold tailWord_4533687
  simp only [CollatzResearch.WordTrace]
  refine ⟨165357149526233765940167315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110238099684155843960111543 165357149526233765940167315)
  ·
    refine ⟨248035724289350648910250973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165357149526233765940167315 248035724289350648910250973)
    ·
      refine ⟨93013396608506493341344115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248035724289350648910250973 93013396608506493341344115)
      ·
        refine ⟨139520094912759740012016173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93013396608506493341344115 139520094912759740012016173)
        ·
          refine ⟨52320035592284902504506065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139520094912759740012016173 52320035592284902504506065)
          ·
            refine ⟨39240026694213676878379549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52320035592284902504506065 39240026694213676878379549)
            ·
              refine ⟨14715010010330128829392331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39240026694213676878379549 14715010010330128829392331)
              ·
                refine ⟨22072515015495193244088497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14715010010330128829392331 22072515015495193244088497)
                ·
                  refine ⟨16554386261621394933066373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22072515015495193244088497 16554386261621394933066373)
                  ·
                    refine ⟨3103947424054011549949945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16554386261621394933066373 3103947424054011549949945)
                    ·
                      refine ⟨2327960568040508662462459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103947424054011549949945 2327960568040508662462459)
                      ·
                        rfl

theorem cell23_4533687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 4, 2].length) (baseStart_4533687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533687 prefixEnd_4533687 := by exact prefixLift 4533687
  have htrace : WordTrace (prefixWord ++ tailWord_4533687) baseStart_4533687 baseEnd_4533687 := by
    simpa [prefixWord, tailWord_4533687, baseEnd_4533687] using wordTrace_append hprefix tailTrace_4533687
  have hstable : (prefixWord ++ tailWord_4533687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533687).length < 2 ^ (prefixWord ++ tailWord_4533687).sum := by decide
  have hdescent : baseEnd_4533687 < baseStart_4533687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533707 : List Nat := [1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 3]
def baseStart_4533707 : Nat := 118140960795 + 4533707 * 2 ^ 59
def prefixEnd_4533707 : Nat := 4983230072969 + 3 ^ 40 * 4533707 * 2
def baseEnd_4533707 : Nat := 2327970837653598584212367

theorem tailTrace_4533707 : CollatzResearch.WordTrace tailWord_4533707 prefixEnd_4533707 2327970837653598584212367 := by
  unfold tailWord_4533707
  simp only [CollatzResearch.WordTrace]
  refine ⟨165357878986161309355895375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110238585990774206237263583 165357878986161309355895375)
  ·
    refine ⟨248036818479241964033843063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165357878986161309355895375 248036818479241964033843063)
    ·
      refine ⟨372055227718862946050764595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248036818479241964033843063 372055227718862946050764595)
      ·
        refine ⟨558082841578294419076146893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372055227718862946050764595 558082841578294419076146893)
        ·
          refine ⟨209281065591860407153555085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 558082841578294419076146893 209281065591860407153555085)
          ·
            refine ⟨78480399596947652682583157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209281065591860407153555085 78480399596947652682583157)
            ·
              refine ⟨7357537462213842438992171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78480399596947652682583157 7357537462213842438992171)
              ·
                refine ⟨11036306193320763658488257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7357537462213842438992171 11036306193320763658488257)
                ·
                  refine ⟨8277229644990572743866193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11036306193320763658488257 8277229644990572743866193)
                  ·
                    refine ⟨6207922233742929557899645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8277229644990572743866193 6207922233742929557899645)
                    ·
                      refine ⟨2327970837653598584212367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6207922233742929557899645 2327970837653598584212367)
                      ·
                        rfl

theorem cell23_4533707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 5, 1, 2, 2, 3].length) (baseStart_4533707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533707 prefixEnd_4533707 := by exact prefixLift 4533707
  have htrace : WordTrace (prefixWord ++ tailWord_4533707) baseStart_4533707 baseEnd_4533707 := by
    simpa [prefixWord, tailWord_4533707, baseEnd_4533707] using wordTrace_append hprefix tailTrace_4533707
  have hstable : (prefixWord ++ tailWord_4533707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533707).length < 2 ^ (prefixWord ++ tailWord_4533707).sum := by decide
  have hdescent : baseEnd_4533707 < baseStart_4533707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533740 : List Nat := [2, 2, 1, 1, 2, 1, 2, 4, 3, 5]
def baseStart_4533740 : Nat := 118140960795 + 4533740 * 2 ^ 59
def prefixEnd_4533740 : Nat := 4983230072969 + 3 ^ 40 * 4533740 * 2
def baseEnd_4533740 : Nat := 775995927505065651699905

theorem tailTrace_4533740 : CollatzResearch.WordTrace tailWord_4533740 prefixEnd_4533740 775995927505065651699905 := by
  unfold tailWord_4533740
  simp only [CollatzResearch.WordTrace]
  refine ⟨82679541297520877995923337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110239388396694503994564449 82679541297520877995923337)
  ·
    refine ⟨62009655973140658496942503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82679541297520877995923337 62009655973140658496942503)
    ·
      refine ⟨93014483959710987745413755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62009655973140658496942503 93014483959710987745413755)
      ·
        refine ⟨139521725939566481618120633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93014483959710987745413755 139521725939566481618120633)
        ·
          refine ⟨104641294454674861213590475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139521725939566481618120633 104641294454674861213590475)
          ·
            refine ⟨156961941682012291820385713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104641294454674861213590475 156961941682012291820385713)
            ·
              refine ⟨117721456261509218865289285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156961941682012291820385713 117721456261509218865289285)
              ·
                refine ⟨22072773049032978537241741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117721456261509218865289285 22072773049032978537241741)
                ·
                  refine ⟨8277289893387366951465653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22072773049032978537241741 8277289893387366951465653)
                  ·
                    refine ⟨775995927505065651699905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8277289893387366951465653 775995927505065651699905)
                    ·
                      rfl

theorem cell23_4533740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 5].length) (baseStart_4533740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533740 prefixEnd_4533740 := by exact prefixLift 4533740
  have htrace : WordTrace (prefixWord ++ tailWord_4533740) baseStart_4533740 baseEnd_4533740 := by
    simpa [prefixWord, tailWord_4533740, baseEnd_4533740] using wordTrace_append hprefix tailTrace_4533740
  have hstable : (prefixWord ++ tailWord_4533740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533740).length < 2 ^ (prefixWord ++ tailWord_4533740).sum := by decide
  have hdescent : baseEnd_4533740 < baseStart_4533740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533747 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 6, 3, 2]
def baseStart_4533747 : Nat := 118140960795 + 4533747 * 2 ^ 59
def prefixEnd_4533747 : Nat := 4983230072969 + 3 ^ 40 * 4533747 * 2
def baseEnd_4533747 : Nat := 2327991376879778427712183

theorem tailTrace_4533747 : CollatzResearch.WordTrace tailWord_4533747 prefixEnd_4533747 2327991376879778427712183 := by
  unfold tailWord_4533747
  simp only [CollatzResearch.WordTrace]
  refine ⟨165359337906016396187351495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110239558604010930791567663 165359337906016396187351495)
  ·
    refine ⟨248039006859024594281027243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165359337906016396187351495 248039006859024594281027243)
    ·
      refine ⟨372058510288536891421540865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248039006859024594281027243 372058510288536891421540865)
      ·
        refine ⟨279043882716402668566155649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372058510288536891421540865 279043882716402668566155649)
        ·
          refine ⟨209282912037302001424616737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279043882716402668566155649 209282912037302001424616737)
          ·
            refine ⟨156962184027976501068462553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209282912037302001424616737 156962184027976501068462553)
            ·
              refine ⟨117721638020982375801346915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156962184027976501068462553 117721638020982375801346915)
              ·
                refine ⟨176582457031473563702020373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117721638020982375801346915 176582457031473563702020373)
                ·
                  refine ⟨8277302673350323298532205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 176582457031473563702020373 8277302673350323298532205)
                  ·
                    refine ⟨3103988502506371236949577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8277302673350323298532205 3103988502506371236949577)
                    ·
                      refine ⟨2327991376879778427712183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3103988502506371236949577 2327991376879778427712183)
                      ·
                        rfl

theorem cell23_4533747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 6, 3, 2].length) (baseStart_4533747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533747 prefixEnd_4533747 := by exact prefixLift 4533747
  have htrace : WordTrace (prefixWord ++ tailWord_4533747) baseStart_4533747 baseEnd_4533747 := by
    simpa [prefixWord, tailWord_4533747, baseEnd_4533747] using wordTrace_append hprefix tailTrace_4533747
  have hstable : (prefixWord ++ tailWord_4533747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533747).length < 2 ^ (prefixWord ++ tailWord_4533747).sum := by decide
  have hdescent : baseEnd_4533747 < baseStart_4533747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533757 : List Nat := [1, 4, 1, 1, 1, 4, 1, 4, 1, 5]
def baseStart_4533757 : Nat := 118140960795 + 4533757 * 2 ^ 59
def prefixEnd_4533757 : Nat := 4983230072969 + 3 ^ 40 * 4533757 * 2
def baseEnd_4533757 : Nat := 775998837228774462862379

theorem tailTrace_4533757 : CollatzResearch.WordTrace tailWord_4533757 prefixEnd_4533757 775998837228774462862379 := by
  unfold tailWord_4533757
  simp only [CollatzResearch.WordTrace]
  refine ⟨165359702635980167895215525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110239801757320111930143683 165359702635980167895215525)
  ·
    refine ⟨31004944244246281480352911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165359702635980167895215525 31004944244246281480352911)
    ·
      refine ⟨46507416366369422220529367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31004944244246281480352911 46507416366369422220529367)
      ·
        refine ⟨69761124549554133330794051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46507416366369422220529367 69761124549554133330794051)
        ·
          refine ⟨104641686824331199996191077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69761124549554133330794051 104641686824331199996191077)
          ·
            refine ⟨19620316279562099999285827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104641686824331199996191077 19620316279562099999285827)
            ·
              refine ⟨29430474419343149998928741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19620316279562099999285827 29430474419343149998928741)
              ·
                refine ⟨5518213953626840624799139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29430474419343149998928741 5518213953626840624799139)
                ·
                  refine ⟨8277320930440260937198709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5518213953626840624799139 8277320930440260937198709)
                  ·
                    refine ⟨775998837228774462862379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8277320930440260937198709 775998837228774462862379)
                    ·
                      rfl

theorem cell23_4533757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 4, 1, 5].length) (baseStart_4533757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533757 prefixEnd_4533757 := by exact prefixLift 4533757
  have htrace : WordTrace (prefixWord ++ tailWord_4533757) baseStart_4533757 baseEnd_4533757 := by
    simpa [prefixWord, tailWord_4533757, baseEnd_4533757] using wordTrace_append hprefix tailTrace_4533757
  have hstable : (prefixWord ++ tailWord_4533757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533757).length < 2 ^ (prefixWord ++ tailWord_4533757).sum := by decide
  have hdescent : baseEnd_4533757 < baseStart_4533757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533777 : List Nat := [1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 4]
def baseStart_4533777 : Nat := 118140960795 + 4533777 * 2 ^ 59
def prefixEnd_4533777 : Nat := 4983230072969 + 3 ^ 40 * 4533777 * 2
def baseEnd_4533777 : Nat := 2328006781299413310337045

theorem tailTrace_4533777 : CollatzResearch.WordTrace tailWord_4533777 prefixEnd_4533777 2328006781299413310337045 := by
  unfold tailWord_4533777
  simp only [CollatzResearch.WordTrace]
  refine ⟨165360432095907711310943585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110240288063938474207295723 165360432095907711310943585)
  ·
    refine ⟨124020324071930783483207689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165360432095907711310943585 124020324071930783483207689)
    ·
      refine ⟨93015243053948087612405767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124020324071930783483207689 93015243053948087612405767)
      ·
        refine ⟨139522864580922131418608651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93015243053948087612405767 139522864580922131418608651)
        ·
          refine ⟨209284296871383197127912977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139522864580922131418608651 209284296871383197127912977)
          ·
            refine ⟨156963222653537397845934733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209284296871383197127912977 156963222653537397845934733)
            ·
              refine ⟨58861208495076524192225525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156963222653537397845934733 58861208495076524192225525)
              ·
                refine ⟨5518238296413424143021143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58861208495076524192225525 5518238296413424143021143)
                ·
                  refine ⟨8277357444620136214531715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5518238296413424143021143 8277357444620136214531715)
                  ·
                    refine ⟨12416036166930204321797573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8277357444620136214531715 12416036166930204321797573)
                    ·
                      refine ⟨2328006781299413310337045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12416036166930204321797573 2328006781299413310337045)
                      ·
                        rfl

theorem cell23_4533777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_4533777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533777 prefixEnd_4533777 := by exact prefixLift 4533777
  have htrace : WordTrace (prefixWord ++ tailWord_4533777) baseStart_4533777 baseEnd_4533777 := by
    simpa [prefixWord, tailWord_4533777, baseEnd_4533777] using wordTrace_append hprefix tailTrace_4533777
  have hstable : (prefixWord ++ tailWord_4533777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533777).length < 2 ^ (prefixWord ++ tailWord_4533777).sum := by decide
  have hdescent : baseEnd_4533777 < baseStart_4533777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533788 : List Nat := [2, 2, 3, 1, 2, 1, 5, 2, 1, 1, 3]
def baseStart_4533788 : Nat := 118140960795 + 4533788 * 2 ^ 59
def prefixEnd_4533788 : Nat := 4983230072969 + 3 ^ 40 * 4533788 * 2
def baseEnd_4533788 : Nat := 2328012429586612767299495

theorem tailTrace_4533788 : CollatzResearch.WordTrace tailWord_4533788 prefixEnd_4533788 2328012429586612767299495 := by
  unfold tailWord_4533788
  simp only [CollatzResearch.WordTrace]
  refine ⟨82680416649433930094797009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110240555532578573459729345 82680416649433930094797009)
  ·
    refine ⟨62010312487075447571097757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82680416649433930094797009 62010312487075447571097757)
    ·
      refine ⟨23253867182653292839161659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62010312487075447571097757 23253867182653292839161659)
      ·
        refine ⟨34880800773979939258742489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23253867182653292839161659 34880800773979939258742489)
        ·
          refine ⟨26160600580484954444056867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34880800773979939258742489 26160600580484954444056867)
          ·
            refine ⟨39240900870727431666085301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26160600580484954444056867 39240900870727431666085301)
            ·
              refine ⟨3678834456630696718695497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39240900870727431666085301 3678834456630696718695497)
              ·
                refine ⟨2759125842473022539021623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3678834456630696718695497 2759125842473022539021623)
                ·
                  refine ⟨4138688763709533808532435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759125842473022539021623 4138688763709533808532435)
                  ·
                    refine ⟨6208033145564300712798653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4138688763709533808532435 6208033145564300712798653)
                    ·
                      refine ⟨2328012429586612767299495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6208033145564300712798653 2328012429586612767299495)
                      ·
                        rfl

theorem cell23_4533788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_4533788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533788 prefixEnd_4533788 := by exact prefixLift 4533788
  have htrace : WordTrace (prefixWord ++ tailWord_4533788) baseStart_4533788 baseEnd_4533788 := by
    simpa [prefixWord, tailWord_4533788, baseEnd_4533788] using wordTrace_append hprefix tailTrace_4533788
  have hstable : (prefixWord ++ tailWord_4533788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533788).length < 2 ^ (prefixWord ++ tailWord_4533788).sum := by decide
  have hdescent : baseEnd_4533788 < baseStart_4533788 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533797 : List Nat := [1, 3, 1, 2, 2, 1, 1, 4, 3, 2, 3]
def baseStart_4533797 : Nat := 118140960795 + 4533797 * 2 ^ 59
def prefixEnd_4533797 : Nat := 4983230072969 + 3 ^ 40 * 4533797 * 2
def baseEnd_4533797 : Nat := 2328017050912503232086953

theorem tailTrace_4533797 : CollatzResearch.WordTrace tailWord_4533797 prefixEnd_4533797 2328017050912503232086953 := by
  unfold tailWord_4533797
  simp only [CollatzResearch.WordTrace]
  refine ⟨165361161555835254726671645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110240774370556836484447763 165361161555835254726671645)
  ·
    refine ⟨62010435583438220522501867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165361161555835254726671645 62010435583438220522501867)
    ·
      refine ⟨93015653375157330783752801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62010435583438220522501867 93015653375157330783752801)
      ·
        refine ⟨69761740031367998087814601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93015653375157330783752801 69761740031367998087814601)
        ·
          refine ⟨52321305023525998565860951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69761740031367998087814601 52321305023525998565860951)
          ·
            refine ⟨78481957535288997848791427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52321305023525998565860951 78481957535288997848791427)
            ·
              refine ⟨117722936302933496773187141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78481957535288997848791427 117722936302933496773187141)
              ·
                refine ⟨22073050556800030644972589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117722936302933496773187141 22073050556800030644972589)
                ·
                  refine ⟨8277393958800011491864721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22073050556800030644972589 8277393958800011491864721)
                  ·
                    refine ⟨6208045469100008618898541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8277393958800011491864721 6208045469100008618898541)
                    ·
                      refine ⟨2328017050912503232086953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6208045469100008618898541 2328017050912503232086953)
                      ·
                        rfl

theorem cell23_4533797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_4533797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533797 prefixEnd_4533797 := by exact prefixLift 4533797
  have htrace : WordTrace (prefixWord ++ tailWord_4533797) baseStart_4533797 baseEnd_4533797 := by
    simpa [prefixWord, tailWord_4533797, baseEnd_4533797] using wordTrace_append hprefix tailTrace_4533797
  have hstable : (prefixWord ++ tailWord_4533797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533797).length < 2 ^ (prefixWord ++ tailWord_4533797).sum := by decide
  have hdescent : baseEnd_4533797 < baseStart_4533797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533831 : List Nat := [1, 1, 4, 1, 6, 1, 1, 1, 1, 1, 5]
def baseStart_4533831 : Nat := 118140960795 + 4533831 * 2 ^ 59
def prefixEnd_4533831 : Nat := 4983230072969 + 3 ^ 40 * 4533831 * 2
def baseEnd_4533831 : Nat := 2328034509254756099061797

theorem tailTrace_4533831 : CollatzResearch.WordTrace tailWord_4533831 prefixEnd_4533831 2328034509254756099061797 := by
  unfold tailWord_4533831
  simp only [CollatzResearch.WordTrace]
  refine ⟨165362401637712078533409347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110241601091808052355606231 165362401637712078533409347)
  ·
    refine ⟨248043602456568117800114021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165362401637712078533409347 248043602456568117800114021)
    ·
      refine ⟨46508175460606522087521379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 248043602456568117800114021 46508175460606522087521379)
      ·
        refine ⟨69762263190909783131282069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46508175460606522087521379 69762263190909783131282069)
        ·
          refine ⟨3270106087073896084278847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69762263190909783131282069 3270106087073896084278847)
          ·
            refine ⟨4905159130610844126418271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3270106087073896084278847 4905159130610844126418271)
            ·
              refine ⟨7357738695916266189627407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4905159130610844126418271 7357738695916266189627407)
              ·
                refine ⟨11036608043874399284441111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7357738695916266189627407 11036608043874399284441111)
                ·
                  refine ⟨16554912065811598926661667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11036608043874399284441111 16554912065811598926661667)
                  ·
                    refine ⟨24832368098717398389992501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16554912065811598926661667 24832368098717398389992501)
                    ·
                      refine ⟨2328034509254756099061797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24832368098717398389992501 2328034509254756099061797)
                      ·
                        rfl

theorem cell23_4533831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_4533831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533831 prefixEnd_4533831 := by exact prefixLift 4533831
  have htrace : WordTrace (prefixWord ++ tailWord_4533831) baseStart_4533831 baseEnd_4533831 := by
    simpa [prefixWord, tailWord_4533831, baseEnd_4533831] using wordTrace_append hprefix tailTrace_4533831
  have hstable : (prefixWord ++ tailWord_4533831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533831).length < 2 ^ (prefixWord ++ tailWord_4533831).sum := by decide
  have hdescent : baseEnd_4533831 < baseStart_4533831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533861 : List Nat := [1, 3, 1, 3, 3, 1, 2, 3, 2, 1, 3]
def baseStart_4533861 : Nat := 118140960795 + 4533861 * 2 ^ 59
def prefixEnd_4533861 : Nat := 4983230072969 + 3 ^ 40 * 4533861 * 2
def baseEnd_4533861 : Nat := 2328049913674390981686659

theorem tailTrace_4533861 : CollatzResearch.WordTrace tailWord_4533861 prefixEnd_4533861 2328049913674390981686659 := by
  unfold tailWord_4533861
  simp only [CollatzResearch.WordTrace]
  refine ⟨165363495827603393657001437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110242330551735595771334291 165363495827603393657001437)
  ·
    refine ⟨62011310935351272621375539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165363495827603393657001437 62011310935351272621375539)
    ·
      refine ⟨93016966403026908932063309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62011310935351272621375539 93016966403026908932063309)
      ·
        refine ⟨34881362401135090849523741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93016966403026908932063309 34881362401135090849523741)
        ·
          refine ⟨13080510900425659068571403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34881362401135090849523741 13080510900425659068571403)
          ·
            refine ⟨19620766350638488602857105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13080510900425659068571403 19620766350638488602857105)
            ·
              refine ⟨14715574762978866452142829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19620766350638488602857105 14715574762978866452142829)
              ·
                refine ⟨5518340536117074919553561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14715574762978866452142829 5518340536117074919553561)
                ·
                  refine ⟨4138755402087806189665171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5518340536117074919553561 4138755402087806189665171)
                  ·
                    refine ⟨6208133103131709284497757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4138755402087806189665171 6208133103131709284497757)
                    ·
                      refine ⟨2328049913674390981686659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6208133103131709284497757 2328049913674390981686659)
                      ·
                        rfl

theorem cell23_4533861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_4533861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533861 prefixEnd_4533861 := by exact prefixLift 4533861
  have htrace : WordTrace (prefixWord ++ tailWord_4533861) baseStart_4533861 baseEnd_4533861 := by
    simpa [prefixWord, tailWord_4533861, baseEnd_4533861] using wordTrace_append hprefix tailTrace_4533861
  have hstable : (prefixWord ++ tailWord_4533861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533861).length < 2 ^ (prefixWord ++ tailWord_4533861).sum := by decide
  have hdescent : baseEnd_4533861 < baseStart_4533861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533897 : List Nat := [1, 2, 1, 1, 4, 1, 3, 2, 2, 2, 4]
def baseStart_4533897 : Nat := 118140960795 + 4533897 * 2 ^ 59
def prefixEnd_4533897 : Nat := 4983230072969 + 3 ^ 40 * 4533897 * 2
def baseEnd_4533897 : Nat := 2328068398977952840836493

theorem tailTrace_4533897 : CollatzResearch.WordTrace tailWord_4533897 prefixEnd_4533897 2328068398977952840836493 := by
  unfold tailWord_4533897
  simp only [CollatzResearch.WordTrace]
  refine ⟨165364808855472971805311945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110243205903648647870207963 165364808855472971805311945)
  ·
    refine ⟨124023606641604728853983959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165364808855472971805311945 124023606641604728853983959)
    ·
      refine ⟨186035409962407093280975939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124023606641604728853983959 186035409962407093280975939)
      ·
        refine ⟨279053114943610639921463909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186035409962407093280975939 279053114943610639921463909)
        ·
          refine ⟨52322459051926994985274483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 279053114943610639921463909 52322459051926994985274483)
          ·
            refine ⟨78483688577890492477911725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52322459051926994985274483 78483688577890492477911725)
            ·
              refine ⟨29431383216708934679216897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78483688577890492477911725 29431383216708934679216897)
              ·
                refine ⟨22073537412531701009412673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29431383216708934679216897 22073537412531701009412673)
                ·
                  refine ⟨16555153059398775757059505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22073537412531701009412673 16555153059398775757059505)
                  ·
                    refine ⟨12416364794549081817794629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16555153059398775757059505 12416364794549081817794629)
                    ·
                      refine ⟨2328068398977952840836493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12416364794549081817794629 2328068398977952840836493)
                      ·
                        rfl

theorem cell23_4533897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 2, 4].length) (baseStart_4533897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533897 prefixEnd_4533897 := by exact prefixLift 4533897
  have htrace : WordTrace (prefixWord ++ tailWord_4533897) baseStart_4533897 baseEnd_4533897 := by
    simpa [prefixWord, tailWord_4533897, baseEnd_4533897] using wordTrace_append hprefix tailTrace_4533897
  have hstable : (prefixWord ++ tailWord_4533897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533897).length < 2 ^ (prefixWord ++ tailWord_4533897).sum := by decide
  have hdescent : baseEnd_4533897 < baseStart_4533897 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533918 : List Nat := [4, 3, 1, 1, 1, 2, 3, 1, 1, 4, 2]
def baseStart_4533918 : Nat := 118140960795 + 4533918 * 2 ^ 59
def prefixEnd_4533918 : Nat := 4983230072969 + 3 ^ 40 * 4533918 * 2
def baseEnd_4533918 : Nat := 2328079182071697258673897

theorem tailTrace_4533918 : CollatzResearch.WordTrace tailWord_4533918 prefixEnd_4533918 2328079182071697258673897 := by
  unfold tailWord_4533918
  simp only [CollatzResearch.WordTrace]
  refine ⟨20670696848549611548978301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110243716525597928261217605 20670696848549611548978301)
  ·
    refine ⟨7751511318206104330866863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20670696848549611548978301 7751511318206104330866863)
    ·
      refine ⟨11627266977309156496300295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7751511318206104330866863 11627266977309156496300295)
      ·
        refine ⟨17440900465963734744450443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11627266977309156496300295 17440900465963734744450443)
        ·
          refine ⟨26161350698945602116675665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17440900465963734744450443 26161350698945602116675665)
          ·
            refine ⟨19621013024209201587506749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26161350698945602116675665 19621013024209201587506749)
            ·
              refine ⟨7357879884078450595315031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19621013024209201587506749 7357879884078450595315031)
              ·
                refine ⟨11036819826117675892972547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7357879884078450595315031 11036819826117675892972547)
                ·
                  refine ⟨16555229739176513839458821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11036819826117675892972547 16555229739176513839458821)
                  ·
                    refine ⟨3104105576095596344898529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16555229739176513839458821 3104105576095596344898529)
                    ·
                      refine ⟨2328079182071697258673897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3104105576095596344898529 2328079182071697258673897)
                      ·
                        rfl

theorem cell23_4533918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 3, 1, 1, 4, 2].length) (baseStart_4533918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533918 prefixEnd_4533918 := by exact prefixLift 4533918
  have htrace : WordTrace (prefixWord ++ tailWord_4533918) baseStart_4533918 baseEnd_4533918 := by
    simpa [prefixWord, tailWord_4533918, baseEnd_4533918] using wordTrace_append hprefix tailTrace_4533918
  have hstable : (prefixWord ++ tailWord_4533918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533918).length < 2 ^ (prefixWord ++ tailWord_4533918).sum := by decide
  have hdescent : baseEnd_4533918 < baseStart_4533918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533958 : List Nat := [6, 1, 2, 1, 1, 1, 3, 1, 7]
def baseStart_4533958 : Nat := 118140960795 + 4533958 * 2 ^ 59
def prefixEnd_4533958 : Nat := 4983230072969 + 3 ^ 40 * 4533958 * 2
def baseEnd_4533958 : Nat := 258677746810875233574857

theorem tailTrace_4533958 : CollatzResearch.WordTrace tailWord_4533958 prefixEnd_4533958 258677746810875233574857 := by
  unfold tailWord_4533958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5167719803382874350727579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 110244689138834652815521685 5167719803382874350727579)
  ·
    refine ⟨7751579705074311526091369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5167719803382874350727579 7751579705074311526091369)
    ·
      refine ⟨5813684778805733644568527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7751579705074311526091369 5813684778805733644568527)
      ·
        refine ⟨8720527168208600466852791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5813684778805733644568527 8720527168208600466852791)
        ·
          refine ⟨13080790752312900700279187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8720527168208600466852791 13080790752312900700279187)
          ·
            refine ⟨19621186128469351050418781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13080790752312900700279187 19621186128469351050418781)
            ·
              refine ⟨7357944798176006643907043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19621186128469351050418781 7357944798176006643907043)
              ·
                refine ⟨11036917197264009965860565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7357944798176006643907043 11036917197264009965860565)
                ·
                  refine ⟨258677746810875233574857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11036917197264009965860565 258677746810875233574857)
                  ·
                    rfl

theorem cell23_4533958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_4533958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533958 prefixEnd_4533958 := by exact prefixLift 4533958
  have htrace : WordTrace (prefixWord ++ tailWord_4533958) baseStart_4533958 baseEnd_4533958 := by
    simpa [prefixWord, tailWord_4533958, baseEnd_4533958] using wordTrace_append hprefix tailTrace_4533958
  have hstable : (prefixWord ++ tailWord_4533958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533958).length < 2 ^ (prefixWord ++ tailWord_4533958).sum := by decide
  have hdescent : baseEnd_4533958 < baseStart_4533958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533984 : List Nat := [2, 1, 1, 3, 1, 2, 2, 4, 3, 4]
def baseStart_4533984 : Nat := 118140960795 + 4533984 * 2 ^ 59
def prefixEnd_4533984 : Nat := 4983230072969 + 3 ^ 40 * 4533984 * 2
def baseEnd_4533984 : Nat := 776037690598298000149531

theorem tailTrace_4533984 : CollatzResearch.WordTrace tailWord_4533984 prefixEnd_4533984 776037690598298000149531 := by
  unfold tailWord_4533984
  simp only [CollatzResearch.WordTrace]
  refine ⟨82683991003078892831864503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110245321337438523775819337 82683991003078892831864503)
  ·
    refine ⟨124025986504618339247796755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82683991003078892831864503 124025986504618339247796755)
    ·
      refine ⟨186038979756927508871695133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124025986504618339247796755 186038979756927508871695133)
      ·
        refine ⟨69764617408847815826885675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186038979756927508871695133 69764617408847815826885675)
        ·
          refine ⟨104646926113271723740328513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69764617408847815826885675 104646926113271723740328513)
          ·
            refine ⟨78485194584953792805246385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104646926113271723740328513 78485194584953792805246385)
            ·
              refine ⟨58863895938715344603934789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78485194584953792805246385 58863895938715344603934789)
              ·
                refine ⟨11036980488509127113237773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58863895938715344603934789 11036980488509127113237773)
                ·
                  refine ⟨4138867683190922667464165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11036980488509127113237773 4138867683190922667464165)
                  ·
                    refine ⟨776037690598298000149531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4138867683190922667464165 776037690598298000149531)
                    ·
                      rfl

theorem cell23_4533984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 4, 3, 4].length) (baseStart_4533984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533984 prefixEnd_4533984 := by exact prefixLift 4533984
  have htrace : WordTrace (prefixWord ++ tailWord_4533984) baseStart_4533984 baseEnd_4533984 := by
    simpa [prefixWord, tailWord_4533984, baseEnd_4533984] using wordTrace_append hprefix tailTrace_4533984
  have hstable : (prefixWord ++ tailWord_4533984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533984).length < 2 ^ (prefixWord ++ tailWord_4533984).sum := by decide
  have hdescent : baseEnd_4533984 < baseStart_4533984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4533994 : List Nat := [3, 1, 3, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_4533994 : Nat := 118140960795 + 4533994 * 2 ^ 59
def prefixEnd_4533994 : Nat := 4983230072969 + 3 ^ 40 * 4533994 * 2
def baseEnd_4533994 : Nat := 2328118206601438961323547

theorem tailTrace_4533994 : CollatzResearch.WordTrace tailWord_4533994 prefixEnd_4533994 2328118206601438961323547 := by
  unfold tailWord_4533994
  simp only [CollatzResearch.WordTrace]
  refine ⟨41342086684030389342898259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110245564490747704914395357 41342086684030389342898259)
  ·
    refine ⟨62013130026045584014347389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41342086684030389342898259 62013130026045584014347389)
    ·
      refine ⟨23254923759767094005380271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62013130026045584014347389 23254923759767094005380271)
      ·
        refine ⟨34882385639650641008070407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23254923759767094005380271 34882385639650641008070407)
        ·
          refine ⟨52323578459475961512105611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34882385639650641008070407 52323578459475961512105611)
          ·
            refine ⟨78485367689213942268158417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52323578459475961512105611 78485367689213942268158417)
            ·
              refine ⟨58864025766910456701118813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78485367689213942268158417 58864025766910456701118813)
              ·
                refine ⟨22074009662591421262919555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58864025766910456701118813 22074009662591421262919555)
                ·
                  refine ⟨33111014493887131894379333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22074009662591421262919555 33111014493887131894379333)
                  ·
                    refine ⟨6208315217603837230196125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33111014493887131894379333 6208315217603837230196125)
                    ·
                      refine ⟨2328118206601438961323547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6208315217603837230196125 2328118206601438961323547)
                      ·
                        rfl

theorem cell23_4533994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_4533994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4533994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4533994 prefixEnd_4533994 := by exact prefixLift 4533994
  have htrace : WordTrace (prefixWord ++ tailWord_4533994) baseStart_4533994 baseEnd_4533994 := by
    simpa [prefixWord, tailWord_4533994, baseEnd_4533994] using wordTrace_append hprefix tailTrace_4533994
  have hstable : (prefixWord ++ tailWord_4533994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4533994).length < 2 ^ (prefixWord ++ tailWord_4533994).sum := by decide
  have hdescent : baseEnd_4533994 < baseStart_4533994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4533994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534044 : List Nat := [2, 2, 3, 1, 1, 2, 1, 3, 3, 5]
def baseStart_4534044 : Nat := 118140960795 + 4534044 * 2 ^ 59
def prefixEnd_4534044 : Nat := 4983230072969 + 3 ^ 40 * 4534044 * 2
def baseEnd_4534044 : Nat := 776047960211387921899439

theorem tailTrace_4534044 : CollatzResearch.WordTrace tailWord_4534044 prefixEnd_4534044 776047960211387921899439 := by
  unfold tailWord_4534044
  simp only [CollatzResearch.WordTrace]
  refine ⟨82685085192970207955456593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110246780257293610607275457 82685085192970207955456593)
  ·
    refine ⟨62013813894727655966592445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82685085192970207955456593 62013813894727655966592445)
    ·
      refine ⟨23255180210522870987472167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62013813894727655966592445 23255180210522870987472167)
      ·
        refine ⟨34882770315784306481208251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23255180210522870987472167 34882770315784306481208251)
        ·
          refine ⟨52324155473676459721812377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34882770315784306481208251 52324155473676459721812377)
          ·
            refine ⟨39243116605257344791359283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52324155473676459721812377 39243116605257344791359283)
            ·
              refine ⟨58864674907886017187038925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39243116605257344791359283 58864674907886017187038925)
              ·
                refine ⟨22074253090457256445139597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58864674907886017187038925 22074253090457256445139597)
                ·
                  refine ⟨8277844908921471166927349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22074253090457256445139597 8277844908921471166927349)
                  ·
                    refine ⟨776047960211387921899439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8277844908921471166927349 776047960211387921899439)
                    ·
                      rfl

theorem cell23_4534044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_4534044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534044 prefixEnd_4534044 := by exact prefixLift 4534044
  have htrace : WordTrace (prefixWord ++ tailWord_4534044) baseStart_4534044 baseEnd_4534044 := by
    simpa [prefixWord, tailWord_4534044, baseEnd_4534044] using wordTrace_append hprefix tailTrace_4534044
  have hstable : (prefixWord ++ tailWord_4534044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534044).length < 2 ^ (prefixWord ++ tailWord_4534044).sum := by decide
  have hdescent : baseEnd_4534044 < baseStart_4534044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534098 : List Nat := [3, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4]
def baseStart_4534098 : Nat := 118140960795 + 4534098 * 2 ^ 59
def prefixEnd_4534098 : Nat := 4983230072969 + 3 ^ 40 * 4534098 * 2
def baseEnd_4534098 : Nat := 2328171608589506554423069

theorem tailTrace_4534098 : CollatzResearch.WordTrace tailWord_4534098 prefixEnd_4534098 2328171608589506554423069 := by
  unfold tailWord_4534098
  simp only [CollatzResearch.WordTrace]
  refine ⟨41343034981936195783344737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110248093285163188755585965 41343034981936195783344737)
  ·
    refine ⟨31007276236452146837508553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41343034981936195783344737 31007276236452146837508553)
    ·
      refine ⟨23255457177339110128131415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31007276236452146837508553 23255457177339110128131415)
      ·
        refine ⟨34883185766008665192197123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23255457177339110128131415 34883185766008665192197123)
        ·
          refine ⟨52324778649012997788295685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34883185766008665192197123 52324778649012997788295685)
          ·
            refine ⟨9810895996689937085305441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52324778649012997788295685 9810895996689937085305441)
            ·
              refine ⟨7358171997517452813979081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9810895996689937085305441 7358171997517452813979081)
              ·
                refine ⟨5518628998138089610484311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7358171997517452813979081 5518628998138089610484311)
                ·
                  refine ⟨8277943497207134415726467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5518628998138089610484311 8277943497207134415726467)
                  ·
                    refine ⟨12416915245810701623589701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8277943497207134415726467 12416915245810701623589701)
                    ·
                      refine ⟨2328171608589506554423069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12416915245810701623589701 2328171608589506554423069)
                      ·
                        rfl

theorem cell23_4534098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4].length) (baseStart_4534098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534098 prefixEnd_4534098 := by exact prefixLift 4534098
  have htrace : WordTrace (prefixWord ++ tailWord_4534098) baseStart_4534098 baseEnd_4534098 := by
    simpa [prefixWord, tailWord_4534098, baseEnd_4534098] using wordTrace_append hprefix tailTrace_4534098
  have hstable : (prefixWord ++ tailWord_4534098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534098).length < 2 ^ (prefixWord ++ tailWord_4534098).sum := by decide
  have hdescent : baseEnd_4534098 < baseStart_4534098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534141 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 2, 7, 2]
def baseStart_4534141 : Nat := 118140960795 + 4534141 * 2 ^ 59
def prefixEnd_4534141 : Nat := 4983230072969 + 3 ^ 40 * 4534141 * 2
def baseEnd_4534141 : Nat := 2328193688257649886185371

theorem tailTrace_4534141 : CollatzResearch.WordTrace tailWord_4534141 prefixEnd_4534141 2328193688257649886185371 := by
  unfold tailWord_4534141
  simp only [CollatzResearch.WordTrace]
  refine ⟨165373708266589001477194277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110249138844392667651462851 165373708266589001477194277)
  ·
    refine ⟨31007570299985437776973927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165373708266589001477194277 31007570299985437776973927)
    ·
      refine ⟨46511355449978156665460891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31007570299985437776973927 46511355449978156665460891)
      ·
        refine ⟨69767033174967234998191337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46511355449978156665460891 69767033174967234998191337)
        ·
          refine ⟨52325274881225426248643503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69767033174967234998191337 52325274881225426248643503)
          ·
            refine ⟨78487912321838139372965255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52325274881225426248643503 78487912321838139372965255)
            ·
              refine ⟨117731868482757209059447883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78487912321838139372965255 117731868482757209059447883)
              ·
                refine ⟨176597802724135813589171825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117731868482757209059447883 176597802724135813589171825)
                ·
                  refine ⟨132448352043101860191878869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176597802724135813589171825 132448352043101860191878869)
                  ·
                    refine ⟨3104258251010199848247161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 132448352043101860191878869 3104258251010199848247161)
                    ·
                      refine ⟨2328193688257649886185371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3104258251010199848247161 2328193688257649886185371)
                      ·
                        rfl

theorem cell23_4534141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 7, 2].length) (baseStart_4534141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534141 prefixEnd_4534141 := by exact prefixLift 4534141
  have htrace : WordTrace (prefixWord ++ tailWord_4534141) baseStart_4534141 baseEnd_4534141 := by
    simpa [prefixWord, tailWord_4534141, baseEnd_4534141] using wordTrace_append hprefix tailTrace_4534141
  have hstable : (prefixWord ++ tailWord_4534141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534141).length < 2 ^ (prefixWord ++ tailWord_4534141).sum := by decide
  have hdescent : baseEnd_4534141 < baseStart_4534141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534142 : List Nat := [4, 2, 3, 1, 1, 1, 4, 1, 2, 4]
def baseStart_4534142 : Nat := 118140960795 + 4534142 * 2 ^ 59
def prefixEnd_4534142 : Nat := 4983230072969 + 3 ^ 40 * 4534142 * 2
def baseEnd_4534142 : Nat := 776064733912768127424289

theorem tailTrace_4534142 : CollatzResearch.WordTrace tailWord_4534142 prefixEnd_4534142 776064733912768127424289 := by
  unfold tailWord_4534142
  simp only [CollatzResearch.WordTrace]
  refine ⟨20671718092448172330997585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110249163159723585765320453 20671718092448172330997585)
  ·
    refine ⟨15503788569336129248248189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20671718092448172330997585 15503788569336129248248189)
    ·
      refine ⟨5813920713501048468093071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15503788569336129248248189 5813920713501048468093071)
      ·
        refine ⟨8720881070251572702139607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5813920713501048468093071 8720881070251572702139607)
        ·
          refine ⟨13081321605377359053209411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8720881070251572702139607 13081321605377359053209411)
          ·
            refine ⟨19621982408066038579814117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13081321605377359053209411 19621982408066038579814117)
            ·
              refine ⟨3679121701512382233715147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19621982408066038579814117 3679121701512382233715147)
              ·
                refine ⟨5518682552268573350572721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3679121701512382233715147 5518682552268573350572721)
                ·
                  refine ⟨4139011914201430012929541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5518682552268573350572721 4139011914201430012929541)
                  ·
                    refine ⟨776064733912768127424289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4139011914201430012929541 776064733912768127424289)
                    ·
                      rfl

theorem cell23_4534142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_4534142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534142 prefixEnd_4534142 := by exact prefixLift 4534142
  have htrace : WordTrace (prefixWord ++ tailWord_4534142) baseStart_4534142 baseEnd_4534142 := by
    simpa [prefixWord, tailWord_4534142, baseEnd_4534142] using wordTrace_append hprefix tailTrace_4534142
  have hstable : (prefixWord ++ tailWord_4534142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534142).length < 2 ^ (prefixWord ++ tailWord_4534142).sum := by decide
  have hdescent : baseEnd_4534142 < baseStart_4534142 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534152 : List Nat := [2, 1, 3, 3, 4, 1, 1, 2, 1, 2, 3]
def baseStart_4534152 : Nat := 118140960795 + 4534152 * 2 ^ 59
def prefixEnd_4534152 : Nat := 4983230072969 + 3 ^ 40 * 4534152 * 2
def baseEnd_4534152 : Nat := 2328199336544849343147821

theorem tailTrace_4534152 : CollatzResearch.WordTrace tailWord_4534152 prefixEnd_4534152 2328199336544849343147821 := by
  unfold tailWord_4534152
  simp only [CollatzResearch.WordTrace]
  refine ⟨82687054734774575177922355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110249406313032766903896473 82687054734774575177922355)
  ·
    refine ⟨124030582102161862766883533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82687054734774575177922355 124030582102161862766883533)
    ·
      refine ⟨46511468288310698537581325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124030582102161862766883533 46511468288310698537581325)
      ·
        refine ⟨17441800608116511951592997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46511468288310698537581325 17441800608116511951592997)
        ·
          refine ⟨3270337614021845990923687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17441800608116511951592997 3270337614021845990923687)
          ·
            refine ⟨4905506421032768986385531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3270337614021845990923687 4905506421032768986385531)
            ·
              refine ⟨7358259631549153479578297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4905506421032768986385531 7358259631549153479578297)
              ·
                refine ⟨5518694723661865109683723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7358259631549153479578297 5518694723661865109683723)
                ·
                  refine ⟨8278042085492797664525585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5518694723661865109683723 8278042085492797664525585)
                  ·
                    refine ⟨6208531564119598248394189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8278042085492797664525585 6208531564119598248394189)
                    ·
                      refine ⟨2328199336544849343147821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6208531564119598248394189 2328199336544849343147821)
                      ·
                        rfl

theorem cell23_4534152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_4534152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534152 prefixEnd_4534152 := by exact prefixLift 4534152
  have htrace : WordTrace (prefixWord ++ tailWord_4534152) baseStart_4534152 baseEnd_4534152 := by
    simpa [prefixWord, tailWord_4534152, baseEnd_4534152] using wordTrace_append hprefix tailTrace_4534152
  have hstable : (prefixWord ++ tailWord_4534152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534152).length < 2 ^ (prefixWord ++ tailWord_4534152).sum := by decide
  have hdescent : baseEnd_4534152 < baseStart_4534152 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534194 : List Nat := [3, 2, 1, 1, 1, 1, 1, 2, 11]
def baseStart_4534194 : Nat := 118140960795 + 4534194 * 2 ^ 59
def prefixEnd_4534194 : Nat := 4983230072969 + 3 ^ 40 * 4534194 * 2
def baseEnd_4534194 : Nat := 258691211414704242091403

theorem tailTrace_4534194 : CollatzResearch.WordTrace tailWord_4534194 prefixEnd_4534194 258691211414704242091403 := by
  unfold tailWord_4534194
  simp only [CollatzResearch.WordTrace]
  refine ⟨41343910333849247882218409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110250427556931327685915757 41343910333849247882218409)
  ·
    refine ⟨31007932750386935911663807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41343910333849247882218409 31007932750386935911663807)
    ·
      refine ⟨46511899125580403867495711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31007932750386935911663807 46511899125580403867495711)
      ·
        refine ⟨69767848688370605801243567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46511899125580403867495711 69767848688370605801243567)
        ·
          refine ⟨104651773032555908701865351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69767848688370605801243567 104651773032555908701865351)
          ·
            refine ⟨156977659548833863052798027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104651773032555908701865351 156977659548833863052798027)
            ·
              refine ⟨235466489323250794579197041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156977659548833863052798027 235466489323250794579197041)
              ·
                refine ⟨176599866992438095934397781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 235466489323250794579197041 176599866992438095934397781)
                ·
                  refine ⟨258691211414704242091403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 176599866992438095934397781 258691211414704242091403)
                  ·
                    rfl

theorem cell23_4534194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 2, 11].length) (baseStart_4534194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534194 prefixEnd_4534194 := by exact prefixLift 4534194
  have htrace : WordTrace (prefixWord ++ tailWord_4534194) baseStart_4534194 baseEnd_4534194 := by
    simpa [prefixWord, tailWord_4534194, baseEnd_4534194] using wordTrace_append hprefix tailTrace_4534194
  have hstable : (prefixWord ++ tailWord_4534194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534194).length < 2 ^ (prefixWord ++ tailWord_4534194).sum := by decide
  have hdescent : baseEnd_4534194 < baseStart_4534194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534201 : List Nat := [1, 2, 1, 4, 2, 1, 3, 1, 2, 2, 4]
def baseStart_4534201 : Nat := 118140960795 + 4534201 * 2 ^ 59
def prefixEnd_4534201 : Nat := 4983230072969 + 3 ^ 40 * 4534201 * 2
def baseEnd_4534201 : Nat := 2328224497096919651435095

theorem tailTrace_4534201 : CollatzResearch.WordTrace tailWord_4534201 prefixEnd_4534201 2328224497096919651435095 := by
  unfold tailWord_4534201
  simp only [CollatzResearch.WordTrace]
  refine ⟨165375896646371631724378457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110250597764247754482918971 165375896646371631724378457)
  ·
    refine ⟨124031922484778723793283843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165375896646371631724378457 124031922484778723793283843)
    ·
      refine ⟨186047883727168085689925765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124031922484778723793283843 186047883727168085689925765)
      ·
        refine ⟨34883978198844016066861081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186047883727168085689925765 34883978198844016066861081)
        ·
          refine ⟨26162983649133012050145811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34883978198844016066861081 26162983649133012050145811)
          ·
            refine ⟨39244475473699518075218717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26162983649133012050145811 39244475473699518075218717)
            ·
              refine ⟨14716678302637319278207019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39244475473699518075218717 14716678302637319278207019)
              ·
                refine ⟨22075017453955978917310529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14716678302637319278207019 22075017453955978917310529)
                ·
                  refine ⟨16556263090466984187982897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22075017453955978917310529 16556263090466984187982897)
                  ·
                    refine ⟨12417197317850238140987173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16556263090466984187982897 12417197317850238140987173)
                    ·
                      refine ⟨2328224497096919651435095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12417197317850238140987173 2328224497096919651435095)
                      ·
                        rfl

theorem cell23_4534201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_4534201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534201 prefixEnd_4534201 := by exact prefixLift 4534201
  have htrace : WordTrace (prefixWord ++ tailWord_4534201) baseStart_4534201 baseEnd_4534201 := by
    simpa [prefixWord, tailWord_4534201, baseEnd_4534201] using wordTrace_append hprefix tailTrace_4534201
  have hstable : (prefixWord ++ tailWord_4534201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534201).length < 2 ^ (prefixWord ++ tailWord_4534201).sum := by decide
  have hdescent : baseEnd_4534201 < baseStart_4534201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534205 : List Nat := [1, 4, 1, 2, 3, 2, 2, 1, 1, 4, 2]
def baseStart_4534205 : Nat := 118140960795 + 4534205 * 2 ^ 59
def prefixEnd_4534205 : Nat := 4983230072969 + 3 ^ 40 * 4534205 * 2
def baseEnd_4534205 : Nat := 2328226551019537635785077

theorem tailTrace_4534205 : CollatzResearch.WordTrace tailWord_4534205 prefixEnd_4534205 2328226551019537635785077 := by
  unfold tailWord_4534205
  simp only [CollatzResearch.WordTrace]
  refine ⟨165376042538357140407524069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110250695025571426938349379 165376042538357140407524069)
  ·
    refine ⟨31008007975941963826410763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165376042538357140407524069 31008007975941963826410763)
    ·
      refine ⟨46512011963912945739616145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31008007975941963826410763 46512011963912945739616145)
      ·
        refine ⟨34884008972934709304712109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46512011963912945739616145 34884008972934709304712109)
        ·
          refine ⟨13081503364850515989267041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34884008972934709304712109 13081503364850515989267041)
          ·
            refine ⟨9811127523637886991950281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13081503364850515989267041 9811127523637886991950281)
            ·
              refine ⟨7358345642728415243962711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9811127523637886991950281 7358345642728415243962711)
              ·
                refine ⟨11037518464092622865944067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7358345642728415243962711 11037518464092622865944067)
                ·
                  refine ⟨16556277696138934298916101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11037518464092622865944067 16556277696138934298916101)
                  ·
                    refine ⟨3104302068026050181046769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16556277696138934298916101 3104302068026050181046769)
                    ·
                      refine ⟨2328226551019537635785077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3104302068026050181046769 2328226551019537635785077)
                      ·
                        rfl

theorem cell23_4534205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 2, 1, 1, 4, 2].length) (baseStart_4534205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534205 prefixEnd_4534205 := by exact prefixLift 4534205
  have htrace : WordTrace (prefixWord ++ tailWord_4534205) baseStart_4534205 baseEnd_4534205 := by
    simpa [prefixWord, tailWord_4534205, baseEnd_4534205] using wordTrace_append hprefix tailTrace_4534205
  have hstable : (prefixWord ++ tailWord_4534205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534205).length < 2 ^ (prefixWord ++ tailWord_4534205).sum := by decide
  have hdescent : baseEnd_4534205 < baseStart_4534205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534226 : List Nat := [3, 2, 2, 3, 3, 1, 2, 1, 1, 3, 2]
def baseStart_4534226 : Nat := 118140960795 + 4534226 * 2 ^ 59
def prefixEnd_4534226 : Nat := 4983230072969 + 3 ^ 40 * 4534226 * 2
def baseEnd_4534226 : Nat := 2328237334113282053622481

theorem tailTrace_4534226 : CollatzResearch.WordTrace tailWord_4534226 prefixEnd_4534226 2328237334113282053622481 := by
  unfold tailWord_4534226
  simp only [CollatzResearch.WordTrace]
  refine ⟨41344202117820265248509633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110251205647520707329359021 41344202117820265248509633)
  ·
    refine ⟨31008151588365198936382225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41344202117820265248509633 31008151588365198936382225)
    ·
      refine ⟨23256113691273899202286669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31008151588365198936382225 23256113691273899202286669)
      ·
        refine ⟨8721042634227712200857501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23256113691273899202286669 8721042634227712200857501)
        ·
          refine ⟨3270390987835392075321563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8721042634227712200857501 3270390987835392075321563)
          ·
            refine ⟨4905586481753088112982345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3270390987835392075321563 4905586481753088112982345)
            ·
              refine ⟨3679189861314816084736759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4905586481753088112982345 3679189861314816084736759)
              ·
                refine ⟨5518784791972224127105139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3679189861314816084736759 5518784791972224127105139)
                ·
                  refine ⟨8278177187958336190657709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5518784791972224127105139 8278177187958336190657709)
                  ·
                    refine ⟨3104316445484376071496641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8278177187958336190657709 3104316445484376071496641)
                    ·
                      refine ⟨2328237334113282053622481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3104316445484376071496641 2328237334113282053622481)
                      ·
                        rfl

theorem cell23_4534226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_4534226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534226 prefixEnd_4534226 := by exact prefixLift 4534226
  have htrace : WordTrace (prefixWord ++ tailWord_4534226) baseStart_4534226 baseEnd_4534226 := by
    simpa [prefixWord, tailWord_4534226, baseEnd_4534226] using wordTrace_append hprefix tailTrace_4534226
  have hstable : (prefixWord ++ tailWord_4534226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534226).length < 2 ^ (prefixWord ++ tailWord_4534226).sum := by decide
  have hdescent : baseEnd_4534226 < baseStart_4534226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534241 : List Nat := [1, 2, 3, 1, 2, 1, 2, 4, 2, 5]
def baseStart_4534241 : Nat := 118140960795 + 4534241 * 2 ^ 59
def prefixEnd_4534241 : Nat := 4983230072969 + 3 ^ 40 * 4534241 * 2
def baseEnd_4534241 : Nat := 776081678774366498311637

theorem tailTrace_4534241 : CollatzResearch.WordTrace tailWord_4534241 prefixEnd_4534241 776081678774366498311637 := by
  unfold tailWord_4534241
  simp only [CollatzResearch.WordTrace]
  refine ⟨165377355566226718555834577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110251570377484479037223051 165377355566226718555834577)
  ·
    refine ⟨124033016674670038916875933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165377355566226718555834577 124033016674670038916875933)
    ·
      refine ⟨46512381253001264593828475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124033016674670038916875933 46512381253001264593828475)
      ·
        refine ⟨69768571879501896890742713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46512381253001264593828475 69768571879501896890742713)
        ·
          refine ⟨52326428909626422668057035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69768571879501896890742713 52326428909626422668057035)
          ·
            refine ⟨78489643364439634002085553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52326428909626422668057035 78489643364439634002085553)
            ·
              refine ⟨58867232523329725501564165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78489643364439634002085553 58867232523329725501564165)
              ·
                refine ⟨11037606098124323531543281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58867232523329725501564165 11037606098124323531543281)
                ·
                  refine ⟨8278204573593242648657461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11037606098124323531543281 8278204573593242648657461)
                  ·
                    refine ⟨776081678774366498311637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8278204573593242648657461 776081678774366498311637)
                    ·
                      rfl

theorem cell23_4534241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 2, 5].length) (baseStart_4534241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534241 prefixEnd_4534241 := by exact prefixLift 4534241
  have htrace : WordTrace (prefixWord ++ tailWord_4534241) baseStart_4534241 baseEnd_4534241 := by
    simpa [prefixWord, tailWord_4534241, baseEnd_4534241] using wordTrace_append hprefix tailTrace_4534241
  have hstable : (prefixWord ++ tailWord_4534241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534241).length < 2 ^ (prefixWord ++ tailWord_4534241).sum := by decide
  have hdescent : baseEnd_4534241 < baseStart_4534241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534292 : List Nat := [2, 4, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_4534292 : Nat := 118140960795 + 4534292 * 2 ^ 59
def prefixEnd_4534292 : Nat := 4983230072969 + 3 ^ 40 * 4534292 * 2
def baseEnd_4534292 : Nat := 776090407945492931799059

theorem tailTrace_4534292 : CollatzResearch.WordTrace tailWord_4534292 prefixEnd_4534292 776090407945492931799059 := by
  unfold tailWord_4534292
  simp only [CollatzResearch.WordTrace]
  refine ⟨82689607844520977132970565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110252810459361302843960753 82689607844520977132970565)
  ·
    refine ⟨15504301470847683212431981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82689607844520977132970565 15504301470847683212431981)
    ·
      refine ⟨5814113051567881204661993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15504301470847683212431981 5814113051567881204661993)
      ·
        refine ⟨4360584788675910903496495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5814113051567881204661993 4360584788675910903496495)
        ·
          refine ⟨6540877183013866355244743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4360584788675910903496495 6540877183013866355244743)
          ·
            refine ⟨9811315774520799532867115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6540877183013866355244743 9811315774520799532867115)
            ·
              refine ⟨14716973661781199299300673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9811315774520799532867115 14716973661781199299300673)
              ·
                refine ⟨11037730246335899474475505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14716973661781199299300673 11037730246335899474475505)
                ·
                  refine ⟨8278297684751924605856629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11037730246335899474475505 8278297684751924605856629)
                  ·
                    refine ⟨776090407945492931799059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8278297684751924605856629 776090407945492931799059)
                    ·
                      rfl

theorem cell23_4534292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_4534292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534292 prefixEnd_4534292 := by exact prefixLift 4534292
  have htrace : WordTrace (prefixWord ++ tailWord_4534292) baseStart_4534292 baseEnd_4534292 := by
    simpa [prefixWord, tailWord_4534292, baseEnd_4534292] using wordTrace_append hprefix tailTrace_4534292
  have hstable : (prefixWord ++ tailWord_4534292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534292).length < 2 ^ (prefixWord ++ tailWord_4534292).sum := by decide
  have hdescent : baseEnd_4534292 < baseStart_4534292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534295 : List Nat := [1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 4]
def baseStart_4534295 : Nat := 118140960795 + 4534295 * 2 ^ 59
def prefixEnd_4534295 : Nat := 4983230072969 + 3 ^ 40 * 4534295 * 2
def baseEnd_4534295 : Nat := 2328272764278442283659663

theorem tailTrace_4534295 : CollatzResearch.WordTrace tailWord_4534295 prefixEnd_4534295 2328272764278442283659663 := by
  unfold tailWord_4534295
  simp only [CollatzResearch.WordTrace]
  refine ⟨165379325108031085778300339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110252883405354057185533559 165379325108031085778300339)
  ·
    refine ⟨248068987662046628667450509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165379325108031085778300339 248068987662046628667450509)
    ·
      refine ⟨93025870373267485750293941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248068987662046628667450509 93025870373267485750293941)
      ·
        refine ⟨8721175347493826789090057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93025870373267485750293941 8721175347493826789090057)
        ·
          refine ⟨6540881510620370091817543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8721175347493826789090057 6540881510620370091817543)
          ·
            refine ⟨9811322265930555137726315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6540881510620370091817543 9811322265930555137726315)
            ·
              refine ⟨14716983398895832706589473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9811322265930555137726315 14716983398895832706589473)
              ·
                refine ⟨11037737549171874529942105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14716983398895832706589473 11037737549171874529942105)
                ·
                  refine ⟨8278303161878905897456579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11037737549171874529942105 8278303161878905897456579)
                  ·
                    refine ⟨12417454742818358846184869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8278303161878905897456579 12417454742818358846184869)
                    ·
                      refine ⟨2328272764278442283659663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12417454742818358846184869 2328272764278442283659663)
                      ·
                        rfl

theorem cell23_4534295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_4534295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534295 prefixEnd_4534295 := by exact prefixLift 4534295
  have htrace : WordTrace (prefixWord ++ tailWord_4534295) baseStart_4534295 baseEnd_4534295 := by
    simpa [prefixWord, tailWord_4534295, baseEnd_4534295] using wordTrace_append hprefix tailTrace_4534295
  have hstable : (prefixWord ++ tailWord_4534295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534295).length < 2 ^ (prefixWord ++ tailWord_4534295).sum := by decide
  have hdescent : baseEnd_4534295 < baseStart_4534295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534298 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3]
def baseStart_4534298 : Nat := 118140960795 + 4534298 * 2 ^ 59
def prefixEnd_4534298 : Nat := 4983230072969 + 3 ^ 40 * 4534298 * 2
def baseEnd_4534298 : Nat := 2328274304720405771922149

theorem tailTrace_4534298 : CollatzResearch.WordTrace tailWord_4534298 prefixEnd_4534298 2328274304720405771922149 := by
  unfold tailWord_4534298
  simp only [CollatzResearch.WordTrace]
  refine ⟨41344858631755054322664887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110252956351346811527106365 41344858631755054322664887)
  ·
    refine ⟨62017287947632581483997331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41344858631755054322664887 62017287947632581483997331)
    ·
      refine ⟨93025931921448872225995997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62017287947632581483997331 93025931921448872225995997)
      ·
        refine ⟨34884724470543327084748499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93025931921448872225995997 34884724470543327084748499)
        ·
          refine ⟨52327086705814990627122749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34884724470543327084748499 52327086705814990627122749)
          ·
            refine ⟨19622657514680621485171031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52327086705814990627122749 19622657514680621485171031)
            ·
              refine ⟨29433986272020932227756547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19622657514680621485171031 29433986272020932227756547)
              ·
                refine ⟨44150979408031398341634821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29433986272020932227756547 44150979408031398341634821)
                ·
                  refine ⟨8278308639005887189056529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44150979408031398341634821 8278308639005887189056529)
                  ·
                    refine ⟨6208731479254415391792397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8278308639005887189056529 6208731479254415391792397)
                    ·
                      refine ⟨2328274304720405771922149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6208731479254415391792397 2328274304720405771922149)
                      ·
                        rfl

theorem cell23_4534298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_4534298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534298 prefixEnd_4534298 := by exact prefixLift 4534298
  have htrace : WordTrace (prefixWord ++ tailWord_4534298) baseStart_4534298 baseEnd_4534298 := by
    simpa [prefixWord, tailWord_4534298, baseEnd_4534298] using wordTrace_append hprefix tailTrace_4534298
  have hstable : (prefixWord ++ tailWord_4534298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534298).length < 2 ^ (prefixWord ++ tailWord_4534298).sum := by decide
  have hdescent : baseEnd_4534298 < baseStart_4534298 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534331 : List Nat := [1, 1, 1, 1, 1, 2, 1, 7, 3, 5]
def baseStart_4534331 : Nat := 118140960795 + 4534331 * 2 ^ 59
def prefixEnd_4534331 : Nat := 4983230072969 + 3 ^ 40 * 4534331 * 2
def baseEnd_4534331 : Nat := 776097083194001380936499

theorem tailTrace_4534331 : CollatzResearch.WordTrace tailWord_4534331 prefixEnd_4534331 776097083194001380936499 := by
  unfold tailWord_4534331
  simp only [CollatzResearch.WordTrace]
  refine ⟨165380638135900663926610847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110253758757267109284407231 165380638135900663926610847)
  ·
    refine ⟨248070957203850995889916271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165380638135900663926610847 248070957203850995889916271)
    ·
      refine ⟨372106435805776493834874407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248070957203850995889916271 372106435805776493834874407)
      ·
        refine ⟨558159653708664740752311611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372106435805776493834874407 558159653708664740752311611)
        ·
          refine ⟨837239480562997111128467417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558159653708664740752311611 837239480562997111128467417)
          ·
            refine ⟨627929610422247833346350563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 837239480562997111128467417 627929610422247833346350563)
            ·
              refine ⟨941894415633371750019525845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 627929610422247833346350563 941894415633371750019525845)
              ·
                refine ⟨22075650366407150391082637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 941894415633371750019525845 22075650366407150391082637)
                ·
                  refine ⟨8278368887402681396655989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22075650366407150391082637 8278368887402681396655989)
                  ·
                    refine ⟨776097083194001380936499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8278368887402681396655989 776097083194001380936499)
                    ·
                      rfl

theorem cell23_4534331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 3, 5].length) (baseStart_4534331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534331 prefixEnd_4534331 := by exact prefixLift 4534331
  have htrace : WordTrace (prefixWord ++ tailWord_4534331) baseStart_4534331 baseEnd_4534331 := by
    simpa [prefixWord, tailWord_4534331, baseEnd_4534331] using wordTrace_append hprefix tailTrace_4534331
  have hstable : (prefixWord ++ tailWord_4534331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534331).length < 2 ^ (prefixWord ++ tailWord_4534331).sum := by decide
  have hdescent : baseEnd_4534331 < baseStart_4534331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534348 : List Nat := [2, 2, 1, 3, 1, 1, 2, 5, 1, 5]
def baseStart_4534348 : Nat := 118140960795 + 4534348 * 2 ^ 59
def prefixEnd_4534348 : Nat := 4983230072969 + 3 ^ 40 * 4534348 * 2
def baseEnd_4534348 : Nat := 776099992917710192098973

theorem tailTrace_4534348 : CollatzResearch.WordTrace tailWord_4534348 prefixEnd_4534348 776099992917710192098973 := by
  unfold tailWord_4534348
  simp only [CollatzResearch.WordTrace]
  refine ⟨82690629088419537914989849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110254172117892717219986465 82690629088419537914989849)
  ·
    refine ⟨62017971816314653436242387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82690629088419537914989849 62017971816314653436242387)
    ·
      refine ⟨93026957724471980154363581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62017971816314653436242387 93026957724471980154363581)
      ·
        refine ⟨34885109146676992557886343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93026957724471980154363581 34885109146676992557886343)
        ·
          refine ⟨52327663720015488836829515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34885109146676992557886343 52327663720015488836829515)
          ·
            refine ⟨78491495580023233255244273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52327663720015488836829515 78491495580023233255244273)
            ·
              refine ⟨58868621685017424941433205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78491495580023233255244273 58868621685017424941433205)
              ·
                refine ⟨5518933282970383588259363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58868621685017424941433205 5518933282970383588259363)
                ·
                  refine ⟨8278399924455575382389045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5518933282970383588259363 8278399924455575382389045)
                  ·
                    refine ⟨776099992917710192098973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8278399924455575382389045 776099992917710192098973)
                    ·
                      rfl

theorem cell23_4534348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 5, 1, 5].length) (baseStart_4534348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534348 prefixEnd_4534348 := by exact prefixLift 4534348
  have htrace : WordTrace (prefixWord ++ tailWord_4534348) baseStart_4534348 baseEnd_4534348 := by
    simpa [prefixWord, tailWord_4534348, baseEnd_4534348] using wordTrace_append hprefix tailTrace_4534348
  have hstable : (prefixWord ++ tailWord_4534348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534348).length < 2 ^ (prefixWord ++ tailWord_4534348).sum := by decide
  have hdescent : baseEnd_4534348 < baseStart_4534348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534361 : List Nat := [1, 2, 1, 2, 2, 1, 3, 2, 3, 6]
def baseStart_4534361 : Nat := 118140960795 + 4534361 * 2 ^ 59
def prefixEnd_4534361 : Nat := 4983230072969 + 3 ^ 40 * 4534361 * 2
def baseEnd_4534361 : Nat := 776102218000546341811453

theorem tailTrace_4534361 : CollatzResearch.WordTrace tailWord_4534361 prefixEnd_4534361 776102218000546341811453 := by
  unfold tailWord_4534361
  simp only [CollatzResearch.WordTrace]
  refine ⟨165381732325791979050202937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110254488217194652700135291 165381732325791979050202937)
  ·
    refine ⟨124036299244343984287652203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165381732325791979050202937 124036299244343984287652203)
    ·
      refine ⟨186054448866515976431478305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124036299244343984287652203 186054448866515976431478305)
      ·
        refine ⟨139540836649886982323608729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186054448866515976431478305 139540836649886982323608729)
        ·
          refine ⟨104655627487415236742706547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139540836649886982323608729 104655627487415236742706547)
          ·
            refine ⟨156983441231122855114059821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104655627487415236742706547 156983441231122855114059821)
            ·
              refine ⟨58868790461671070667772433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156983441231122855114059821 58868790461671070667772433)
              ·
                refine ⟨44151592846253303000829325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58868790461671070667772433 44151592846253303000829325)
                ·
                  refine ⟨16556847317344988625310997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44151592846253303000829325 16556847317344988625310997)
                  ·
                    refine ⟨776102218000546341811453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16556847317344988625310997 776102218000546341811453)
                    ·
                      rfl

theorem cell23_4534361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 3, 6].length) (baseStart_4534361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534361 prefixEnd_4534361 := by exact prefixLift 4534361
  have htrace : WordTrace (prefixWord ++ tailWord_4534361) baseStart_4534361 baseEnd_4534361 := by
    simpa [prefixWord, tailWord_4534361, baseEnd_4534361] using wordTrace_append hprefix tailTrace_4534361
  have hstable : (prefixWord ++ tailWord_4534361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534361).length < 2 ^ (prefixWord ++ tailWord_4534361).sum := by decide
  have hdescent : baseEnd_4534361 < baseStart_4534361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534362 : List Nat := [3, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3]
def baseStart_4534362 : Nat := 118140960795 + 4534362 * 2 ^ 59
def prefixEnd_4534362 : Nat := 4983230072969 + 3 ^ 40 * 4534362 * 2
def baseEnd_4534362 : Nat := 2328307167482293521521855

theorem tailTrace_4534362 : CollatzResearch.WordTrace tailWord_4534362 prefixEnd_4534362 2328307167482293521521855 := by
  unfold tailWord_4534362
  simp only [CollatzResearch.WordTrace]
  refine ⟨41345442199697089055247335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110254512532525570813992893 41345442199697089055247335)
  ·
    refine ⟨62018163299545633582871003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41345442199697089055247335 62018163299545633582871003)
    ·
      refine ⟨93027244949318450374306505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62018163299545633582871003 93027244949318450374306505)
      ·
        refine ⟨69770433711988837780729879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93027244949318450374306505 69770433711988837780729879)
        ·
          refine ⟨104655650567983256671094819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69770433711988837780729879 104655650567983256671094819)
          ·
            refine ⟨156983475851974885006642229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104655650567983256671094819 156983475851974885006642229)
            ·
              refine ⟨14717200861122645469372709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 156983475851974885006642229 14717200861122645469372709)
              ·
                refine ⟨2759475161460496025507383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14717200861122645469372709 2759475161460496025507383)
                ·
                  refine ⟨4139212742190744038261075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759475161460496025507383 4139212742190744038261075)
                  ·
                    refine ⟨6208819113286116057391613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4139212742190744038261075 6208819113286116057391613)
                    ·
                      refine ⟨2328307167482293521521855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6208819113286116057391613 2328307167482293521521855)
                      ·
                        rfl

theorem cell23_4534362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_4534362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534362 prefixEnd_4534362 := by exact prefixLift 4534362
  have htrace : WordTrace (prefixWord ++ tailWord_4534362) baseStart_4534362 baseEnd_4534362 := by
    simpa [prefixWord, tailWord_4534362, baseEnd_4534362] using wordTrace_append hprefix tailTrace_4534362
  have hstable : (prefixWord ++ tailWord_4534362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534362).length < 2 ^ (prefixWord ++ tailWord_4534362).sum := by decide
  have hdescent : baseEnd_4534362 < baseStart_4534362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534365 : List Nat := [1, 4, 4, 1, 1, 1, 1, 2, 3, 5]
def baseStart_4534365 : Nat := 118140960795 + 4534365 * 2 ^ 59
def prefixEnd_4534365 : Nat := 4983230072969 + 3 ^ 40 * 4534365 * 2
def baseEnd_4534365 : Nat := 776102902641419003261447

theorem tailTrace_4534365 : CollatzResearch.WordTrace tailWord_4534365 prefixEnd_4534365 776102902641419003261447 := by
  unfold tailWord_4534365
  simp only [CollatzResearch.WordTrace]
  refine ⟨165381878217777487733348549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110254585478518325155565699 165381878217777487733348549)
  ·
    refine ⟨31009102165833278950002853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165381878217777487733348549 31009102165833278950002853)
    ·
      refine ⟨5814206656093739803125535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31009102165833278950002853 5814206656093739803125535)
      ·
        refine ⟨8721309984140609704688303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5814206656093739803125535 8721309984140609704688303)
        ·
          refine ⟨13081964976210914557032455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8721309984140609704688303 13081964976210914557032455)
          ·
            refine ⟨19622947464316371835548683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13081964976210914557032455 19622947464316371835548683)
            ·
              refine ⟨29434421196474557753323025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19622947464316371835548683 29434421196474557753323025)
              ·
                refine ⟨22075815897355918314992269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29434421196474557753323025 22075815897355918314992269)
                ·
                  refine ⟨8278430961508469368122101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22075815897355918314992269 8278430961508469368122101)
                  ·
                    refine ⟨776102902641419003261447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8278430961508469368122101 776102902641419003261447)
                    ·
                      rfl

theorem cell23_4534365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_4534365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534365 prefixEnd_4534365 := by exact prefixLift 4534365
  have htrace : WordTrace (prefixWord ++ tailWord_4534365) baseStart_4534365 baseEnd_4534365 := by
    simpa [prefixWord, tailWord_4534365, baseEnd_4534365] using wordTrace_append hprefix tailTrace_4534365
  have hstable : (prefixWord ++ tailWord_4534365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534365).length < 2 ^ (prefixWord ++ tailWord_4534365).sum := by decide
  have hdescent : baseEnd_4534365 < baseStart_4534365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534368 : List Nat := [2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 4]
def baseStart_4534368 : Nat := 118140960795 + 4534368 * 2 ^ 59
def prefixEnd_4534368 : Nat := 4983230072969 + 3 ^ 40 * 4534368 * 2
def baseEnd_4534368 : Nat := 2328310248366220498046827

theorem tailTrace_4534368 : CollatzResearch.WordTrace tailWord_4534368 prefixEnd_4534368 2328310248366220498046827 := by
  unfold tailWord_4534368
  simp only [CollatzResearch.WordTrace]
  refine ⟨82690993818383309622853879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110254658424511079497138505 82690993818383309622853879)
  ·
    refine ⟨124036490727574964434280819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82690993818383309622853879 124036490727574964434280819)
    ·
      refine ⟨186054736091362446651421229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124036490727574964434280819 186054736091362446651421229)
      ·
        refine ⟨69770526034260917494282961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186054736091362446651421229 69770526034260917494282961)
        ·
          refine ⟨52327894525695688120712221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69770526034260917494282961 52327894525695688120712221)
          ·
            refine ⟨19622960447135883045267083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52327894525695688120712221 19622960447135883045267083)
            ·
              refine ⟨29434440670703824567900625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19622960447135883045267083 29434440670703824567900625)
              ·
                refine ⟨22075830503027868425925469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29434440670703824567900625 22075830503027868425925469)
                ·
                  refine ⟨8278436438635450659722051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22075830503027868425925469 8278436438635450659722051)
                  ·
                    refine ⟨12417654657953175989583077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8278436438635450659722051 12417654657953175989583077)
                    ·
                      refine ⟨2328310248366220498046827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12417654657953175989583077 2328310248366220498046827)
                      ·
                        rfl

theorem cell23_4534368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_4534368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534368 prefixEnd_4534368 := by exact prefixLift 4534368
  have htrace : WordTrace (prefixWord ++ tailWord_4534368) baseStart_4534368 baseEnd_4534368 := by
    simpa [prefixWord, tailWord_4534368, baseEnd_4534368] using wordTrace_append hprefix tailTrace_4534368
  have hstable : (prefixWord ++ tailWord_4534368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534368).length < 2 ^ (prefixWord ++ tailWord_4534368).sum := by decide
  have hdescent : baseEnd_4534368 < baseStart_4534368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534408 : List Nat := [2, 1, 3, 4, 1, 2, 10]
def baseStart_4534408 : Nat := 118140960795 + 4534408 * 2 ^ 59
def prefixEnd_4534408 : Nat := 4983230072969 + 3 ^ 40 * 4534408 * 2
def baseEnd_4534408 : Nat := 28744824538177781994403

theorem tailTrace_4534408 : CollatzResearch.WordTrace tailWord_4534408 prefixEnd_4534408 28744824538177781994403 := by
  unfold tailWord_4534408
  simp only [CollatzResearch.WordTrace]
  refine ⟨82691723278310853038581939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110255631037747804051442585 82691723278310853038581939)
  ·
    refine ⟨124037584917466279557872909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82691723278310853038581939 124037584917466279557872909)
    ·
      refine ⟨46514094344049854834202341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124037584917466279557872909 46514094344049854834202341)
      ·
        refine ⟨8721392689509347781412939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46514094344049854834202341 8721392689509347781412939)
        ·
          refine ⟨13082089034264021672119409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8721392689509347781412939 13082089034264021672119409)
          ·
            refine ⟨9811566775698016254089557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13082089034264021672119409 9811566775698016254089557)
            ·
              refine ⟨28744824538177781994403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9811566775698016254089557 28744824538177781994403)
              ·
                rfl

theorem cell23_4534408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 10].length) (baseStart_4534408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534408 prefixEnd_4534408 := by exact prefixLift 4534408
  have htrace : WordTrace (prefixWord ++ tailWord_4534408) baseStart_4534408 baseEnd_4534408 := by
    simpa [prefixWord, tailWord_4534408, baseEnd_4534408] using wordTrace_append hprefix tailTrace_4534408
  have hstable : (prefixWord ++ tailWord_4534408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534408).length < 2 ^ (prefixWord ++ tailWord_4534408).sum := by decide
  have hdescent : baseEnd_4534408 < baseStart_4534408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534411 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 6]
def baseStart_4534411 : Nat := 118140960795 + 4534411 * 2 ^ 59
def prefixEnd_4534411 : Nat := 4983230072969 + 3 ^ 40 * 4534411 * 2
def baseEnd_4534411 : Nat := 2328332328034363829809129

theorem tailTrace_4534411 : CollatzResearch.WordTrace tailWord_4534411 prefixEnd_4534411 2328332328034363829809129 := by
  unfold tailWord_4534411
  simp only [CollatzResearch.WordTrace]
  refine ⟨165383555975610837589523087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110255703983740558393015391 165383555975610837589523087)
  ·
    refine ⟨248075333963416256384284631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165383555975610837589523087 248075333963416256384284631)
    ·
      refine ⟨372113000945124384576426947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248075333963416256384284631 372113000945124384576426947)
      ·
        refine ⟨558169501417686576864640421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372113000945124384576426947 558169501417686576864640421)
        ·
          refine ⟨104656781515816233162120079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 558169501417686576864640421 104656781515816233162120079)
          ·
            refine ⟨156985172273724349743180119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104656781515816233162120079 156985172273724349743180119)
            ·
              refine ⟨235477758410586524614770179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156985172273724349743180119 235477758410586524614770179)
              ·
                refine ⟨353216637615879786922155269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235477758410586524614770179 353216637615879786922155269)
                ·
                  refine ⟨66228119552977460047904113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 353216637615879786922155269 66228119552977460047904113)
                  ·
                    refine ⟨49671089664733095035928085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66228119552977460047904113 49671089664733095035928085)
                    ·
                      refine ⟨2328332328034363829809129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49671089664733095035928085 2328332328034363829809129)
                      ·
                        rfl

theorem cell23_4534411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 4, 2, 6].length) (baseStart_4534411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534411 prefixEnd_4534411 := by exact prefixLift 4534411
  have htrace : WordTrace (prefixWord ++ tailWord_4534411) baseStart_4534411 baseEnd_4534411 := by
    simpa [prefixWord, tailWord_4534411, baseEnd_4534411] using wordTrace_append hprefix tailTrace_4534411
  have hstable : (prefixWord ++ tailWord_4534411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534411).length < 2 ^ (prefixWord ++ tailWord_4534411).sum := by decide
  have hdescent : baseEnd_4534411 < baseStart_4534411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534439 : List Nat := [1, 1, 6, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_4534439 : Nat := 118140960795 + 4534439 * 2 ^ 59
def prefixEnd_4534439 : Nat := 4983230072969 + 3 ^ 40 * 4534439 * 2
def baseEnd_4534439 : Nat := 2328346705492689720259001

theorem tailTrace_4534439 : CollatzResearch.WordTrace tailWord_4534439 prefixEnd_4534439 2328346705492689720259001 := by
  unfold tailWord_4534439
  simp only [CollatzResearch.WordTrace]
  refine ⟨165384577219509398371542371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110256384813006265581028247 165384577219509398371542371)
  ·
    refine ⟨248076865829264097557313557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165384577219509398371542371 248076865829264097557313557)
    ·
      refine ⟨11628603085746754572999073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 248076865829264097557313557 11628603085746754572999073)
      ·
        refine ⟨8721452314310065929749305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11628603085746754572999073 8721452314310065929749305)
        ·
          refine ⟨6541089235732549447311979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8721452314310065929749305 6541089235732549447311979)
          ·
            refine ⟨9811633853598824170967969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6541089235732549447311979 9811633853598824170967969)
            ·
              refine ⟨7358725390199118128225977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9811633853598824170967969 7358725390199118128225977)
              ·
                refine ⟨5519044042649338596169483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7358725390199118128225977 5519044042649338596169483)
                ·
                  refine ⟨8278566063974007894254225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5519044042649338596169483 8278566063974007894254225)
                  ·
                    refine ⟨6208924547980505920690669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8278566063974007894254225 6208924547980505920690669)
                    ·
                      refine ⟨2328346705492689720259001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6208924547980505920690669 2328346705492689720259001)
                      ·
                        rfl

theorem cell23_4534439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_4534439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534439 prefixEnd_4534439 := by exact prefixLift 4534439
  have htrace : WordTrace (prefixWord ++ tailWord_4534439) baseStart_4534439 baseEnd_4534439 := by
    simpa [prefixWord, tailWord_4534439, baseEnd_4534439] using wordTrace_append hprefix tailTrace_4534439
  have hstable : (prefixWord ++ tailWord_4534439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534439).length < 2 ^ (prefixWord ++ tailWord_4534439).sum := by decide
  have hdescent : baseEnd_4534439 < baseStart_4534439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534486 : List Nat := [5, 2, 1, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_4534486 : Nat := 118140960795 + 4534486 * 2 ^ 59
def prefixEnd_4534486 : Nat := 4983230072969 + 3 ^ 40 * 4534486 * 2
def baseEnd_4534486 : Nat := 2328370839083451036371285

theorem tailTrace_4534486 : CollatzResearch.WordTrace tailWord_4534486 prefixEnd_4534486 2328370839083451036371285 := by
  unfold tailWord_4534486
  simp only [CollatzResearch.WordTrace]
  refine ⟨10336643215646195337406457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110257527633559416932335541 10336643215646195337406457)
  ·
    refine ⟨7752482411734646503054843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10336643215646195337406457 7752482411734646503054843)
    ·
      refine ⟨11628723617601969754582265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7752482411734646503054843 11628723617601969754582265)
      ·
        refine ⟨8721542713201477315936699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11628723617601969754582265 8721542713201477315936699)
        ·
          refine ⟨13082314069802215973905049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8721542713201477315936699 13082314069802215973905049)
          ·
            refine ⟨9811735552351661980428787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13082314069802215973905049 9811735552351661980428787)
            ·
              refine ⟨14717603328527492970643181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9811735552351661980428787 14717603328527492970643181)
              ·
                refine ⟨5519101248197809863991193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14717603328527492970643181 5519101248197809863991193)
                ·
                  refine ⟨4139325936148357397993395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5519101248197809863991193 4139325936148357397993395)
                  ·
                    refine ⟨6208988904222536096990093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4139325936148357397993395 6208988904222536096990093)
                    ·
                      refine ⟨2328370839083451036371285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6208988904222536096990093 2328370839083451036371285)
                      ·
                        rfl

theorem cell23_4534486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_4534486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534486 prefixEnd_4534486 := by exact prefixLift 4534486
  have htrace : WordTrace (prefixWord ++ tailWord_4534486) baseStart_4534486 baseEnd_4534486 := by
    simpa [prefixWord, tailWord_4534486, baseEnd_4534486] using wordTrace_append hprefix tailTrace_4534486
  have hstable : (prefixWord ++ tailWord_4534486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534486).length < 2 ^ (prefixWord ++ tailWord_4534486).sum := by decide
  have hdescent : baseEnd_4534486 < baseStart_4534486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534509 : List Nat := [1, 5, 1, 2, 3, 1, 1, 2, 1, 4, 2]
def baseStart_4534509 : Nat := 118140960795 + 4534509 * 2 ^ 59
def prefixEnd_4534509 : Nat := 4983230072969 + 3 ^ 40 * 4534509 * 2
def baseEnd_4534509 : Nat := 2328382649138504446383679

theorem tailTrace_4534509 : CollatzResearch.WordTrace tailWord_4534509 prefixEnd_4534509 2328382649138504446383679 := by
  unfold tailWord_4534509
  simp only [CollatzResearch.WordTrace]
  refine ⟨165387130329255800326590581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110258086886170533551060387 165387130329255800326590581)
  ·
    refine ⟨15505043468367731280617867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165387130329255800326590581 15505043468367731280617867)
    ·
      refine ⟨23257565202551596920926801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15505043468367731280617867 23257565202551596920926801)
      ·
        refine ⟨17443173901913697690695101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23257565202551596920926801 17443173901913697690695101)
        ·
          refine ⟨6541190213217636634010663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17443173901913697690695101 6541190213217636634010663)
          ·
            refine ⟨9811785319826454951015995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6541190213217636634010663 9811785319826454951015995)
            ·
              refine ⟨14717677979739682426523993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9811785319826454951015995 14717677979739682426523993)
              ·
                refine ⟨11038258484804761819892995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14717677979739682426523993 11038258484804761819892995)
                ·
                  refine ⟨16557387727207142729839493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11038258484804761819892995 16557387727207142729839493)
                  ·
                    refine ⟨3104510198851339261844905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16557387727207142729839493 3104510198851339261844905)
                    ·
                      refine ⟨2328382649138504446383679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3104510198851339261844905 2328382649138504446383679)
                      ·
                        rfl

theorem cell23_4534509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_4534509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534509 prefixEnd_4534509 := by exact prefixLift 4534509
  have htrace : WordTrace (prefixWord ++ tailWord_4534509) baseStart_4534509 baseEnd_4534509 := by
    simpa [prefixWord, tailWord_4534509, baseEnd_4534509] using wordTrace_append hprefix tailTrace_4534509
  have hstable : (prefixWord ++ tailWord_4534509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534509).length < 2 ^ (prefixWord ++ tailWord_4534509).sum := by decide
  have hdescent : baseEnd_4534509 < baseStart_4534509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534515 : List Nat := [1, 1, 1, 2, 2, 4, 2, 5, 5]
def baseStart_4534515 : Nat := 118140960795 + 4534515 * 2 ^ 59
def prefixEnd_4534515 : Nat := 4983230072969 + 3 ^ 40 * 4534515 * 2
def baseEnd_4534515 : Nat := 258709525558047935878739

theorem tailTrace_4534515 : CollatzResearch.WordTrace tailWord_4534515 prefixEnd_4534515 258709525558047935878739 := by
  unfold tailWord_4534515
  simp only [CollatzResearch.WordTrace]
  refine ⟨165387349167234063351308999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110258232778156042234205999 165387349167234063351308999)
  ·
    refine ⟨248081023750851095026963499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165387349167234063351308999 248081023750851095026963499)
    ·
      refine ⟨372121535626276642540445249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248081023750851095026963499 372121535626276642540445249)
      ·
        refine ⟨279091151719707481905333937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372121535626276642540445249 279091151719707481905333937)
        ·
          refine ⟨209318363789780611429000453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279091151719707481905333937 209318363789780611429000453)
          ·
            refine ⟨39247193210583864642937585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 209318363789780611429000453 39247193210583864642937585)
            ·
              refine ⟨29435394907937898482203189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39247193210583864642937585 29435394907937898482203189)
              ·
                refine ⟨2759568272619177982706549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29435394907937898482203189 2759568272619177982706549)
                ·
                  refine ⟨258709525558047935878739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2759568272619177982706549 258709525558047935878739)
                  ·
                    rfl

theorem cell23_4534515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5, 5].length) (baseStart_4534515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534515 prefixEnd_4534515 := by exact prefixLift 4534515
  have htrace : WordTrace (prefixWord ++ tailWord_4534515) baseStart_4534515 baseEnd_4534515 := by
    simpa [prefixWord, tailWord_4534515, baseEnd_4534515] using wordTrace_append hprefix tailTrace_4534515
  have hstable : (prefixWord ++ tailWord_4534515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534515).length < 2 ^ (prefixWord ++ tailWord_4534515).sum := by decide
  have hdescent : baseEnd_4534515 < baseStart_4534515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534526 : List Nat := [4, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_4534526 : Nat := 118140960795 + 4534526 * 2 ^ 59
def prefixEnd_4534526 : Nat := 4983230072969 + 3 ^ 40 * 4534526 * 2
def baseEnd_4534526 : Nat := 2328391378309630879871101

theorem tailTrace_4534526 : CollatzResearch.WordTrace tailWord_4534526 prefixEnd_4534526 2328391378309630879871101 := by
  unfold tailWord_4534526
  simp only [CollatzResearch.WordTrace]
  refine ⟨20673468796274276528744929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110258500246796141486639621 20673468796274276528744929)
  ·
    refine ⟨15505101597205707396558697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20673468796274276528744929 15505101597205707396558697)
    ·
      refine ⟨11628826197904280547419023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15505101597205707396558697 11628826197904280547419023)
      ·
        refine ⟨17443239296856420821128535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11628826197904280547419023 17443239296856420821128535)
        ·
          refine ⟨26164858945284631231692803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17443239296856420821128535 26164858945284631231692803)
          ·
            refine ⟨39247288417926946847539205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26164858945284631231692803 39247288417926946847539205)
            ·
              refine ⟨7358866578361302533913601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39247288417926946847539205 7358866578361302533913601)
              ·
                refine ⟨5519149933770976900435201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7358866578361302533913601 5519149933770976900435201)
                ·
                  refine ⟨4139362450328232675326401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5519149933770976900435201 4139362450328232675326401)
                  ·
                    refine ⟨3104521837746174506494801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4139362450328232675326401 3104521837746174506494801)
                    ·
                      refine ⟨2328391378309630879871101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3104521837746174506494801 2328391378309630879871101)
                      ·
                        rfl

theorem cell23_4534526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_4534526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534526 prefixEnd_4534526 := by exact prefixLift 4534526
  have htrace : WordTrace (prefixWord ++ tailWord_4534526) baseStart_4534526 baseEnd_4534526 := by
    simpa [prefixWord, tailWord_4534526, baseEnd_4534526] using wordTrace_append hprefix tailTrace_4534526
  have hstable : (prefixWord ++ tailWord_4534526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534526).length < 2 ^ (prefixWord ++ tailWord_4534526).sum := by decide
  have hdescent : baseEnd_4534526 < baseStart_4534526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534562 : List Nat := [3, 3, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_4534562 : Nat := 118140960795 + 4534562 * 2 ^ 59
def prefixEnd_4534562 : Nat := 4983230072969 + 3 ^ 40 * 4534562 * 2
def baseEnd_4534562 : Nat := 776136621204397579673645

theorem tailTrace_4534562 : CollatzResearch.WordTrace tailWord_4534562 prefixEnd_4534562 776136621204397579673645 := by
  unfold tailWord_4534562
  simp only [CollatzResearch.WordTrace]
  refine ⟨41347265849515947594567485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110259375598709193585513293 41347265849515947594567485)
  ·
    refine ⟨15505224693568480347962807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41347265849515947594567485 15505224693568480347962807)
    ·
      refine ⟨23257837040352720521944211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15505224693568480347962807 23257837040352720521944211)
      ·
        refine ⟨34886755560529080782916317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23257837040352720521944211 34886755560529080782916317)
        ·
          refine ⟨13082533335198405293593619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34886755560529080782916317 13082533335198405293593619)
          ·
            refine ⟨19623800002797607940390429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13082533335198405293593619 19623800002797607940390429)
            ·
              refine ⟨7358925001049102977646411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19623800002797607940390429 7358925001049102977646411)
              ·
                refine ⟨11038387501573654466469617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7358925001049102977646411 11038387501573654466469617)
                ·
                  refine ⟨8278790626180240849852213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11038387501573654466469617 8278790626180240849852213)
                  ·
                    refine ⟨776136621204397579673645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8278790626180240849852213 776136621204397579673645)
                    ·
                      rfl

theorem cell23_4534562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_4534562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534562 prefixEnd_4534562 := by exact prefixLift 4534562
  have htrace : WordTrace (prefixWord ++ tailWord_4534562) baseStart_4534562 baseEnd_4534562 := by
    simpa [prefixWord, tailWord_4534562, baseEnd_4534562] using wordTrace_append hprefix tailTrace_4534562
  have hstable : (prefixWord ++ tailWord_4534562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534562).length < 2 ^ (prefixWord ++ tailWord_4534562).sum := by decide
  have hdescent : baseEnd_4534562 < baseStart_4534562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534615 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 3]
def baseStart_4534615 : Nat := 118140960795 + 4534615 * 2 ^ 59
def prefixEnd_4534615 : Nat := 4983230072969 + 3 ^ 40 * 4534615 * 2
def baseEnd_4534615 : Nat := 2328437078087881031658191

theorem tailTrace_4534615 : CollatzResearch.WordTrace tailWord_4534615 prefixEnd_4534615 2328437078087881031658191 := by
  unfold tailWord_4534615
  simp only [CollatzResearch.WordTrace]
  refine ⟨165390996466871780429949299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110260664311247853619966199 165390996466871780429949299)
  ·
    refine ⟨248086494700307670644923949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165390996466871780429949299 248086494700307670644923949)
    ·
      refine ⟨93032435512615376491846481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248086494700307670644923949 93032435512615376491846481)
      ·
        refine ⟨69774326634461532368884861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93032435512615376491846481 69774326634461532368884861)
        ·
          refine ⟨26165372487923074638331823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69774326634461532368884861 26165372487923074638331823)
          ·
            refine ⟨39248058731884611957497735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26165372487923074638331823 39248058731884611957497735)
            ·
              refine ⟨58872088097826917936246603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39248058731884611957497735 58872088097826917936246603)
              ·
                refine ⟨88308132146740376904369905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58872088097826917936246603 88308132146740376904369905)
                ·
                  refine ⟨66231099110055282678277429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88308132146740376904369905 66231099110055282678277429)
                  ·
                    refine ⟨6209165541567682751088509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66231099110055282678277429 6209165541567682751088509)
                    ·
                      refine ⟨2328437078087881031658191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6209165541567682751088509 2328437078087881031658191)
                      ·
                        rfl

theorem cell23_4534615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_4534615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534615 prefixEnd_4534615 := by exact prefixLift 4534615
  have htrace : WordTrace (prefixWord ++ tailWord_4534615) baseStart_4534615 baseEnd_4534615 := by
    simpa [prefixWord, tailWord_4534615, baseEnd_4534615] using wordTrace_append hprefix tailTrace_4534615
  have hstable : (prefixWord ++ tailWord_4534615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534615).length < 2 ^ (prefixWord ++ tailWord_4534615).sum := by decide
  have hdescent : baseEnd_4534615 < baseStart_4534615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534626 : List Nat := [3, 3, 2, 1, 1, 2, 3, 3, 1, 4]
def baseStart_4534626 : Nat := 118140960795 + 4534626 * 2 ^ 59
def prefixEnd_4534626 : Nat := 4983230072969 + 3 ^ 40 * 4534626 * 2
def baseEnd_4534626 : Nat := 776147575458360162873547

theorem tailTrace_4534626 : CollatzResearch.WordTrace tailWord_4534626 prefixEnd_4534626 776147575458360162873547 := by
  unfold tailWord_4534626
  simp only [CollatzResearch.WordTrace]
  refine ⟨41347849417457982327149933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110260931779887952872399821 41347849417457982327149933)
  ·
    refine ⟨15505443531546743372681225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41347849417457982327149933 15505443531546743372681225)
    ·
      refine ⟨11629082648660057529510919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15505443531546743372681225 11629082648660057529510919)
      ·
        refine ⟨17443623972990086294266379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11629082648660057529510919 17443623972990086294266379)
        ·
          refine ⟨26165435959485129441399569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17443623972990086294266379 26165435959485129441399569)
          ·
            refine ⟨19624076969613847081049677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26165435959485129441399569 19624076969613847081049677)
            ·
              refine ⟨7359028863605192655393629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19624076969613847081049677 7359028863605192655393629)
              ·
                refine ⟨2759635823851947245772611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7359028863605192655393629 2759635823851947245772611)
                ·
                  refine ⟨4139453735777920868658917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759635823851947245772611 4139453735777920868658917)
                  ·
                    refine ⟨776147575458360162873547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4139453735777920868658917 776147575458360162873547)
                    ·
                      rfl

theorem cell23_4534626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_4534626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534626 prefixEnd_4534626 := by exact prefixLift 4534626
  have htrace : WordTrace (prefixWord ++ tailWord_4534626) baseStart_4534626 baseEnd_4534626 := by
    simpa [prefixWord, tailWord_4534626, baseEnd_4534626] using wordTrace_append hprefix tailTrace_4534626
  have hstable : (prefixWord ++ tailWord_4534626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534626).length < 2 ^ (prefixWord ++ tailWord_4534626).sum := by decide
  have hdescent : baseEnd_4534626 < baseStart_4534626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534655 : List Nat := [1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 4]
def baseStart_4534655 : Nat := 118140960795 + 4534655 * 2 ^ 59
def prefixEnd_4534655 : Nat := 4983230072969 + 3 ^ 40 * 4534655 * 2
def baseEnd_4534655 : Nat := 2328457617314060875158007

theorem tailTrace_4534655 : CollatzResearch.WordTrace tailWord_4534655 prefixEnd_4534655 2328457617314060875158007 := by
  unfold tailWord_4534655
  simp only [CollatzResearch.WordTrace]
  refine ⟨165392455386726867261405419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110261636924484578174270279 165392455386726867261405419)
  ·
    refine ⟨248088683080090300892108129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165392455386726867261405419 248088683080090300892108129)
    ·
      refine ⟨186066512310067725669081097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248088683080090300892108129 186066512310067725669081097)
      ·
        refine ⟨139549884232550794251810823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186066512310067725669081097 139549884232550794251810823)
        ·
          refine ⟨209324826348826191377716235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139549884232550794251810823 209324826348826191377716235)
          ·
            refine ⟨313987239523239287066574353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209324826348826191377716235 313987239523239287066574353)
            ·
              refine ⟨235490429642429465299930765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313987239523239287066574353 235490429642429465299930765)
              ·
                refine ⟨88308911115911049487474037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 235490429642429465299930765 88308911115911049487474037)
                ·
                  refine ⟨8278960417116660889450691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88308911115911049487474037 8278960417116660889450691)
                  ·
                    refine ⟨12418440625674991334176037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8278960417116660889450691 12418440625674991334176037)
                    ·
                      refine ⟨2328457617314060875158007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12418440625674991334176037 2328457617314060875158007)
                      ·
                        rfl

theorem cell23_4534655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 4].length) (baseStart_4534655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534655 prefixEnd_4534655 := by exact prefixLift 4534655
  have htrace : WordTrace (prefixWord ++ tailWord_4534655) baseStart_4534655 baseEnd_4534655 := by
    simpa [prefixWord, tailWord_4534655, baseEnd_4534655] using wordTrace_append hprefix tailTrace_4534655
  have hstable : (prefixWord ++ tailWord_4534655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534655).length < 2 ^ (prefixWord ++ tailWord_4534655).sum := by decide
  have hdescent : baseEnd_4534655 < baseStart_4534655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534682 : List Nat := [3, 1, 1, 4, 1, 3, 1, 2, 1, 6]
def baseStart_4534682 : Nat := 118140960795 + 4534682 * 2 ^ 59
def prefixEnd_4534682 : Nat := 4983230072969 + 3 ^ 40 * 4534682 * 2
def baseEnd_4534682 : Nat := 776157160430577423173461

theorem tailTrace_4534682 : CollatzResearch.WordTrace tailWord_4534682 prefixEnd_4534682 776157160430577423173461 := by
  unfold tailWord_4534682
  simp only [CollatzResearch.WordTrace]
  refine ⟨41348360039407262718159575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110262293438419367248425533 41348360039407262718159575)
  ·
    refine ⟨62022540059110894077239363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41348360039407262718159575 62022540059110894077239363)
    ·
      refine ⟨93033810088666341115859045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62022540059110894077239363 93033810088666341115859045)
      ·
        refine ⟨17443839391624938959223571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93033810088666341115859045 17443839391624938959223571)
        ·
          refine ⟨26165759087437408438835357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17443839391624938959223571 26165759087437408438835357)
          ·
            refine ⟨9812159657789028164563259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26165759087437408438835357 9812159657789028164563259)
            ·
              refine ⟨14718239486683542246844889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9812159657789028164563259 14718239486683542246844889)
              ·
                refine ⟨11038679615012656685133667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14718239486683542246844889 11038679615012656685133667)
                ·
                  refine ⟨16558019422518985027700501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11038679615012656685133667 16558019422518985027700501)
                  ·
                    refine ⟨776157160430577423173461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16558019422518985027700501 776157160430577423173461)
                    ·
                      rfl

theorem cell23_4534682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 2, 1, 6].length) (baseStart_4534682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534682 prefixEnd_4534682 := by exact prefixLift 4534682
  have htrace : WordTrace (prefixWord ++ tailWord_4534682) baseStart_4534682 baseEnd_4534682 := by
    simpa [prefixWord, tailWord_4534682, baseEnd_4534682] using wordTrace_append hprefix tailTrace_4534682
  have hstable : (prefixWord ++ tailWord_4534682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534682).length < 2 ^ (prefixWord ++ tailWord_4534682).sum := by decide
  have hdescent : baseEnd_4534682 < baseStart_4534682 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534692 : List Nat := [2, 3, 1, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_4534692 : Nat := 118140960795 + 4534692 * 2 ^ 59
def prefixEnd_4534692 : Nat := 4983230072969 + 3 ^ 40 * 4534692 * 2
def baseEnd_4534692 : Nat := 2328476616098277230395337

theorem tailTrace_4534692 : CollatzResearch.WordTrace tailWord_4534692 prefixEnd_4534692 2328476616098277230395337 := by
  unfold tailWord_4534692
  simp only [CollatzResearch.WordTrace]
  refine ⟨82696902443796411290251165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110262536591728548387001553 82696902443796411290251165)
  ·
    refine ⟨31011338416423654233844187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82696902443796411290251165 31011338416423654233844187)
    ·
      refine ⟨46517007624635481350766281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31011338416423654233844187 46517007624635481350766281)
      ·
        refine ⟨34887755718476611013074711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46517007624635481350766281 34887755718476611013074711)
        ·
          refine ⟨52331633577714916519612067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34887755718476611013074711 52331633577714916519612067)
          ·
            refine ⟨78497450366572374779418101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52331633577714916519612067 78497450366572374779418101)
            ·
              refine ⟨7359135971866160135570447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78497450366572374779418101 7359135971866160135570447)
              ·
                refine ⟨11038703957799240203355671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7359135971866160135570447 11038703957799240203355671)
                ·
                  refine ⟨16558055936698860305033507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11038703957799240203355671 16558055936698860305033507)
                  ·
                    refine ⟨24837083905048290457550261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16558055936698860305033507 24837083905048290457550261)
                    ·
                      refine ⟨2328476616098277230395337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24837083905048290457550261 2328476616098277230395337)
                      ·
                        rfl

theorem cell23_4534692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_4534692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534692 prefixEnd_4534692 := by exact prefixLift 4534692
  have htrace : WordTrace (prefixWord ++ tailWord_4534692) baseStart_4534692 baseEnd_4534692 := by
    simpa [prefixWord, tailWord_4534692, baseEnd_4534692] using wordTrace_append hprefix tailTrace_4534692
  have hstable : (prefixWord ++ tailWord_4534692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534692).length < 2 ^ (prefixWord ++ tailWord_4534692).sum := by decide
  have hdescent : baseEnd_4534692 < baseStart_4534692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534695 : List Nat := [1, 1, 6, 1, 1, 13]
def baseStart_4534695 : Nat := 118140960795 + 4534695 * 2 ^ 59
def prefixEnd_4534695 : Nat := 4983230072969 + 3 ^ 40 * 4534695 * 2
def baseEnd_4534695 : Nat := 9582214635968068801061

theorem tailTrace_4534695 : CollatzResearch.WordTrace tailWord_4534695 prefixEnd_4534695 9582214635968068801061 := by
  unfold tailWord_4534695
  simp only [CollatzResearch.WordTrace]
  refine ⟨165393914306581954092861539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110262609537721302728574359 165393914306581954092861539)
  ·
    refine ⟨248090871459872931139292309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165393914306581954092861539 248090871459872931139292309)
    ·
      refine ⟨11629259599681543647154327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 248090871459872931139292309 11629259599681543647154327)
      ·
        refine ⟨17443889399522315470731491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11629259599681543647154327 17443889399522315470731491)
        ·
          refine ⟨26165834099283473206097237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17443889399522315470731491 26165834099283473206097237)
          ·
            refine ⟨9582214635968068801061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 26165834099283473206097237 9582214635968068801061)
            ·
              rfl

theorem cell23_4534695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 13].length) (baseStart_4534695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534695 prefixEnd_4534695 := by exact prefixLift 4534695
  have htrace : WordTrace (prefixWord ++ tailWord_4534695) baseStart_4534695 baseEnd_4534695 := by
    simpa [prefixWord, tailWord_4534695, baseEnd_4534695] using wordTrace_append hprefix tailTrace_4534695
  have hstable : (prefixWord ++ tailWord_4534695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534695).length < 2 ^ (prefixWord ++ tailWord_4534695).sum := by decide
  have hdescent : baseEnd_4534695 < baseStart_4534695 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534735 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 5]
def baseStart_4534735 : Nat := 118140960795 + 4534735 * 2 ^ 59
def prefixEnd_4534735 : Nat := 4983230072969 + 3 ^ 40 * 4534735 * 2
def baseEnd_4534735 : Nat := 2328498695766420562157639

theorem tailTrace_4534735 : CollatzResearch.WordTrace tailWord_4534735 prefixEnd_4534735 2328498695766420562157639 := by
  unfold tailWord_4534735
  simp only [CollatzResearch.WordTrace]
  refine ⟨165395373226437040924317659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110263582150958027282878439 165395373226437040924317659)
  ·
    refine ⟨248093059839655561386476489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165395373226437040924317659 248093059839655561386476489)
    ·
      refine ⟨186069794879741671039857367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248093059839655561386476489 186069794879741671039857367)
      ·
        refine ⟨279104692319612506559786051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186069794879741671039857367 279104692319612506559786051)
        ·
          refine ⟨418657038479418759839679077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279104692319612506559786051 418657038479418759839679077)
          ·
            refine ⟨78498194714891017469939827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 418657038479418759839679077 78498194714891017469939827)
            ·
              refine ⟨117747292072336526204909741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78498194714891017469939827 117747292072336526204909741)
              ·
                refine ⟨44155234527126197326841153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117747292072336526204909741 44155234527126197326841153)
                ·
                  refine ⟨33116425895344647995130865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44155234527126197326841153 33116425895344647995130865)
                  ·
                    refine ⟨24837319421508485996348149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33116425895344647995130865 24837319421508485996348149)
                    ·
                      refine ⟨2328498695766420562157639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24837319421508485996348149 2328498695766420562157639)
                      ·
                        rfl

theorem cell23_4534735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 2, 2, 5].length) (baseStart_4534735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534735 prefixEnd_4534735 := by exact prefixLift 4534735
  have htrace : WordTrace (prefixWord ++ tailWord_4534735) baseStart_4534735 baseEnd_4534735 := by
    simpa [prefixWord, tailWord_4534735, baseEnd_4534735] using wordTrace_append hprefix tailTrace_4534735
  have hstable : (prefixWord ++ tailWord_4534735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534735).length < 2 ^ (prefixWord ++ tailWord_4534735).sum := by decide
  have hdescent : baseEnd_4534735 < baseStart_4534735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534740 : List Nat := [2, 4, 1, 2, 2, 2, 2, 3, 1, 2, 2]
def baseStart_4534740 : Nat := 118140960795 + 4534740 * 2 ^ 59
def prefixEnd_4534740 : Nat := 4983230072969 + 3 ^ 40 * 4534740 * 2
def baseEnd_4534740 : Nat := 2328501263169693042595117

theorem tailTrace_4534740 : CollatzResearch.WordTrace tailWord_4534740 prefixEnd_4534740 2328501263169693042595117 := by
  unfold tailWord_4534740
  simp only [CollatzResearch.WordTrace]
  refine ⟨82697777795709463389124837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110263703727612617852166449 82697777795709463389124837)
  ·
    refine ⟨15505833336695524385460907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82697777795709463389124837 15505833336695524385460907)
    ·
      refine ⟨23258750005043286578191361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15505833336695524385460907 23258750005043286578191361)
      ·
        refine ⟨17444062503782464933643521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23258750005043286578191361 17444062503782464933643521)
        ·
          refine ⟨13083046877836848700232641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17444062503782464933643521 13083046877836848700232641)
          ·
            refine ⟨9812285158377636525174481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13083046877836848700232641 9812285158377636525174481)
            ·
              refine ⟨7359213868783227393880861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9812285158377636525174481 7359213868783227393880861)
              ·
                refine ⟨2759705200793710272705323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7359213868783227393880861 2759705200793710272705323)
                ·
                  refine ⟨4139557801190565409057985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759705200793710272705323 4139557801190565409057985)
                  ·
                    refine ⟨3104668350892924056793489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4139557801190565409057985 3104668350892924056793489)
                    ·
                      refine ⟨2328501263169693042595117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3104668350892924056793489 2328501263169693042595117)
                      ·
                        rfl

theorem cell23_4534740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_4534740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534740 prefixEnd_4534740 := by exact prefixLift 4534740
  have htrace : WordTrace (prefixWord ++ tailWord_4534740) baseStart_4534740 baseEnd_4534740 := by
    simpa [prefixWord, tailWord_4534740, baseEnd_4534740] using wordTrace_append hprefix tailTrace_4534740
  have hstable : (prefixWord ++ tailWord_4534740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534740).length < 2 ^ (prefixWord ++ tailWord_4534740).sum := by decide
  have hdescent : baseEnd_4534740 < baseStart_4534740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534773 : List Nat := [1, 3, 5, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_4534773 : Nat := 118140960795 + 4534773 * 2 ^ 59
def prefixEnd_4534773 : Nat := 4983230072969 + 3 ^ 40 * 4534773 * 2
def baseEnd_4534773 : Nat := 2328518208031291413482465

theorem tailTrace_4534773 : CollatzResearch.WordTrace tailWord_4534773 prefixEnd_4534773 2328518208031291413482465 := by
  unfold tailWord_4534773
  simp only [CollatzResearch.WordTrace]
  refine ⟨165396759200299373414200973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110264506133532915609467315 165396759200299373414200973)
  ·
    refine ⟨62023784700112265030325365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165396759200299373414200973 62023784700112265030325365)
    ·
      refine ⟨5814729815635524846593003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62023784700112265030325365 5814729815635524846593003)
      ·
        refine ⟨8722094723453287269889505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5814729815635524846593003 8722094723453287269889505)
        ·
          refine ⟨6541571042589965452417129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8722094723453287269889505 6541571042589965452417129)
          ·
            refine ⟨4906178281942474089312847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6541571042589965452417129 4906178281942474089312847)
            ·
              refine ⟨7359267422913711133969271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4906178281942474089312847 7359267422913711133969271)
              ·
                refine ⟨11038901134370566700953907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7359267422913711133969271 11038901134370566700953907)
                ·
                  refine ⟨16558351701555850051430861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11038901134370566700953907 16558351701555850051430861)
                  ·
                    refine ⟨6209381888083443769286573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16558351701555850051430861 6209381888083443769286573)
                    ·
                      refine ⟨2328518208031291413482465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6209381888083443769286573 2328518208031291413482465)
                      ·
                        rfl

theorem cell23_4534773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_4534773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534773 prefixEnd_4534773 := by exact prefixLift 4534773
  have htrace : WordTrace (prefixWord ++ tailWord_4534773) baseStart_4534773 baseEnd_4534773 := by
    simpa [prefixWord, tailWord_4534773, baseEnd_4534773] using wordTrace_append hprefix tailTrace_4534773
  have hstable : (prefixWord ++ tailWord_4534773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534773).length < 2 ^ (prefixWord ++ tailWord_4534773).sum := by decide
  have hdescent : baseEnd_4534773 < baseStart_4534773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534779 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 8, 2, 2]
def baseStart_4534779 : Nat := 118140960795 + 4534779 * 2 ^ 59
def prefixEnd_4534779 : Nat := 4983230072969 + 3 ^ 40 * 4534779 * 2
def baseEnd_4534779 : Nat := 2328521288915218390007437

theorem tailTrace_4534779 : CollatzResearch.WordTrace tailWord_4534779 prefixEnd_4534779 2328521288915218390007437 := by
  unfold tailWord_4534779
  simp only [CollatzResearch.WordTrace]
  refine ⟨165396978038277636438919391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110264652025518424292612927 165396978038277636438919391)
  ·
    refine ⟨248095467057416454658379087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165396978038277636438919391 248095467057416454658379087)
    ·
      refine ⟨372143200586124681987568631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248095467057416454658379087 372143200586124681987568631)
      ·
        refine ⟨558214800879187022981352947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372143200586124681987568631 558214800879187022981352947)
        ·
          refine ⟨837322201318780534472029421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558214800879187022981352947 837322201318780534472029421)
          ·
            refine ⟨313995825494542700427011033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 837322201318780534472029421 313995825494542700427011033)
            ·
              refine ⟨235496869120907025320258275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 313995825494542700427011033 235496869120907025320258275)
              ·
                refine ⟨353245303681360537980387413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235496869120907025320258275 353245303681360537980387413)
                ·
                  refine ⟨4139593402515943804457665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 353245303681360537980387413 4139593402515943804457665)
                  ·
                    refine ⟨3104695051886957853343249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4139593402515943804457665 3104695051886957853343249)
                    ·
                      refine ⟨2328521288915218390007437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3104695051886957853343249 2328521288915218390007437)
                      ·
                        rfl

theorem cell23_4534779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 8, 2, 2].length) (baseStart_4534779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534779 prefixEnd_4534779 := by exact prefixLift 4534779
  have htrace : WordTrace (prefixWord ++ tailWord_4534779) baseStart_4534779 baseEnd_4534779 := by
    simpa [prefixWord, tailWord_4534779, baseEnd_4534779] using wordTrace_append hprefix tailTrace_4534779
  have hstable : (prefixWord ++ tailWord_4534779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534779).length < 2 ^ (prefixWord ++ tailWord_4534779).sum := by decide
  have hdescent : baseEnd_4534779 < baseStart_4534779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534790 : List Nat := [6, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_4534790 : Nat := 118140960795 + 4534790 * 2 ^ 59
def prefixEnd_4534790 : Nat := 4983230072969 + 3 ^ 40 * 4534790 * 2
def baseEnd_4534790 : Nat := 2328526937202417846969887

theorem tailTrace_4534790 : CollatzResearch.WordTrace tailWord_4534790 prefixEnd_4534790 2328526937202417846969887 := by
  unfold tailWord_4534790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5168668101288680791174057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 110264919494158523545046549 5168668101288680791174057)
  ·
    refine ⟨3876501075966510593380543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5168668101288680791174057 3876501075966510593380543)
    ·
      refine ⟨5814751613949765890070815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3876501075966510593380543 5814751613949765890070815)
      ·
        refine ⟨8722127420924648835106223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5814751613949765890070815 8722127420924648835106223)
        ·
          refine ⟨13083191131386973252659335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8722127420924648835106223 13083191131386973252659335)
          ·
            refine ⟨19624786697080459878989003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13083191131386973252659335 19624786697080459878989003)
            ·
              refine ⟨29437180045620689818483505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19624786697080459878989003 29437180045620689818483505)
              ·
                refine ⟨22077885034215517363862629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29437180045620689818483505 22077885034215517363862629)
                ·
                  refine ⟨4139603443915409505724243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22077885034215517363862629 4139603443915409505724243)
                  ·
                    refine ⟨6209405165873114258586365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4139603443915409505724243 6209405165873114258586365)
                    ·
                      refine ⟨2328526937202417846969887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6209405165873114258586365 2328526937202417846969887)
                      ·
                        rfl

theorem cell23_4534790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_4534790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534790 prefixEnd_4534790 := by exact prefixLift 4534790
  have htrace : WordTrace (prefixWord ++ tailWord_4534790) baseStart_4534790 baseEnd_4534790 := by
    simpa [prefixWord, tailWord_4534790, baseEnd_4534790] using wordTrace_append hprefix tailTrace_4534790
  have hstable : (prefixWord ++ tailWord_4534790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534790).length < 2 ^ (prefixWord ++ tailWord_4534790).sum := by decide
  have hdescent : baseEnd_4534790 < baseStart_4534790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534796 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 4, 2, 2]
def baseStart_4534796 : Nat := 118140960795 + 4534796 * 2 ^ 59
def prefixEnd_4534796 : Nat := 4983230072969 + 3 ^ 40 * 4534796 * 2
def baseEnd_4534796 : Nat := 2328530018086344823494859

theorem tailTrace_4534796 : CollatzResearch.WordTrace tailWord_4534796 prefixEnd_4534796 2328530018086344823494859 := by
  unfold tailWord_4534796
  simp only [CollatzResearch.WordTrace]
  refine ⟨82698799039608024171144121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110265065386144032228192161 82698799039608024171144121)
  ·
    refine ⟨62024099279706018128358091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82698799039608024171144121 62024099279706018128358091)
    ·
      refine ⟨93036148919559027192537137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62024099279706018128358091 93036148919559027192537137)
      ·
        refine ⟨69777111689669270394402853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93036148919559027192537137 69777111689669270394402853)
        ·
          refine ⟨13083208441812988198950535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69777111689669270394402853 13083208441812988198950535)
          ·
            refine ⟨19624812662719482298425803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13083208441812988198950535 19624812662719482298425803)
            ·
              refine ⟨29437218994079223447638705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19624812662719482298425803 29437218994079223447638705)
              ·
                refine ⟨22077914245559417585729029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29437218994079223447638705 22077914245559417585729029)
                ·
                  refine ⟨4139608921042390797324193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22077914245559417585729029 4139608921042390797324193)
                  ·
                    refine ⟨3104706690781793097993145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4139608921042390797324193 3104706690781793097993145)
                    ·
                      refine ⟨2328530018086344823494859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3104706690781793097993145 2328530018086344823494859)
                      ·
                        rfl

theorem cell23_4534796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 4, 2, 2].length) (baseStart_4534796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534796 prefixEnd_4534796 := by exact prefixLift 4534796
  have htrace : WordTrace (prefixWord ++ tailWord_4534796) baseStart_4534796 baseEnd_4534796 := by
    simpa [prefixWord, tailWord_4534796, baseEnd_4534796] using wordTrace_append hprefix tailTrace_4534796
  have hstable : (prefixWord ++ tailWord_4534796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534796).length < 2 ^ (prefixWord ++ tailWord_4534796).sum := by decide
  have hdescent : baseEnd_4534796 < baseStart_4534796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534819 : List Nat := [1, 1, 1, 4, 4, 3, 1, 1, 7]
def baseStart_4534819 : Nat := 118140960795 + 4534819 * 2 ^ 59
def prefixEnd_4534819 : Nat := 4983230072969 + 3 ^ 40 * 4534819 * 2
def baseEnd_4534819 : Nat := 258726869793488692611917

theorem tailTrace_4534819 : CollatzResearch.WordTrace tailWord_4534819 prefixEnd_4534819 258726869793488692611917 := by
  unfold tailWord_4534819
  simp only [CollatzResearch.WordTrace]
  refine ⟨165398436958132723270375511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110265624638755148846917007 165398436958132723270375511)
  ·
    refine ⟨248097655437199084905563267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165398436958132723270375511 248097655437199084905563267)
    ·
      refine ⟨372146483155798627358344901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248097655437199084905563267 372146483155798627358344901)
      ·
        refine ⟨69777465591712242629689669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 372146483155798627358344901 69777465591712242629689669)
        ·
          refine ⟨13083274798446045493066813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69777465591712242629689669 13083274798446045493066813)
          ·
            refine ⟨4906228049417267059900055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13083274798446045493066813 4906228049417267059900055)
            ·
              refine ⟨7359342074125900589850083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4906228049417267059900055 7359342074125900589850083)
              ·
                refine ⟨11039013111188850884775125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7359342074125900589850083 11039013111188850884775125)
                ·
                  refine ⟨258726869793488692611917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11039013111188850884775125 258726869793488692611917)
                  ·
                    rfl

theorem cell23_4534819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 3, 1, 1, 7].length) (baseStart_4534819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534819 prefixEnd_4534819 := by exact prefixLift 4534819
  have htrace : WordTrace (prefixWord ++ tailWord_4534819) baseStart_4534819 baseEnd_4534819 := by
    simpa [prefixWord, tailWord_4534819, baseEnd_4534819] using wordTrace_append hprefix tailTrace_4534819
  have hstable : (prefixWord ++ tailWord_4534819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534819).length < 2 ^ (prefixWord ++ tailWord_4534819).sum := by decide
  have hdescent : baseEnd_4534819 < baseStart_4534819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534830 : List Nat := [4, 1, 3, 1, 3, 1, 1, 3, 2, 2, 2]
def baseStart_4534830 : Nat := 118140960795 + 4534830 * 2 ^ 59
def prefixEnd_4534830 : Nat := 4983230072969 + 3 ^ 40 * 4534830 * 2
def baseEnd_4534830 : Nat := 2328547476428597690469703

theorem tailTrace_4534830 : CollatzResearch.WordTrace tailWord_4534830 prefixEnd_4534830 2328547476428597690469703 := by
  unfold tailWord_4534830
  simp only [CollatzResearch.WordTrace]
  refine ⟨20674854770136609018628243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110265892107395248099350629 20674854770136609018628243)
  ·
    refine ⟨31012282155204913527942365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20674854770136609018628243 31012282155204913527942365)
    ·
      refine ⟨11629605808201842572978387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31012282155204913527942365 11629605808201842572978387)
      ·
        refine ⟨17444408712302763859467581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11629605808201842572978387 17444408712302763859467581)
        ·
          refine ⟨6541653267113536447300343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17444408712302763859467581 6541653267113536447300343)
          ·
            refine ⟨9812479900670304670950515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6541653267113536447300343 9812479900670304670950515)
            ·
              refine ⟨14718719851005457006425773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9812479900670304670950515 14718719851005457006425773)
              ·
                refine ⟨5519519944127046377409665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14718719851005457006425773 5519519944127046377409665)
                ·
                  refine ⟨4139639958095284783057249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5519519944127046377409665 4139639958095284783057249)
                  ·
                    refine ⟨3104729968571463587292937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4139639958095284783057249 3104729968571463587292937)
                    ·
                      refine ⟨2328547476428597690469703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3104729968571463587292937 2328547476428597690469703)
                      ·
                        rfl

theorem cell23_4534830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_4534830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534830 prefixEnd_4534830 := by exact prefixLift 4534830
  have htrace : WordTrace (prefixWord ++ tailWord_4534830) baseStart_4534830 baseEnd_4534830 := by
    simpa [prefixWord, tailWord_4534830, baseEnd_4534830] using wordTrace_append hprefix tailTrace_4534830
  have hstable : (prefixWord ++ tailWord_4534830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534830).length < 2 ^ (prefixWord ++ tailWord_4534830).sum := by decide
  have hdescent : baseEnd_4534830 < baseStart_4534830 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534849 : List Nat := [1, 2, 5, 1, 1, 2, 1, 3, 2, 5]
def baseStart_4534849 : Nat := 118140960795 + 4534849 * 2 ^ 59
def prefixEnd_4534849 : Nat := 4983230072969 + 3 ^ 40 * 4534849 * 2
def baseEnd_4534849 : Nat := 776185744187011038710705

theorem tailTrace_4534849 : CollatzResearch.WordTrace tailWord_4534849 prefixEnd_4534849 776185744187011038710705 := by
  unfold tailWord_4534849
  simp only [CollatzResearch.WordTrace]
  refine ⟨165399531148024038393967601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110266354098682692262645067 165399531148024038393967601)
  ·
    refine ⟨124049648361018028795475701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165399531148024038393967601 124049648361018028795475701)
    ·
      refine ⟨11629654533845440199575847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124049648361018028795475701 11629654533845440199575847)
      ·
        refine ⟨17444481800768160299363771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11629654533845440199575847 17444481800768160299363771)
        ·
          refine ⟨26166722701152240449045657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17444481800768160299363771 26166722701152240449045657)
          ·
            refine ⟨19625042025864180336784243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26166722701152240449045657 19625042025864180336784243)
            ·
              refine ⟨29437563038796270505176365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19625042025864180336784243 29437563038796270505176365)
              ·
                refine ⟨11039086139548601439441137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29437563038796270505176365 11039086139548601439441137)
                ·
                  refine ⟨8279314604661451079580853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11039086139548601439441137 8279314604661451079580853)
                  ·
                    refine ⟨776185744187011038710705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8279314604661451079580853 776185744187011038710705)
                    ·
                      rfl

theorem cell23_4534849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_4534849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534849 prefixEnd_4534849 := by exact prefixLift 4534849
  have htrace : WordTrace (prefixWord ++ tailWord_4534849) baseStart_4534849 baseEnd_4534849 := by
    simpa [prefixWord, tailWord_4534849, baseEnd_4534849] using wordTrace_append hprefix tailTrace_4534849
  have hstable : (prefixWord ++ tailWord_4534849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534849).length < 2 ^ (prefixWord ++ tailWord_4534849).sum := by decide
  have hdescent : baseEnd_4534849 < baseStart_4534849 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534869 : List Nat := [1, 3, 2, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_4534869 : Nat := 118140960795 + 4534869 * 2 ^ 59
def prefixEnd_4534869 : Nat := 4983230072969 + 3 ^ 40 * 4534869 * 2
def baseEnd_4534869 : Nat := 2328567502174123037882023

theorem tailTrace_4534869 : CollatzResearch.WordTrace tailWord_4534869 prefixEnd_4534869 2328567502174123037882023 := by
  unfold tailWord_4534869
  simp only [CollatzResearch.WordTrace]
  refine ⟨165400260607951581809695661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110266840405301054539797107 165400260607951581809695661)
  ·
    refine ⟨62025097727981843178635873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165400260607951581809695661 62025097727981843178635873)
    ·
      refine ⟨46518823295986382383976905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62025097727981843178635873 46518823295986382383976905)
      ·
        refine ⟨34889117471989786787982679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46518823295986382383976905 34889117471989786787982679)
        ·
          refine ⟨52333676207984680181974019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34889117471989786787982679 52333676207984680181974019)
          ·
            refine ⟨78500514311977020272961029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52333676207984680181974019 78500514311977020272961029)
            ·
              refine ⟨14718846433495691301180193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78500514311977020272961029 14718846433495691301180193)
              ·
                refine ⟨11039134825121768475885145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14718846433495691301180193 11039134825121768475885145)
                ·
                  refine ⟨8279351118841326356913859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11039134825121768475885145 8279351118841326356913859)
                  ·
                    refine ⟨12419026678261989535370789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8279351118841326356913859 12419026678261989535370789)
                    ·
                      refine ⟨2328567502174123037882023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12419026678261989535370789 2328567502174123037882023)
                      ·
                        rfl

theorem cell23_4534869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_4534869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534869 prefixEnd_4534869 := by exact prefixLift 4534869
  have htrace : WordTrace (prefixWord ++ tailWord_4534869) baseStart_4534869 baseEnd_4534869 := by
    simpa [prefixWord, tailWord_4534869, baseEnd_4534869] using wordTrace_append hprefix tailTrace_4534869
  have hstable : (prefixWord ++ tailWord_4534869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534869).length < 2 ^ (prefixWord ++ tailWord_4534869).sum := by decide
  have hdescent : baseEnd_4534869 < baseStart_4534869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534896 : List Nat := [2, 1, 1, 1, 7, 1, 1, 2, 3, 4]
def baseStart_4534896 : Nat := 118140960795 + 4534896 * 2 ^ 59
def prefixEnd_4534896 : Nat := 4983230072969 + 3 ^ 40 * 4534896 * 2
def baseEnd_4534896 : Nat := 776193788717264810748133

theorem tailTrace_4534896 : CollatzResearch.WordTrace tailWord_4534896 prefixEnd_4534896 776193788717264810748133 := by
  unfold tailWord_4534896
  simp only [CollatzResearch.WordTrace]
  refine ⟨82700622689426882710464271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110267496919235843613952361 82700622689426882710464271)
  ·
    refine ⟨124050934034140324065696407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82700622689426882710464271 124050934034140324065696407)
    ·
      refine ⟨186076401051210486098544611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124050934034140324065696407 186076401051210486098544611)
      ·
        refine ⟨279114601576815729147816917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186076401051210486098544611 279114601576815729147816917)
        ·
          refine ⟨6541748474456618651901959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 279114601576815729147816917 6541748474456618651901959)
          ·
            refine ⟨9812622711684927977852939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6541748474456618651901959 9812622711684927977852939)
            ·
              refine ⟨14718934067527391966779409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9812622711684927977852939 14718934067527391966779409)
              ·
                refine ⟨11039200550645543975084557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14718934067527391966779409 11039200550645543975084557)
                ·
                  refine ⟨4139700206492078990656709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11039200550645543975084557 4139700206492078990656709)
                  ·
                    refine ⟨776193788717264810748133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4139700206492078990656709 776193788717264810748133)
                    ·
                      rfl

theorem cell23_4534896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 1, 2, 3, 4].length) (baseStart_4534896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534896 prefixEnd_4534896 := by exact prefixLift 4534896
  have htrace : WordTrace (prefixWord ++ tailWord_4534896) baseStart_4534896 baseEnd_4534896 := by
    simpa [prefixWord, tailWord_4534896, baseEnd_4534896] using wordTrace_append hprefix tailTrace_4534896
  have hstable : (prefixWord ++ tailWord_4534896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534896).length < 2 ^ (prefixWord ++ tailWord_4534896).sum := by decide
  have hdescent : baseEnd_4534896 < baseStart_4534896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534913 : List Nat := [1, 2, 4, 2, 1, 1, 4, 3, 1, 4]
def baseStart_4534913 : Nat := 118140960795 + 4534913 * 2 ^ 59
def prefixEnd_4534913 : Nat := 4983230072969 + 3 ^ 40 * 4534913 * 2
def baseEnd_4534913 : Nat := 776196698440973621910607

theorem tailTrace_4534913 : CollatzResearch.WordTrace tailWord_4534913 prefixEnd_4534913 776196698440973621910607 := by
  unfold tailWord_4534913
  simp only [CollatzResearch.WordTrace]
  refine ⟨165401865419792177324297393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110267910279861451549531595 165401865419792177324297393)
  ·
    refine ⟨124051399064844132993223045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165401865419792177324297393 124051399064844132993223045)
    ·
      refine ⟨23259637324658274936229321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124051399064844132993223045 23259637324658274936229321)
      ·
        refine ⟨17444727993493706202171991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23259637324658274936229321 17444727993493706202171991)
        ·
          refine ⟨26167091990240559303257987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17444727993493706202171991 26167091990240559303257987)
          ·
            refine ⟨39250637985360838954886981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26167091990240559303257987 39250637985360838954886981)
            ·
              refine ⟨7359494622255157304041309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39250637985360838954886981 7359494622255157304041309)
              ·
                refine ⟨2759810483345683989015491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7359494622255157304041309 2759810483345683989015491)
                ·
                  refine ⟨4139715725018525983523237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759810483345683989015491 4139715725018525983523237)
                  ·
                    refine ⟨776196698440973621910607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4139715725018525983523237 776196698440973621910607)
                    ·
                      rfl

theorem cell23_4534913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 4, 3, 1, 4].length) (baseStart_4534913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534913 prefixEnd_4534913 := by exact prefixLift 4534913
  have htrace : WordTrace (prefixWord ++ tailWord_4534913) baseStart_4534913 baseEnd_4534913 := by
    simpa [prefixWord, tailWord_4534913, baseEnd_4534913] using wordTrace_append hprefix tailTrace_4534913
  have hstable : (prefixWord ++ tailWord_4534913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534913).length < 2 ^ (prefixWord ++ tailWord_4534913).sum := by decide
  have hdescent : baseEnd_4534913 < baseStart_4534913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534976 : List Nat := [2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 4]
def baseStart_4534976 : Nat := 118140960795 + 4534976 * 2 ^ 59
def prefixEnd_4534976 : Nat := 4983230072969 + 3 ^ 40 * 4534976 * 2
def baseEnd_4534976 : Nat := 2328622444604154119244031

theorem tailTrace_4534976 : CollatzResearch.WordTrace tailWord_4534976 prefixEnd_4534976 2328622444604154119244031 := by
  unfold tailWord_4534976
  simp only [CollatzResearch.WordTrace]
  refine ⟨82702081609281969541920391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110269442145709292722560521 82702081609281969541920391)
  ·
    refine ⟨124053122413922954312880587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82702081609281969541920391 124053122413922954312880587)
    ·
      refine ⟨186079683620884431469320881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124053122413922954312880587 186079683620884431469320881)
      ·
        refine ⟨139559762715663323601990661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186079683620884431469320881 139559762715663323601990661)
        ·
          refine ⟨26167455509186873175373249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 139559762715663323601990661 26167455509186873175373249)
          ·
            refine ⟨19625591631890154881529937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26167455509186873175373249 19625591631890154881529937)
            ·
              refine ⟨14719193723917616161147453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19625591631890154881529937 14719193723917616161147453)
              ·
                refine ⟨5519697646469106060430295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14719193723917616161147453 5519697646469106060430295)
                ·
                  refine ⟨8279546469703659090645443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5519697646469106060430295 8279546469703659090645443)
                  ·
                    refine ⟨12419319704555488635968165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8279546469703659090645443 12419319704555488635968165)
                    ·
                      refine ⟨2328622444604154119244031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12419319704555488635968165 2328622444604154119244031)
                      ·
                        rfl

theorem cell23_4534976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 3, 1, 1, 4].length) (baseStart_4534976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534976 prefixEnd_4534976 := by exact prefixLift 4534976
  have htrace : WordTrace (prefixWord ++ tailWord_4534976) baseStart_4534976 baseEnd_4534976 := by
    simpa [prefixWord, tailWord_4534976, baseEnd_4534976] using wordTrace_append hprefix tailTrace_4534976
  have hstable : (prefixWord ++ tailWord_4534976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534976).length < 2 ^ (prefixWord ++ tailWord_4534976).sum := by decide
  have hdescent : baseEnd_4534976 < baseStart_4534976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534986 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 4, 4]
def baseStart_4534986 : Nat := 118140960795 + 4534986 * 2 ^ 59
def prefixEnd_4534986 : Nat := 4983230072969 + 3 ^ 40 * 4534986 * 2
def baseEnd_4534986 : Nat := 776209193136899693372995

theorem tailTrace_4534986 : CollatzResearch.WordTrace tailWord_4534986 prefixEnd_4534986 776209193136899693372995 := by
  unfold tailWord_4534986
  simp only [CollatzResearch.WordTrace]
  refine ⟨41351131987131927697926203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110269685299018473861136541 41351131987131927697926203)
  ·
    refine ⟨62026697980697891546889305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41351131987131927697926203 62026697980697891546889305)
    ·
      refine ⟨46520023485523418660166979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62026697980697891546889305 46520023485523418660166979)
      ·
        refine ⟨69780035228285127990250469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46520023485523418660166979 69780035228285127990250469)
        ·
          refine ⟨13083756605303461498171963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69780035228285127990250469 13083756605303461498171963)
          ·
            refine ⟨19625634907955192247257945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13083756605303461498171963 19625634907955192247257945)
            ·
              refine ⟨14719226180966394185443459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19625634907955192247257945 14719226180966394185443459)
              ·
                refine ⟨22078839271449591278165189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14719226180966394185443459 22078839271449591278165189)
                ·
                  refine ⟨4139782363396798364655973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22078839271449591278165189 4139782363396798364655973)
                  ·
                    refine ⟨776209193136899693372995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4139782363396798364655973 776209193136899693372995)
                    ·
                      rfl

theorem cell23_4534986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_4534986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534986 prefixEnd_4534986 := by exact prefixLift 4534986
  have htrace : WordTrace (prefixWord ++ tailWord_4534986) baseStart_4534986 baseEnd_4534986 := by
    simpa [prefixWord, tailWord_4534986, baseEnd_4534986] using wordTrace_append hprefix tailTrace_4534986
  have hstable : (prefixWord ++ tailWord_4534986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534986).length < 2 ^ (prefixWord ++ tailWord_4534986).sum := by decide
  have hdescent : baseEnd_4534986 < baseStart_4534986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4534999 : List Nat := [1, 1, 3, 2, 1, 5, 2, 8]
def baseStart_4534999 : Nat := 118140960795 + 4534999 * 2 ^ 59
def prefixEnd_4534999 : Nat := 4983230072969 + 3 ^ 40 * 4534999 * 2
def baseEnd_4534999 : Nat := 86245713135526204787275

theorem tailTrace_4534999 : CollatzResearch.WordTrace tailWord_4534999 prefixEnd_4534999 86245713135526204787275 := by
  unfold tailWord_4534999
  simp only [CollatzResearch.WordTrace]
  refine ⟨165405002097480614011928051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110270001398320409341285367 165405002097480614011928051)
  ·
    refine ⟨248107503146220921017892077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165405002097480614011928051 248107503146220921017892077)
    ·
      refine ⟨93040313679832845381709529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248107503146220921017892077 93040313679832845381709529)
      ·
        refine ⟨69780235259874634036282147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93040313679832845381709529 69780235259874634036282147)
        ·
          refine ⟨104670352889811951054423221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69780235259874634036282147 104670352889811951054423221)
          ·
            refine ⟨9812845583419870411352177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104670352889811951054423221 9812845583419870411352177)
            ·
              refine ⟨7359634187564902808514133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9812845583419870411352177 7359634187564902808514133)
              ·
                refine ⟨86245713135526204787275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7359634187564902808514133 86245713135526204787275)
                ·
                  rfl

theorem cell23_4534999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 8].length) (baseStart_4534999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4534999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4534999 prefixEnd_4534999 := by exact prefixLift 4534999
  have htrace : WordTrace (prefixWord ++ tailWord_4534999) baseStart_4534999 baseEnd_4534999 := by
    simpa [prefixWord, tailWord_4534999, baseEnd_4534999] using wordTrace_append hprefix tailTrace_4534999
  have hstable : (prefixWord ++ tailWord_4534999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4534999).length < 2 ^ (prefixWord ++ tailWord_4534999).sum := by decide
  have hdescent : baseEnd_4534999 < baseStart_4534999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4534999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535013 : List Nat := [1, 3, 1, 4, 1, 2, 3, 2, 1, 2, 3]
def baseStart_4535013 : Nat := 118140960795 + 4535013 * 2 ^ 59
def prefixEnd_4535013 : Nat := 4983230072969 + 3 ^ 40 * 4535013 * 2
def baseEnd_4535013 : Nat := 2328641443388370474481361

theorem tailTrace_4535013 : CollatzResearch.WordTrace tailWord_4535013 prefixEnd_4535013 2328641443388370474481361 := by
  unfold tailWord_4535013
  simp only [CollatzResearch.WordTrace]
  refine ⟨165405512719429894402937693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110270341812953262935291795 165405512719429894402937693)
  ·
    refine ⟨62027067269786210401101635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165405512719429894402937693 62027067269786210401101635)
    ·
      refine ⟨93040600904679315601652453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62027067269786210401101635 93040600904679315601652453)
      ·
        refine ⟨17445112669627371675309835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93040600904679315601652453 17445112669627371675309835)
        ·
          refine ⟨26167669004441057512964753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17445112669627371675309835 26167669004441057512964753)
          ·
            refine ⟨19625751753330793134723565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26167669004441057512964753 19625751753330793134723565)
            ·
              refine ⟨7359656907499047425521337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19625751753330793134723565 7359656907499047425521337)
              ·
                refine ⟨5519742680624285569141003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7359656907499047425521337 5519742680624285569141003)
                ·
                  refine ⟨8279614020936428353711505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5519742680624285569141003 8279614020936428353711505)
                  ·
                    refine ⟨6209710515702321265283629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8279614020936428353711505 6209710515702321265283629)
                    ·
                      refine ⟨2328641443388370474481361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6209710515702321265283629 2328641443388370474481361)
                      ·
                        rfl

theorem cell23_4535013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_4535013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535013 prefixEnd_4535013 := by exact prefixLift 4535013
  have htrace : WordTrace (prefixWord ++ tailWord_4535013) baseStart_4535013 baseEnd_4535013 := by
    simpa [prefixWord, tailWord_4535013, baseEnd_4535013] using wordTrace_append hprefix tailTrace_4535013
  have hstable : (prefixWord ++ tailWord_4535013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535013).length < 2 ^ (prefixWord ++ tailWord_4535013).sum := by decide
  have hdescent : baseEnd_4535013 < baseStart_4535013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535026 : List Nat := [3, 2, 1, 3, 1, 2, 1, 1, 3, 3, 3]
def baseStart_4535026 : Nat := 118140960795 + 4535026 * 2 ^ 59
def prefixEnd_4535026 : Nat := 4983230072969 + 3 ^ 40 * 4535026 * 2
def baseEnd_4535026 : Nat := 2328648118636878923618801

theorem tailTrace_4535026 : CollatzResearch.WordTrace tailWord_4535026 prefixEnd_4535026 2328648118636878923618801 := by
  unfold tailWord_4535026
  simp only [CollatzResearch.WordTrace]
  refine ⟨41351496717095699405790233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110270657912255198415440621 41351496717095699405790233)
  ·
    refine ⟨31013622537821774554342675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41351496717095699405790233 31013622537821774554342675)
    ·
      refine ⟨46520433806732661831514013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31013622537821774554342675 46520433806732661831514013)
      ·
        refine ⟨17445162677524748186817755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46520433806732661831514013 17445162677524748186817755)
        ·
          refine ⟨26167744016287122280226633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17445162677524748186817755 26167744016287122280226633)
          ·
            refine ⟨19625808012215341710169975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26167744016287122280226633 19625808012215341710169975)
            ·
              refine ⟨29438712018323012565254963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19625808012215341710169975 29438712018323012565254963)
              ·
                refine ⟨44158068027484518847882445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29438712018323012565254963 44158068027484518847882445)
                ·
                  refine ⟨16559275510306694567955917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44158068027484518847882445 16559275510306694567955917)
                  ·
                    refine ⟨6209728316365010462983469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16559275510306694567955917 6209728316365010462983469)
                    ·
                      refine ⟨2328648118636878923618801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6209728316365010462983469 2328648118636878923618801)
                      ·
                        rfl

theorem cell23_4535026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_4535026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535026 prefixEnd_4535026 := by exact prefixLift 4535026
  have htrace : WordTrace (prefixWord ++ tailWord_4535026) baseStart_4535026 baseEnd_4535026 := by
    simpa [prefixWord, tailWord_4535026, baseEnd_4535026] using wordTrace_append hprefix tailTrace_4535026
  have hstable : (prefixWord ++ tailWord_4535026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535026).length < 2 ^ (prefixWord ++ tailWord_4535026).sum := by decide
  have hdescent : baseEnd_4535026 < baseStart_4535026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535030 : List Nat := [5, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3]
def baseStart_4535030 : Nat := 118140960795 + 4535030 * 2 ^ 59
def prefixEnd_4535030 : Nat := 4983230072969 + 3 ^ 40 * 4535030 * 2
def baseEnd_4535030 : Nat := 2328650172559496907968783

theorem tailTrace_4535030 : CollatzResearch.WordTrace tailWord_4535030 prefixEnd_4535030 2328650172559496907968783 := by
  unfold tailWord_4535030
  simp only [CollatzResearch.WordTrace]
  refine ⟨10337883297523019144144159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110270755173578870870871029 10337883297523019144144159)
  ·
    refine ⟨15506824946284528716216239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10337883297523019144144159 15506824946284528716216239)
    ·
      refine ⟨23260237419426793074324359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15506824946284528716216239 23260237419426793074324359)
      ·
        refine ⟨34890356129140189611486539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23260237419426793074324359 34890356129140189611486539)
        ·
          refine ⟨52335534193710284417229809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34890356129140189611486539 52335534193710284417229809)
          ·
            refine ⟨39251650645282713312922357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52335534193710284417229809 39251650645282713312922357)
            ·
              refine ⟨3679842247995254373086471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39251650645282713312922357 3679842247995254373086471)
              ·
                refine ⟨5519763371992881559629707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3679842247995254373086471 5519763371992881559629707)
                ·
                  refine ⟨8279645057989322339444561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5519763371992881559629707 8279645057989322339444561)
                  ·
                    refine ⟨6209733793491991754583421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8279645057989322339444561 6209733793491991754583421)
                    ·
                      refine ⟨2328650172559496907968783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6209733793491991754583421 2328650172559496907968783)
                      ·
                        rfl

theorem cell23_4535030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3].length) (baseStart_4535030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535030 prefixEnd_4535030 := by exact prefixLift 4535030
  have htrace : WordTrace (prefixWord ++ tailWord_4535030) baseStart_4535030 baseEnd_4535030 := by
    simpa [prefixWord, tailWord_4535030, baseEnd_4535030] using wordTrace_append hprefix tailTrace_4535030
  have hstable : (prefixWord ++ tailWord_4535030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535030).length < 2 ^ (prefixWord ++ tailWord_4535030).sum := by decide
  have hdescent : baseEnd_4535030 < baseStart_4535030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535049 : List Nat := [1, 2, 1, 1, 3, 2, 3, 1, 2, 3, 4]
def baseStart_4535049 : Nat := 118140960795 + 4535049 * 2 ^ 59
def prefixEnd_4535049 : Nat := 4983230072969 + 3 ^ 40 * 4535049 * 2
def baseEnd_4535049 : Nat := 2328659928691932333631195

theorem tailTrace_4535049 : CollatzResearch.WordTrace tailWord_4535049 prefixEnd_4535049 2328659928691932333631195 := by
  unfold tailWord_4535049
  simp only [CollatzResearch.WordTrace]
  refine ⟨165406825747299472551248201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110271217164866315034165467 165406825747299472551248201)
  ·
    refine ⟨124055119310474604413436151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165406825747299472551248201 124055119310474604413436151)
    ·
      refine ⟨186082678965711906620154227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124055119310474604413436151 186082678965711906620154227)
      ·
        refine ⟨279124018448567859930231341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186082678965711906620154227 279124018448567859930231341)
        ·
          refine ⟨104671506918212947473836753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 279124018448567859930231341 104671506918212947473836753)
          ·
            refine ⟨78503630188659710605377565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104671506918212947473836753 78503630188659710605377565)
            ·
              refine ⟨29438861320747391477016587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78503630188659710605377565 29438861320747391477016587)
              ·
                refine ⟨44158291981121087215524881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29438861320747391477016587 44158291981121087215524881)
                ·
                  refine ⟨33118718985840815411643661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44158291981121087215524881 33118718985840815411643661)
                  ·
                    refine ⟨12419519619690305779366373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33118718985840815411643661 12419519619690305779366373)
                    ·
                      refine ⟨2328659928691932333631195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12419519619690305779366373 2328659928691932333631195)
                      ·
                        rfl

theorem cell23_4535049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 3, 4].length) (baseStart_4535049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535049 prefixEnd_4535049 := by exact prefixLift 4535049
  have htrace : WordTrace (prefixWord ++ tailWord_4535049) baseStart_4535049 baseEnd_4535049 := by
    simpa [prefixWord, tailWord_4535049, baseEnd_4535049] using wordTrace_append hprefix tailTrace_4535049
  have hstable : (prefixWord ++ tailWord_4535049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535049).length < 2 ^ (prefixWord ++ tailWord_4535049).sum := by decide
  have hdescent : baseEnd_4535049 < baseStart_4535049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535059 : List Nat := [1, 1, 1, 2, 1, 3, 5, 1, 2, 6]
def baseStart_4535059 : Nat := 118140960795 + 4535059 * 2 ^ 59
def prefixEnd_4535059 : Nat := 4983230072969 + 3 ^ 40 * 4535059 * 2
def baseEnd_4535059 : Nat := 776221687832825764835383

theorem tailTrace_4535059 : CollatzResearch.WordTrace tailWord_4535059 prefixEnd_4535059 776221687832825764835383 := by
  unfold tailWord_4535059
  simp only [CollatzResearch.WordTrace]
  refine ⟨165407190477263244259112231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110271460318175496172741487 165407190477263244259112231)
  ·
    refine ⟨248110785715894866388668347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165407190477263244259112231 248110785715894866388668347)
    ·
      refine ⟨372166178573842299583002521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248110785715894866388668347 372166178573842299583002521)
      ·
        refine ⟨279124633930381724687251891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372166178573842299583002521 279124633930381724687251891)
        ·
          refine ⟨418686950895572587030877837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279124633930381724687251891 418686950895572587030877837)
          ·
            refine ⟨157007606585839720136579189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 418686950895572587030877837 157007606585839720136579189)
            ·
              refine ⟨14719463117422473762804299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157007606585839720136579189 14719463117422473762804299)
              ·
                refine ⟨22079194676133710644206449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14719463117422473762804299 22079194676133710644206449)
                ·
                  refine ⟨16559396007100282983154837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22079194676133710644206449 16559396007100282983154837)
                  ·
                    refine ⟨776221687832825764835383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16559396007100282983154837 776221687832825764835383)
                    ·
                      rfl

theorem cell23_4535059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 1, 2, 6].length) (baseStart_4535059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535059 prefixEnd_4535059 := by exact prefixLift 4535059
  have htrace : WordTrace (prefixWord ++ tailWord_4535059) baseStart_4535059 baseEnd_4535059 := by
    simpa [prefixWord, tailWord_4535059, baseEnd_4535059] using wordTrace_append hprefix tailTrace_4535059
  have hstable : (prefixWord ++ tailWord_4535059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535059).length < 2 ^ (prefixWord ++ tailWord_4535059).sum := by decide
  have hdescent : baseEnd_4535059 < baseStart_4535059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535089 : List Nat := [1, 2, 2, 3, 2, 1, 1, 2, 9]
def baseStart_4535089 : Nat := 118140960795 + 4535089 * 2 ^ 59
def prefixEnd_4535089 : Nat := 4983230072969 + 3 ^ 40 * 4535089 * 2
def baseEnd_4535089 : Nat := 258742274213123575236779

theorem tailTrace_4535089 : CollatzResearch.WordTrace tailWord_4535089 prefixEnd_4535089 258742274213123575236779 := by
  unfold tailWord_4535089
  simp only [CollatzResearch.WordTrace]
  refine ⟨165408284667154559382704321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110272189778103039588469547 165408284667154559382704321)
  ·
    refine ⟨124056213500365919537028241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165408284667154559382704321 124056213500365919537028241)
    ·
      refine ⟨93042160125274439652771181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124056213500365919537028241 93042160125274439652771181)
      ·
        refine ⟨34890810046977914869789193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93042160125274439652771181 34890810046977914869789193)
        ·
          refine ⟨26168107535233436152341895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34890810046977914869789193 26168107535233436152341895)
          ·
            refine ⟨39252161302850154228512843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26168107535233436152341895 39252161302850154228512843)
            ·
              refine ⟨58878241954275231342769265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39252161302850154228512843 58878241954275231342769265)
              ·
                refine ⟨44158681465706423507076949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58878241954275231342769265 44158681465706423507076949)
                ·
                  refine ⟨258742274213123575236779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44158681465706423507076949 258742274213123575236779)
                  ·
                    rfl

theorem cell23_4535089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 2, 9].length) (baseStart_4535089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535089 prefixEnd_4535089 := by exact prefixLift 4535089
  have htrace : WordTrace (prefixWord ++ tailWord_4535089) baseStart_4535089 baseEnd_4535089 := by
    simpa [prefixWord, tailWord_4535089, baseEnd_4535089] using wordTrace_append hprefix tailTrace_4535089
  have hstable : (prefixWord ++ tailWord_4535089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535089).length < 2 ^ (prefixWord ++ tailWord_4535089).sum := by decide
  have hdescent : baseEnd_4535089 < baseStart_4535089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535094 : List Nat := [5, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_4535094 : Nat := 118140960795 + 4535094 * 2 ^ 59
def prefixEnd_4535094 : Nat := 4983230072969 + 3 ^ 40 * 4535094 * 2
def baseEnd_4535094 : Nat := 2328683035321384657568489

theorem tailTrace_4535094 : CollatzResearch.WordTrace tailWord_4535094 prefixEnd_4535094 2328683035321384657568489 := by
  unfold tailWord_4535094
  simp only [CollatzResearch.WordTrace]
  refine ⟨10338029189508527827289771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110272311354757630157757557 10338029189508527827289771)
  ·
    refine ⟨15507043784262791740934657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10338029189508527827289771 15507043784262791740934657)
    ·
      refine ⟨11630282838197093805700993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15507043784262791740934657 11630282838197093805700993)
      ·
        refine ⟨8722712128647820354275745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11630282838197093805700993 8722712128647820354275745)
        ·
          refine ⟨6542034096485865265706809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8722712128647820354275745 6542034096485865265706809)
          ·
            refine ⟨4906525572364398949280107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6542034096485865265706809 4906525572364398949280107)
            ·
              refine ⟨7359788358546598423920161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4906525572364398949280107 7359788358546598423920161)
              ·
                refine ⟨5519841268909948817940121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7359788358546598423920161 5519841268909948817940121)
                ·
                  refine ⟨4139880951682461613455091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5519841268909948817940121 4139880951682461613455091)
                  ·
                    refine ⟨6209821427523692420182637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4139880951682461613455091 6209821427523692420182637)
                    ·
                      refine ⟨2328683035321384657568489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6209821427523692420182637 2328683035321384657568489)
                      ·
                        rfl

theorem cell23_4535094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_4535094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535094 prefixEnd_4535094 := by exact prefixLift 4535094
  have htrace : WordTrace (prefixWord ++ tailWord_4535094) baseStart_4535094 baseEnd_4535094 := by
    simpa [prefixWord, tailWord_4535094, baseEnd_4535094] using wordTrace_append hprefix tailTrace_4535094
  have hstable : (prefixWord ++ tailWord_4535094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535094).length < 2 ^ (prefixWord ++ tailWord_4535094).sum := by decide
  have hdescent : baseEnd_4535094 < baseStart_4535094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535136 : List Nat := [2, 1, 1, 3, 3, 1, 2, 3, 2, 5]
def baseStart_4535136 : Nat := 118140960795 + 4535136 * 2 ^ 59
def prefixEnd_4535136 : Nat := 4983230072969 + 3 ^ 40 * 4535136 * 2
def baseEnd_4535136 : Nat := 776234867169624497747765

theorem tailTrace_4535136 : CollatzResearch.WordTrace tailWord_4535136 prefixEnd_4535136 776234867169624497747765 := by
  unfold tailWord_4535136
  simp only [CollatzResearch.WordTrace]
  refine ⟨82704999448992143204832631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110273332598656190939776841 82704999448992143204832631)
  ·
    refine ⟨124057499173488214807248947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82704999448992143204832631 124057499173488214807248947)
    ·
      refine ⟨186086248760232322210873421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124057499173488214807248947 186086248760232322210873421)
      ·
        refine ⟨69782343285087120829077533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186086248760232322210873421 69782343285087120829077533)
        ·
          refine ⟨26168378731907670310904075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69782343285087120829077533 26168378731907670310904075)
          ·
            refine ⟨39252568097861505466356113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26168378731907670310904075 39252568097861505466356113)
            ·
              refine ⟨29439426073396129099767085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39252568097861505466356113 29439426073396129099767085)
              ·
                refine ⟨11039784777523548412412657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29439426073396129099767085 11039784777523548412412657)
                ·
                  refine ⟨8279838583142661309309493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11039784777523548412412657 8279838583142661309309493)
                  ·
                    refine ⟨776234867169624497747765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8279838583142661309309493 776234867169624497747765)
                    ·
                      rfl

theorem cell23_4535136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 3, 2, 5].length) (baseStart_4535136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535136 prefixEnd_4535136 := by exact prefixLift 4535136
  have htrace : WordTrace (prefixWord ++ tailWord_4535136) baseStart_4535136 baseEnd_4535136 := by
    simpa [prefixWord, tailWord_4535136, baseEnd_4535136] using wordTrace_append hprefix tailTrace_4535136
  have hstable : (prefixWord ++ tailWord_4535136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535136).length < 2 ^ (prefixWord ++ tailWord_4535136).sum := by decide
  have hdescent : baseEnd_4535136 < baseStart_4535136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535140 : List Nat := [2, 3, 1, 1, 4, 3, 1, 3, 5]
def baseStart_4535140 : Nat := 118140960795 + 4535140 * 2 ^ 59
def prefixEnd_4535140 : Nat := 4983230072969 + 3 ^ 40 * 4535140 * 2
def baseEnd_4535140 : Nat := 258745183936832386399253

theorem tailTrace_4535140 : CollatzResearch.WordTrace tailWord_4535140 prefixEnd_4535140 258745183936832386399253 := by
  unfold tailWord_4535140
  simp only [CollatzResearch.WordTrace]
  refine ⟨82705072394984897546405437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110273429859979863395207249 82705072394984897546405437)
  ·
    refine ⟨31014402148119336579902039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82705072394984897546405437 31014402148119336579902039)
    ·
      refine ⟨46521603222179004869853059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31014402148119336579902039 46521603222179004869853059)
      ·
        refine ⟨69782404833268507304779589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46521603222179004869853059 69782404833268507304779589)
        ·
          refine ⟨13084200906237845119646173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69782404833268507304779589 13084200906237845119646173)
          ·
            refine ⟨4906575339839191919867315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13084200906237845119646173 4906575339839191919867315)
            ·
              refine ⟨7359863009758787879800973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4906575339839191919867315 7359863009758787879800973)
              ·
                refine ⟨2759948628659545454925365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7359863009758787879800973 2759948628659545454925365)
                ·
                  refine ⟨258745183936832386399253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2759948628659545454925365 258745183936832386399253)
                  ·
                    rfl

theorem cell23_4535140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 3, 5].length) (baseStart_4535140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535140 prefixEnd_4535140 := by exact prefixLift 4535140
  have htrace : WordTrace (prefixWord ++ tailWord_4535140) baseStart_4535140 baseEnd_4535140 := by
    simpa [prefixWord, tailWord_4535140, baseEnd_4535140] using wordTrace_append hprefix tailTrace_4535140
  have hstable : (prefixWord ++ tailWord_4535140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535140).length < 2 ^ (prefixWord ++ tailWord_4535140).sum := by decide
  have hdescent : baseEnd_4535140 < baseStart_4535140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535217 : List Nat := [1, 2, 2, 4, 3, 1, 1, 4, 1, 4]
def baseStart_4535217 : Nat := 118140960795 + 4535217 * 2 ^ 59
def prefixEnd_4535217 : Nat := 4983230072969 + 3 ^ 40 * 4535217 * 2
def baseEnd_4535217 : Nat := 776248731147295892110141

theorem tailTrace_4535217 : CollatzResearch.WordTrace tailWord_4535217 prefixEnd_4535217 776248731147295892110141 := by
  unfold tailWord_4535217
  simp only [CollatzResearch.WordTrace]
  refine ⟨165412953210690837243363905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110275302140460558162242603 165412953210690837243363905)
  ·
    refine ⟨124059714908018127932522929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165412953210690837243363905 124059714908018127932522929)
    ·
      refine ⟨93044786181013595949392197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124059714908018127932522929 93044786181013595949392197)
      ·
        refine ⟨17445897408940049240511037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93044786181013595949392197 17445897408940049240511037)
        ·
          refine ⟨6542211528352518465191639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17445897408940049240511037 6542211528352518465191639)
          ·
            refine ⟨9813317292528777697787459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6542211528352518465191639 9813317292528777697787459)
            ·
              refine ⟨14719975938793166546681189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9813317292528777697787459 14719975938793166546681189)
              ·
                refine ⟨2759995488523718727502723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14719975938793166546681189 2759995488523718727502723)
                ·
                  refine ⟨4139993232785578091254085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759995488523718727502723 4139993232785578091254085)
                  ·
                    refine ⟨776248731147295892110141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4139993232785578091254085 776248731147295892110141)
                    ·
                      rfl

theorem cell23_4535217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4, 1, 4].length) (baseStart_4535217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535217 prefixEnd_4535217 := by exact prefixLift 4535217
  have htrace : WordTrace (prefixWord ++ tailWord_4535217) baseStart_4535217 baseEnd_4535217 := by
    simpa [prefixWord, tailWord_4535217, baseEnd_4535217] using wordTrace_append hprefix tailTrace_4535217
  have hstable : (prefixWord ++ tailWord_4535217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535217).length < 2 ^ (prefixWord ++ tailWord_4535217).sum := by decide
  have hdescent : baseEnd_4535217 < baseStart_4535217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535226 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 5, 5]
def baseStart_4535226 : Nat := 118140960795 + 4535226 * 2 ^ 59
def prefixEnd_4535226 : Nat := 4983230072969 + 3 ^ 40 * 4535226 * 2
def baseEnd_4535226 : Nat := 776250271589259380372627

theorem tailTrace_4535226 : CollatzResearch.WordTrace tailWord_4535226 prefixEnd_4535226 776250271589259380372627 := by
  unfold tailWord_4535226
  simp only [CollatzResearch.WordTrace]
  refine ⟨41353320366914557945110383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110275520978438821186961021 41353320366914557945110383)
  ·
    refine ⟨62029980550371836917665575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41353320366914557945110383 62029980550371836917665575)
    ·
      refine ⟨93044970825557755376498363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62029980550371836917665575 93044970825557755376498363)
      ·
        refine ⟨139567456238336633064747545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93044970825557755376498363 139567456238336633064747545)
        ·
          refine ⟨104675592178752474798560659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139567456238336633064747545 104675592178752474798560659)
          ·
            refine ⟨157013388268128712197840989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104675592178752474798560659 157013388268128712197840989)
            ·
              refine ⟨58880020600548267074190371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157013388268128712197840989 58880020600548267074190371)
              ·
                refine ⟨88320030900822400611285557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58880020600548267074190371 88320030900822400611285557)
                ·
                  refine ⟨8280002896952100057308021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88320030900822400611285557 8280002896952100057308021)
                  ·
                    refine ⟨776250271589259380372627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8280002896952100057308021 776250271589259380372627)
                    ·
                      rfl

theorem cell23_4535226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 5, 5].length) (baseStart_4535226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535226 prefixEnd_4535226 := by exact prefixLift 4535226
  have htrace : WordTrace (prefixWord ++ tailWord_4535226) baseStart_4535226 baseEnd_4535226 := by
    simpa [prefixWord, tailWord_4535226, baseEnd_4535226] using wordTrace_append hprefix tailTrace_4535226
  have hstable : (prefixWord ++ tailWord_4535226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535226).length < 2 ^ (prefixWord ++ tailWord_4535226).sum := by decide
  have hdescent : baseEnd_4535226 < baseStart_4535226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535238 : List Nat := [6, 1, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_4535238 : Nat := 118140960795 + 4535238 * 2 ^ 59
def prefixEnd_4535238 : Nat := 4983230072969 + 3 ^ 40 * 4535238 * 2
def baseEnd_4535238 : Nat := 776252325511877364722609

theorem tailTrace_4535238 : CollatzResearch.WordTrace tailWord_4535238 prefixEnd_4535238 776252325511877364722609 := by
  unfold tailWord_4535238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5169178723237961182183699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 110275812762409838553252245 5169178723237961182183699)
  ·
    refine ⟨7753768084856941773275549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5169178723237961182183699 7753768084856941773275549)
    ·
      refine ⟨2907663031821353164978331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7753768084856941773275549 2907663031821353164978331)
      ·
        refine ⟨4361494547732029747467497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2907663031821353164978331 4361494547732029747467497)
        ·
          refine ⟨3271120910799022310600623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4361494547732029747467497 3271120910799022310600623)
          ·
            refine ⟨4906681366198533465900935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3271120910799022310600623 4906681366198533465900935)
            ·
              refine ⟨7360022049297800198851403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4906681366198533465900935 7360022049297800198851403)
              ·
                refine ⟨11040033073946700298277105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7360022049297800198851403 11040033073946700298277105)
                ·
                  refine ⟨8280024805460025223707829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11040033073946700298277105 8280024805460025223707829)
                  ·
                    refine ⟨776252325511877364722609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8280024805460025223707829 776252325511877364722609)
                    ·
                      rfl

theorem cell23_4535238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_4535238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535238 prefixEnd_4535238 := by exact prefixLift 4535238
  have htrace : WordTrace (prefixWord ++ tailWord_4535238) baseStart_4535238 baseEnd_4535238 := by
    simpa [prefixWord, tailWord_4535238, baseEnd_4535238] using wordTrace_append hprefix tailTrace_4535238
  have hstable : (prefixWord ++ tailWord_4535238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535238).length < 2 ^ (prefixWord ++ tailWord_4535238).sum := by decide
  have hdescent : baseEnd_4535238 < baseStart_4535238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535257 : List Nat := [1, 2, 1, 2, 5, 1, 1, 5, 1, 1, 3]
def baseStart_4535257 : Nat := 118140960795 + 4535257 * 2 ^ 59
def prefixEnd_4535257 : Nat := 4983230072969 + 3 ^ 40 * 4535257 * 2
def baseEnd_4535257 : Nat := 2328766732668067519830239

theorem tailTrace_4535257 : CollatzResearch.WordTrace tailWord_4535257 prefixEnd_4535257 2328766732668067519830239 := by
  unfold tailWord_4535257
  simp only [CollatzResearch.WordTrace]
  refine ⟨165414412130545924074820025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110276274753697282716546683 165414412130545924074820025)
  ·
    refine ⟨124060809097909443056115019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165414412130545924074820025 124060809097909443056115019)
    ·
      refine ⟨186091213646864164584172529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124060809097909443056115019 186091213646864164584172529)
      ·
        refine ⟨139568410235148123438129397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186091213646864164584172529 139568410235148123438129397)
        ·
          refine ⟨13084538459545136572324631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139568410235148123438129397 13084538459545136572324631)
          ·
            refine ⟨19626807689317704858486947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13084538459545136572324631 19626807689317704858486947)
            ·
              refine ⟨29440211533976557287730421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19626807689317704858486947 29440211533976557287730421)
              ·
                refine ⟨2760019831310302245724727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29440211533976557287730421 2760019831310302245724727)
                ·
                  refine ⟨4140029746965453368587091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760019831310302245724727 4140029746965453368587091)
                  ·
                    refine ⟨6210044620448180052880637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4140029746965453368587091 6210044620448180052880637)
                    ·
                      refine ⟨2328766732668067519830239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6210044620448180052880637 2328766732668067519830239)
                      ·
                        rfl

theorem cell23_4535257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 5, 1, 1, 3].length) (baseStart_4535257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535257 prefixEnd_4535257 := by exact prefixLift 4535257
  have htrace : WordTrace (prefixWord ++ tailWord_4535257) baseStart_4535257 baseEnd_4535257 := by
    simpa [prefixWord, tailWord_4535257, baseEnd_4535257] using wordTrace_append hprefix tailTrace_4535257
  have hstable : (prefixWord ++ tailWord_4535257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535257).length < 2 ^ (prefixWord ++ tailWord_4535257).sum := by decide
  have hdescent : baseEnd_4535257 < baseStart_4535257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535276 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 4]
def baseStart_4535276 : Nat := 118140960795 + 4535276 * 2 ^ 59
def prefixEnd_4535276 : Nat := 4983230072969 + 3 ^ 40 * 4535276 * 2
def baseEnd_4535276 : Nat := 2328776488800502945492651

theorem tailTrace_4535276 : CollatzResearch.WordTrace tailWord_4535276 prefixEnd_4535276 2328776488800502945492651 := by
  unfold tailWord_4535276
  simp only [CollatzResearch.WordTrace]
  refine ⟨82707552558738545159880841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110276736744984726879841121 82707552558738545159880841)
  ·
    refine ⟨62030664419053908869910631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82707552558738545159880841 62030664419053908869910631)
    ·
      refine ⟨93045996628580863304865947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62030664419053908869910631 93045996628580863304865947)
      ·
        refine ⟨139568994942871294957298921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93045996628580863304865947 139568994942871294957298921)
        ·
          refine ⟨104676746207153471217974191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139568994942871294957298921 104676746207153471217974191)
          ·
            refine ⟨157015119310730206826961287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104676746207153471217974191 157015119310730206826961287)
            ·
              refine ⟨235522678966095310240441931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157015119310730206826961287 235522678966095310240441931)
              ·
                refine ⟨353284018449142965360662897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 235522678966095310240441931 353284018449142965360662897)
                ·
                  refine ⟨264963013836857224020497173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 353284018449142965360662897 264963013836857224020497173)
                  ·
                    refine ⟨12420141273602682375960805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 264963013836857224020497173 12420141273602682375960805)
                    ·
                      refine ⟨2328776488800502945492651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12420141273602682375960805 2328776488800502945492651)
                      ·
                        rfl

theorem cell23_4535276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 4].length) (baseStart_4535276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535276 prefixEnd_4535276 := by exact prefixLift 4535276
  have htrace : WordTrace (prefixWord ++ tailWord_4535276) baseStart_4535276 baseEnd_4535276 := by
    simpa [prefixWord, tailWord_4535276, baseEnd_4535276] using wordTrace_append hprefix tailTrace_4535276
  have hstable : (prefixWord ++ tailWord_4535276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535276).length < 2 ^ (prefixWord ++ tailWord_4535276).sum := by decide
  have hdescent : baseEnd_4535276 < baseStart_4535276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535297 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 3, 2, 2]
def baseStart_4535297 : Nat := 118140960795 + 4535297 * 2 ^ 59
def prefixEnd_4535297 : Nat := 4983230072969 + 3 ^ 40 * 4535297 * 2
def baseEnd_4535297 : Nat := 2328787271894247363330055

theorem tailTrace_4535297 : CollatzResearch.WordTrace tailWord_4535297 prefixEnd_4535297 2328787271894247363330055 := by
  unfold tailWord_4535297
  simp only [CollatzResearch.WordTrace]
  refine ⟨165415871050401010906276145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110277247366934007270850763 165415871050401010906276145)
  ·
    refine ⟨124061903287800758179707109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165415871050401010906276145 124061903287800758179707109)
    ·
      refine ⟨23261606866462642158695083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124061903287800758179707109 23261606866462642158695083)
      ·
        refine ⟨34892410299693963238042625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23261606866462642158695083 34892410299693963238042625)
        ·
          refine ⟨26169307724770472428531969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34892410299693963238042625 26169307724770472428531969)
          ·
            refine ⟨19626980793577854321398977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26169307724770472428531969 19626980793577854321398977)
            ·
              refine ⟨14720235595183390741049233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19626980793577854321398977 14720235595183390741049233)
              ·
                refine ⟨11040176696387543055786925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14720235595183390741049233 11040176696387543055786925)
                ·
                  refine ⟨4140066261145328645920097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11040176696387543055786925 4140066261145328645920097)
                  ·
                    refine ⟨3105049695858996484440073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4140066261145328645920097 3105049695858996484440073)
                    ·
                      refine ⟨2328787271894247363330055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105049695858996484440073 2328787271894247363330055)
                      ·
                        rfl

theorem cell23_4535297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_4535297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535297 prefixEnd_4535297 := by exact prefixLift 4535297
  have htrace : WordTrace (prefixWord ++ tailWord_4535297) baseStart_4535297 baseEnd_4535297 := by
    simpa [prefixWord, tailWord_4535297, baseEnd_4535297] using wordTrace_append hprefix tailTrace_4535297
  have hstable : (prefixWord ++ tailWord_4535297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535297).length < 2 ^ (prefixWord ++ tailWord_4535297).sum := by decide
  have hdescent : baseEnd_4535297 < baseStart_4535297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535313 : List Nat := [1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 3]
def baseStart_4535313 : Nat := 118140960795 + 4535313 * 2 ^ 59
def prefixEnd_4535313 : Nat := 4983230072969 + 3 ^ 40 * 4535313 * 2
def baseEnd_4535313 : Nat := 2328795487584719300729981

theorem tailTrace_4535313 : CollatzResearch.WordTrace tailWord_4535313 prefixEnd_4535313 2328795487584719300729981 := by
  unfold tailWord_4535313
  simp only [CollatzResearch.WordTrace]
  refine ⟨165416454618343045638858593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110277636412228697092572395 165416454618343045638858593)
  ·
    refine ⟨124062340963757284229143945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165416454618343045638858593 124062340963757284229143945)
    ·
      refine ⟨93046755722817963171857959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124062340963757284229143945 93046755722817963171857959)
      ·
        refine ⟨139570133584226944757786939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93046755722817963171857959 139570133584226944757786939)
        ·
          refine ⟨209355200376340417136680409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139570133584226944757786939 209355200376340417136680409)
          ·
            refine ⟨157016400282255312852510307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209355200376340417136680409 157016400282255312852510307)
            ·
              refine ⟨235524600423382969278765461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157016400282255312852510307 235524600423382969278765461)
              ·
                refine ⟨11040215644846076684942131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 235524600423382969278765461 11040215644846076684942131)
                ·
                  refine ⟨16560323467269115027413197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11040215644846076684942131 16560323467269115027413197)
                  ·
                    refine ⟨6210121300225918135279949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16560323467269115027413197 6210121300225918135279949)
                    ·
                      refine ⟨2328795487584719300729981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6210121300225918135279949 2328795487584719300729981)
                      ·
                        rfl

theorem cell23_4535313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 3].length) (baseStart_4535313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535313 prefixEnd_4535313 := by exact prefixLift 4535313
  have htrace : WordTrace (prefixWord ++ tailWord_4535313) baseStart_4535313 baseEnd_4535313 := by
    simpa [prefixWord, tailWord_4535313, baseEnd_4535313] using wordTrace_append hprefix tailTrace_4535313
  have hstable : (prefixWord ++ tailWord_4535313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535313).length < 2 ^ (prefixWord ++ tailWord_4535313).sum := by decide
  have hdescent : baseEnd_4535313 < baseStart_4535313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535323 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 1, 9, 2]
def baseStart_4535323 : Nat := 118140960795 + 4535323 * 2 ^ 59
def prefixEnd_4535323 : Nat := 4983230072969 + 3 ^ 40 * 4535323 * 2
def baseEnd_4535323 : Nat := 2328800622391264261604935

theorem tailTrace_4535323 : CollatzResearch.WordTrace tailWord_4535323 prefixEnd_4535323 2328800622391264261604935 := by
  unfold tailWord_4535323
  simp only [CollatzResearch.WordTrace]
  refine ⟨165416819348306817346722623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110277879565537878231148415 165416819348306817346722623)
  ·
    refine ⟨248125229022460226020083935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165416819348306817346722623 248125229022460226020083935)
    ·
      refine ⟨372187843533690339030125903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248125229022460226020083935 372187843533690339030125903)
      ·
        refine ⟨558281765300535508545188855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372187843533690339030125903 558281765300535508545188855)
        ·
          refine ⟨837422647950803262817783283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558281765300535508545188855 837422647950803262817783283)
          ·
            refine ⟨1256133971926204894226674925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 837422647950803262817783283 1256133971926204894226674925)
            ·
              refine ⟨471050239472326835335003097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1256133971926204894226674925 471050239472326835335003097)
              ·
                refine ⟨353287679604245126501252323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 471050239472326835335003097 353287679604245126501252323)
                ·
                  refine ⟨529931519406367689751878485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 353287679604245126501252323 529931519406367689751878485)
                  ·
                    refine ⟨3105067496521685682139913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 529931519406367689751878485 3105067496521685682139913)
                    ·
                      refine ⟨2328800622391264261604935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105067496521685682139913 2328800622391264261604935)
                      ·
                        rfl

theorem cell23_4535323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 9, 2].length) (baseStart_4535323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535323 prefixEnd_4535323 := by exact prefixLift 4535323
  have htrace : WordTrace (prefixWord ++ tailWord_4535323) baseStart_4535323 baseEnd_4535323 := by
    simpa [prefixWord, tailWord_4535323, baseEnd_4535323] using wordTrace_append hprefix tailTrace_4535323
  have hstable : (prefixWord ++ tailWord_4535323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535323).length < 2 ^ (prefixWord ++ tailWord_4535323).sum := by decide
  have hdescent : baseEnd_4535323 < baseStart_4535323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535331 : List Nat := [1, 1, 1, 4, 3, 3, 3, 2, 1, 2, 2]
def baseStart_4535331 : Nat := 118140960795 + 4535331 * 2 ^ 59
def prefixEnd_4535331 : Nat := 4983230072969 + 3 ^ 40 * 4535331 * 2
def baseEnd_4535331 : Nat := 2328804730236500230304899

theorem tailTrace_4535331 : CollatzResearch.WordTrace tailWord_4535331 prefixEnd_4535331 2328804730236500230304899 := by
  unfold tailWord_4535331
  simp only [CollatzResearch.WordTrace]
  refine ⟨165417111132277834713013847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110278074088185223142009231 165417111132277834713013847)
  ·
    refine ⟨248125666698416752069520771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165417111132277834713013847 248125666698416752069520771)
    ·
      refine ⟨372188500047625128104281157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248125666698416752069520771 372188500047625128104281157)
      ·
        refine ⟨69785343758929711519552717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 372188500047625128104281157 69785343758929711519552717)
        ·
          refine ⟨26169503909598641819832269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69785343758929711519552717 26169503909598641819832269)
          ·
            refine ⟨9813563966099490682437101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26169503909598641819832269 9813563966099490682437101)
            ·
              refine ⟨3680086487287309005913913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9813563966099490682437101 3680086487287309005913913)
              ·
                refine ⟨2760064865465481754435435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3680086487287309005913913 2760064865465481754435435)
                ·
                  refine ⟨4140097298198222631653153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760064865465481754435435 4140097298198222631653153)
                  ·
                    refine ⟨3105072973648666973739865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4140097298198222631653153 3105072973648666973739865)
                    ·
                      refine ⟨2328804730236500230304899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105072973648666973739865 2328804730236500230304899)
                      ·
                        rfl

theorem cell23_4535331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_4535331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535331 prefixEnd_4535331 := by exact prefixLift 4535331
  have htrace : WordTrace (prefixWord ++ tailWord_4535331) baseStart_4535331 baseEnd_4535331 := by
    simpa [prefixWord, tailWord_4535331, baseEnd_4535331] using wordTrace_append hprefix tailTrace_4535331
  have hstable : (prefixWord ++ tailWord_4535331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535331).length < 2 ^ (prefixWord ++ tailWord_4535331).sum := by decide
  have hdescent : baseEnd_4535331 < baseStart_4535331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535340 : List Nat := [2, 2, 1, 1, 1, 2, 4, 2, 3, 3, 2]
def baseStart_4535340 : Nat := 118140960795 + 4535340 * 2 ^ 59
def prefixEnd_4535340 : Nat := 4983230072969 + 3 ^ 40 * 4535340 * 2
def baseEnd_4535340 : Nat := 2328809351562390695092357

theorem tailTrace_4535340 : CollatzResearch.WordTrace tailWord_4535340 prefixEnd_4535340 2328809351562390695092357 := by
  unfold tailWord_4535340
  simp only [CollatzResearch.WordTrace]
  refine ⟨82708719694622614625045737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110278292926163486166727649 82708719694622614625045737)
  ·
    refine ⟨62031539770966960968784303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82708719694622614625045737 62031539770966960968784303)
    ·
      refine ⟨93047309656450441453176455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62031539770966960968784303 93047309656450441453176455)
      ·
        refine ⟨139570964484675662179764683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93047309656450441453176455 139570964484675662179764683)
        ·
          refine ⟨209356446727013493269647025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139570964484675662179764683 209356446727013493269647025)
          ·
            refine ⟨157017335045260119952235269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209356446727013493269647025 157017335045260119952235269)
            ·
              refine ⟨29440750320986272491044113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157017335045260119952235269 29440750320986272491044113)
              ·
                refine ⟨22080562740739704368283085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29440750320986272491044113 22080562740739704368283085)
                ·
                  refine ⟨8280211027777389138106157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22080562740739704368283085 8280211027777389138106157)
                  ·
                    refine ⟨3105079135416520926789809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8280211027777389138106157 3105079135416520926789809)
                    ·
                      refine ⟨2328809351562390695092357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105079135416520926789809 2328809351562390695092357)
                      ·
                        rfl

theorem cell23_4535340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 3, 2].length) (baseStart_4535340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535340 prefixEnd_4535340 := by exact prefixLift 4535340
  have htrace : WordTrace (prefixWord ++ tailWord_4535340) baseStart_4535340 baseEnd_4535340 := by
    simpa [prefixWord, tailWord_4535340, baseEnd_4535340] using wordTrace_append hprefix tailTrace_4535340
  have hstable : (prefixWord ++ tailWord_4535340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535340).length < 2 ^ (prefixWord ++ tailWord_4535340).sum := by decide
  have hdescent : baseEnd_4535340 < baseStart_4535340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535357 : List Nat := [1, 4, 1, 3, 1, 3, 1, 1, 3, 3, 2]
def baseStart_4535357 : Nat := 118140960795 + 4535357 * 2 ^ 59
def prefixEnd_4535357 : Nat := 4983230072969 + 3 ^ 40 * 4535357 * 2
def baseEnd_4535357 : Nat := 2328818080733517128579779

theorem tailTrace_4535357 : CollatzResearch.WordTrace tailWord_4535357 prefixEnd_4535357 2328818080733517128579779 := by
  unfold tailWord_4535357
  simp only [CollatzResearch.WordTrace]
  refine ⟨165418059430183641153460325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110278706286789094102306883 165418059430183641153460325)
  ·
    refine ⟨31015886143159432716273811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165418059430183641153460325 31015886143159432716273811)
    ·
      refine ⟨46523829214739149074410717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31015886143159432716273811 46523829214739149074410717)
      ·
        refine ⟨17446435955527180902904019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46523829214739149074410717 17446435955527180902904019)
        ·
          refine ⟨26169653933290771354356029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17446435955527180902904019 26169653933290771354356029)
          ·
            refine ⟨9813620224984039257883511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26169653933290771354356029 9813620224984039257883511)
            ·
              refine ⟨14720430337476058886825267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9813620224984039257883511 14720430337476058886825267)
              ·
                refine ⟨22080645506214088330237901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14720430337476058886825267 22080645506214088330237901)
                ·
                  refine ⟨8280242064830283123839213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22080645506214088330237901 8280242064830283123839213)
                  ·
                    refine ⟨3105090774311356171439705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8280242064830283123839213 3105090774311356171439705)
                    ·
                      refine ⟨2328818080733517128579779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105090774311356171439705 2328818080733517128579779)
                      ·
                        rfl

theorem cell23_4535357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 1, 1, 3, 3, 2].length) (baseStart_4535357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535357 prefixEnd_4535357 := by exact prefixLift 4535357
  have htrace : WordTrace (prefixWord ++ tailWord_4535357) baseStart_4535357 baseEnd_4535357 := by
    simpa [prefixWord, tailWord_4535357, baseEnd_4535357] using wordTrace_append hprefix tailTrace_4535357
  have hstable : (prefixWord ++ tailWord_4535357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535357).length < 2 ^ (prefixWord ++ tailWord_4535357).sum := by decide
  have hdescent : baseEnd_4535357 < baseStart_4535357 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535370 : List Nat := [3, 1, 2, 1, 1, 2, 3, 1, 3, 4, 2]
def baseStart_4535370 : Nat := 118140960795 + 4535370 * 2 ^ 59
def prefixEnd_4535370 : Nat := 4983230072969 + 3 ^ 40 * 4535370 * 2
def baseEnd_4535370 : Nat := 2328824755982025577717219

theorem tailTrace_4535370 : CollatzResearch.WordTrace tailWord_4535370 prefixEnd_4535370 2328824755982025577717219 := by
  unfold tailWord_4535370
  simp only [CollatzResearch.WordTrace]
  refine ⟨41354633394784136093420891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110279022386091029582455709 41354633394784136093420891)
  ·
    refine ⟨62031950092176204140131337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41354633394784136093420891 62031950092176204140131337)
    ·
      refine ⟨46523962569132153105098503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62031950092176204140131337 46523962569132153105098503)
      ·
        refine ⟨69785943853698229657647755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46523962569132153105098503 69785943853698229657647755)
        ·
          refine ⟨104678915780547344486471633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69785943853698229657647755 104678915780547344486471633)
          ·
            refine ⟨78509186835410508364853725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104678915780547344486471633 78509186835410508364853725)
            ·
              refine ⟨29440945063278940636820147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78509186835410508364853725 29440945063278940636820147)
              ·
                refine ⟨44161417594918410955230221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29440945063278940636820147 44161417594918410955230221)
                ·
                  refine ⟨16560531598094404108211333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44161417594918410955230221 16560531598094404108211333)
                  ·
                    refine ⟨3105099674642700770289625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16560531598094404108211333 3105099674642700770289625)
                    ·
                      refine ⟨2328824755982025577717219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105099674642700770289625 2328824755982025577717219)
                      ·
                        rfl

theorem cell23_4535370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_4535370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535370 prefixEnd_4535370 := by exact prefixLift 4535370
  have htrace : WordTrace (prefixWord ++ tailWord_4535370) baseStart_4535370 baseEnd_4535370 := by
    simpa [prefixWord, tailWord_4535370, baseEnd_4535370] using wordTrace_append hprefix tailTrace_4535370
  have hstable : (prefixWord ++ tailWord_4535370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535370).length < 2 ^ (prefixWord ++ tailWord_4535370).sum := by decide
  have hdescent : baseEnd_4535370 < baseStart_4535370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535374 : List Nat := [4, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2]
def baseStart_4535374 : Nat := 118140960795 + 4535374 * 2 ^ 59
def prefixEnd_4535374 : Nat := 4983230072969 + 3 ^ 40 * 4535374 * 2
def baseEnd_4535374 : Nat := 2328826809904643562067201

theorem tailTrace_4535374 : CollatzResearch.WordTrace tailWord_4535374 prefixEnd_4535374 2328826809904643562067201 := by
  unfold tailWord_4535374
  simp only [CollatzResearch.WordTrace]
  refine ⟨20677334933890256632103647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110279119647414702037886117 20677334933890256632103647)
  ·
    refine ⟨31016002400835384948155471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20677334933890256632103647 31016002400835384948155471)
    ·
      refine ⟨46524003601253077422233207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31016002400835384948155471 46524003601253077422233207)
      ·
        refine ⟨69786005401879616133349811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46524003601253077422233207 69786005401879616133349811)
        ·
          refine ⟨104679008102819424200024717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69786005401879616133349811 104679008102819424200024717)
          ·
            refine ⟨39254628038557284075009269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104679008102819424200024717 39254628038557284075009269)
            ·
              refine ⟨3680121378614745382032119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39254628038557284075009269 3680121378614745382032119)
              ·
                refine ⟨5520182067922118073048179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3680121378614745382032119 5520182067922118073048179)
                ·
                  refine ⟨8280273101883177109572269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5520182067922118073048179 8280273101883177109572269)
                  ·
                    refine ⟨3105102413206191416089601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8280273101883177109572269 3105102413206191416089601)
                    ·
                      refine ⟨2328826809904643562067201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105102413206191416089601 2328826809904643562067201)
                      ·
                        rfl

theorem cell23_4535374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 1, 3, 2].length) (baseStart_4535374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535374 prefixEnd_4535374 := by exact prefixLift 4535374
  have htrace : WordTrace (prefixWord ++ tailWord_4535374) baseStart_4535374 baseEnd_4535374 := by
    simpa [prefixWord, tailWord_4535374, baseEnd_4535374] using wordTrace_append hprefix tailTrace_4535374
  have hstable : (prefixWord ++ tailWord_4535374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535374).length < 2 ^ (prefixWord ++ tailWord_4535374).sum := by decide
  have hdescent : baseEnd_4535374 < baseStart_4535374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535382 : List Nat := [5, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_4535382 : Nat := 118140960795 + 4535382 * 2 ^ 59
def prefixEnd_4535382 : Nat := 4983230072969 + 3 ^ 40 * 4535382 * 2
def baseEnd_4535382 : Nat := 2328830917749879530767165

theorem tailTrace_4535382 : CollatzResearch.WordTrace tailWord_4535382 prefixEnd_4535382 2328830917749879530767165 := by
  unfold tailWord_4535382
  simp only [CollatzResearch.WordTrace]
  refine ⟨10338685703443316901445025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110279314170062046948746933 10338685703443316901445025)
  ·
    refine ⟨7754014277582487676083769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10338685703443316901445025 7754014277582487676083769)
    ·
      refine ⟨5815510708186865757062827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7754014277582487676083769 5815510708186865757062827)
      ·
        refine ⟨8723266062280298635594241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5815510708186865757062827 8723266062280298635594241)
        ·
          refine ⟨6542449546710223976695681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8723266062280298635594241 6542449546710223976695681)
          ·
            refine ⟨4906837160032667982521761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6542449546710223976695681 4906837160032667982521761)
            ·
              refine ⟨3680127870024500986891321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4906837160032667982521761 3680127870024500986891321)
              ·
                refine ⟨2760095902518375740168491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3680127870024500986891321 2760095902518375740168491)
                ·
                  refine ⟨4140143853777563610252737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760095902518375740168491 4140143853777563610252737)
                  ·
                    refine ⟨3105107890333172707689553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4140143853777563610252737 3105107890333172707689553)
                    ·
                      refine ⟨2328830917749879530767165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105107890333172707689553 2328830917749879530767165)
                      ·
                        rfl

theorem cell23_4535382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_4535382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535382 prefixEnd_4535382 := by exact prefixLift 4535382
  have htrace : WordTrace (prefixWord ++ tailWord_4535382) baseStart_4535382 baseEnd_4535382 := by
    simpa [prefixWord, tailWord_4535382, baseEnd_4535382] using wordTrace_append hprefix tailTrace_4535382
  have hstable : (prefixWord ++ tailWord_4535382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535382).length < 2 ^ (prefixWord ++ tailWord_4535382).sum := by decide
  have hdescent : baseEnd_4535382 < baseStart_4535382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535383 : List Nat := [1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 4]
def baseStart_4535383 : Nat := 118140960795 + 4535383 * 2 ^ 59
def prefixEnd_4535383 : Nat := 4983230072969 + 3 ^ 40 * 4535383 * 2
def baseEnd_4535383 : Nat := 2328831431230534026854659

theorem tailTrace_4535383 : CollatzResearch.WordTrace tailWord_4535383 prefixEnd_4535383 2328831431230534026854659 := by
  unfold tailWord_4535383
  simp only [CollatzResearch.WordTrace]
  refine ⟨165419007728089447593906803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110279338485392965062604535 165419007728089447593906803)
  ·
    refine ⟨248128511592134171390860205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165419007728089447593906803 248128511592134171390860205)
    ·
      refine ⟨93048191847050314271572577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 248128511592134171390860205 93048191847050314271572577)
      ·
        refine ⟨69786143885287735703679433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93048191847050314271572577 69786143885287735703679433)
        ·
          refine ⟨52339607913965801777759575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69786143885287735703679433 52339607913965801777759575)
          ·
            refine ⟨78509411870948702666639363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52339607913965801777759575 78509411870948702666639363)
            ·
              refine ⟨117764117806423053999959045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78509411870948702666639363 117764117806423053999959045)
              ·
                refine ⟨22080772088704322624992321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117764117806423053999959045 22080772088704322624992321)
                ·
                  refine ⟨16560579066528241968744241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22080772088704322624992321 16560579066528241968744241)
                  ·
                    refine ⟨12420434299896181476558181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16560579066528241968744241 12420434299896181476558181)
                    ·
                      refine ⟨2328831431230534026854659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12420434299896181476558181 2328831431230534026854659)
                      ·
                        rfl

theorem cell23_4535383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 4, 2, 2, 4].length) (baseStart_4535383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535383 prefixEnd_4535383 := by exact prefixLift 4535383
  have htrace : WordTrace (prefixWord ++ tailWord_4535383) baseStart_4535383 baseEnd_4535383 := by
    simpa [prefixWord, tailWord_4535383, baseEnd_4535383] using wordTrace_append hprefix tailTrace_4535383
  have hstable : (prefixWord ++ tailWord_4535383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535383).length < 2 ^ (prefixWord ++ tailWord_4535383).sum := by decide
  have hdescent : baseEnd_4535383 < baseStart_4535383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535460 : List Nat := [2, 3, 1, 2, 3, 1, 1, 2, 1, 3, 4]
def baseStart_4535460 : Nat := 118140960795 + 4535460 * 2 ^ 59
def prefixEnd_4535460 : Nat := 4983230072969 + 3 ^ 40 * 4535460 * 2
def baseEnd_4535460 : Nat := 2328870969240930225591805

theorem tailTrace_4535460 : CollatzResearch.WordTrace tailWord_4535460 prefixEnd_4535460 2328870969240930225591805 := by
  unfold tailWord_4535460
  simp only [CollatzResearch.WordTrace]
  refine ⟨82710908074405244872229917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110281210765873659829639889 82710908074405244872229917)
  ·
    refine ⟨31016590527901966827086219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82710908074405244872229917 31016590527901966827086219)
    ·
      refine ⟨46524885791852950240629329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31016590527901966827086219 46524885791852950240629329)
      ·
        refine ⟨34893664343889712680471997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46524885791852950240629329 34893664343889712680471997)
        ·
          refine ⟨13085124128958642255176999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34893664343889712680471997 13085124128958642255176999)
          ·
            refine ⟨19627686193437963382765499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13085124128958642255176999 19627686193437963382765499)
            ·
              refine ⟨29441529290156945074148249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19627686193437963382765499 29441529290156945074148249)
              ·
                refine ⟨22081146967617708805611187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29441529290156945074148249 22081146967617708805611187)
                ·
                  refine ⟨33121720451426563208416781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22081146967617708805611187 33121720451426563208416781)
                  ·
                    refine ⟨12420645169284961203156293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33121720451426563208416781 12420645169284961203156293)
                    ·
                      refine ⟨2328870969240930225591805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12420645169284961203156293 2328870969240930225591805)
                      ·
                        rfl

theorem cell23_4535460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_4535460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535460 prefixEnd_4535460 := by exact prefixLift 4535460
  have htrace : WordTrace (prefixWord ++ tailWord_4535460) baseStart_4535460 baseEnd_4535460 := by
    simpa [prefixWord, tailWord_4535460, baseEnd_4535460] using wordTrace_append hprefix tailTrace_4535460
  have hstable : (prefixWord ++ tailWord_4535460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535460).length < 2 ^ (prefixWord ++ tailWord_4535460).sum := by decide
  have hdescent : baseEnd_4535460 < baseStart_4535460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535478 : List Nat := [5, 1, 3, 2, 1, 2, 1, 3, 5]
def baseStart_4535478 : Nat := 118140960795 + 4535478 * 2 ^ 59
def prefixEnd_4535478 : Nat := 4983230072969 + 3 ^ 40 * 4535478 * 2
def baseEnd_4535478 : Nat := 258764467988079017240747

theorem tailTrace_4535478 : CollatzResearch.WordTrace tailWord_4535478 prefixEnd_4535478 258764467988079017240747 := by
  unfold tailWord_4535478
  simp only [CollatzResearch.WordTrace]
  refine ⟨10338904541421579926163443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 110281648441830185879076725 10338904541421579926163443)
  ·
    refine ⟨15508356812132369889245165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10338904541421579926163443 15508356812132369889245165)
    ·
      refine ⟨5815633804549638708466937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15508356812132369889245165 5815633804549638708466937)
      ·
        refine ⟨4361725353412229031350203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5815633804549638708466937 4361725353412229031350203)
        ·
          refine ⟨6542588030118343547025305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4361725353412229031350203 6542588030118343547025305)
          ·
            refine ⟨4906941022588757660268979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6542588030118343547025305 4906941022588757660268979)
            ·
              refine ⟨7360411533883136490403469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4906941022588757660268979 7360411533883136490403469)
              ·
                refine ⟨2760154325206176183901301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7360411533883136490403469 2760154325206176183901301)
                ·
                  refine ⟨258764467988079017240747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2760154325206176183901301 258764467988079017240747)
                  ·
                    rfl

theorem cell23_4535478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_4535478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535478 prefixEnd_4535478 := by exact prefixLift 4535478
  have htrace : WordTrace (prefixWord ++ tailWord_4535478) baseStart_4535478 baseEnd_4535478 := by
    simpa [prefixWord, tailWord_4535478, baseEnd_4535478] using wordTrace_append hprefix tailTrace_4535478
  have hstable : (prefixWord ++ tailWord_4535478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535478).length < 2 ^ (prefixWord ++ tailWord_4535478).sum := by decide
  have hdescent : baseEnd_4535478 < baseStart_4535478 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535503 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 6]
def baseStart_4535503 : Nat := 118140960795 + 4535503 * 2 ^ 59
def prefixEnd_4535503 : Nat := 4983230072969 + 3 ^ 40 * 4535503 * 2
def baseEnd_4535503 : Nat := 2328893048909073557354107

theorem tailTrace_4535503 : CollatzResearch.WordTrace tailWord_4535503 prefixEnd_4535503 2328893048909073557354107 := by
  unfold tailWord_4535503
  simp only [CollatzResearch.WordTrace]
  refine ⟨165423384487654708088275163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110282256325103138725516775 165423384487654708088275163)
  ·
    refine ⟨248135076731482062132412745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165423384487654708088275163 248135076731482062132412745)
    ·
      refine ⟨186101307548611546599309559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248135076731482062132412745 186101307548611546599309559)
      ·
        refine ⟨279151961322917319898964339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186101307548611546599309559 279151961322917319898964339)
        ·
          refine ⟨418727941984375979848446509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279151961322917319898964339 418727941984375979848446509)
          ·
            refine ⟨157022978244140992443167441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 418727941984375979848446509 157022978244140992443167441)
            ·
              refine ⟨117767233683105744332375581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157022978244140992443167441 117767233683105744332375581)
              ·
                refine ⟨44162712631164654124640843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117767233683105744332375581 44162712631164654124640843)
                ·
                  refine ⟨66244068946746981186961265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44162712631164654124640843 66244068946746981186961265)
                  ·
                    refine ⟨49683051710060235890220949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66244068946746981186961265 49683051710060235890220949)
                    ·
                      refine ⟨2328893048909073557354107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49683051710060235890220949 2328893048909073557354107)
                      ·
                        rfl

theorem cell23_4535503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 1, 2, 6].length) (baseStart_4535503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535503 prefixEnd_4535503 := by exact prefixLift 4535503
  have htrace : WordTrace (prefixWord ++ tailWord_4535503) baseStart_4535503 baseEnd_4535503 := by
    simpa [prefixWord, tailWord_4535503, baseEnd_4535503] using wordTrace_append hprefix tailTrace_4535503
  have hstable : (prefixWord ++ tailWord_4535503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535503).length < 2 ^ (prefixWord ++ tailWord_4535503).sum := by decide
  have hdescent : baseEnd_4535503 < baseStart_4535503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535513 : List Nat := [1, 2, 1, 2, 3, 1, 1, 1, 2, 9]
def baseStart_4535513 : Nat := 118140960795 + 4535513 * 2 ^ 59
def prefixEnd_4535513 : Nat := 4983230072969 + 3 ^ 40 * 4535513 * 2
def baseEnd_4535513 : Nat := 776299394571872839409687

theorem tailTrace_4535513 : CollatzResearch.WordTrace tailWord_4535513 prefixEnd_4535513 776299394571872839409687 := by
  unfold tailWord_4535513
  simp only [CollatzResearch.WordTrace]
  refine ⟨165423749217618479796139193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110282499478412319864092795 165423749217618479796139193)
  ·
    refine ⟨124067811913213859847104395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165423749217618479796139193 124067811913213859847104395)
    ·
      refine ⟨186101717869820789770656593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124067811913213859847104395 186101717869820789770656593)
      ·
        refine ⟨139576288402365592327992445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186101717869820789770656593 139576288402365592327992445)
        ·
          refine ⟨52341108150887097122997167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139576288402365592327992445 52341108150887097122997167)
          ·
            refine ⟨78511662226330645684495751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52341108150887097122997167 78511662226330645684495751)
            ·
              refine ⟨117767493339495968526743627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78511662226330645684495751 117767493339495968526743627)
              ·
                refine ⟨176651240009243952790115441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117767493339495968526743627 176651240009243952790115441)
                ·
                  refine ⟨132488430006932964592586581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176651240009243952790115441 132488430006932964592586581)
                  ·
                    refine ⟨776299394571872839409687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 132488430006932964592586581 776299394571872839409687)
                    ·
                      rfl

theorem cell23_4535513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 2, 9].length) (baseStart_4535513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535513 prefixEnd_4535513 := by exact prefixLift 4535513
  have htrace : WordTrace (prefixWord ++ tailWord_4535513) baseStart_4535513 baseEnd_4535513 := by
    simpa [prefixWord, tailWord_4535513, baseEnd_4535513] using wordTrace_append hprefix tailTrace_4535513
  have hstable : (prefixWord ++ tailWord_4535513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535513).length < 2 ^ (prefixWord ++ tailWord_4535513).sum := by decide
  have hdescent : baseEnd_4535513 < baseStart_4535513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535580 : List Nat := [2, 2, 3, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_4535580 : Nat := 118140960795 + 4535580 * 2 ^ 59
def prefixEnd_4535580 : Nat := 4983230072969 + 3 ^ 40 * 4535580 * 2
def baseEnd_4535580 : Nat := 2328932586919469756091253

theorem tailTrace_4535580 : CollatzResearch.WordTrace tailWord_4535580 prefixEnd_4535580 2328932586919469756091253 := by
  unfold tailWord_4535580
  simp only [CollatzResearch.WordTrace]
  refine ⟨82713096454187875119414097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110284128605583833492552129 82713096454187875119414097)
  ·
    refine ⟨62034822340640906339560573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82713096454187875119414097 62034822340640906339560573)
    ·
      refine ⟨23263058377740339877335215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62034822340640906339560573 23263058377740339877335215)
      ·
        refine ⟨34894587566610509816002823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23263058377740339877335215 34894587566610509816002823)
        ·
          refine ⟨52341881349915764724004235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34894587566610509816002823 52341881349915764724004235)
          ·
            refine ⟨78512822024873647086006353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52341881349915764724004235 78512822024873647086006353)
            ·
              refine ⟨58884616518655235314504765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78512822024873647086006353 58884616518655235314504765)
              ·
                refine ⟨22081731194495713242939287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58884616518655235314504765 22081731194495713242939287)
                ·
                  refine ⟨33122596791743569864408931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22081731194495713242939287 33122596791743569864408931)
                  ·
                    refine ⟨49683895187615354796613397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33122596791743569864408931 49683895187615354796613397)
                    ·
                      refine ⟨2328932586919469756091253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49683895187615354796613397 2328932586919469756091253)
                      ·
                        rfl

theorem cell23_4535580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_4535580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535580 prefixEnd_4535580 := by exact prefixLift 4535580
  have htrace : WordTrace (prefixWord ++ tailWord_4535580) baseStart_4535580 baseEnd_4535580 := by
    simpa [prefixWord, tailWord_4535580, baseEnd_4535580] using wordTrace_append hprefix tailTrace_4535580
  have hstable : (prefixWord ++ tailWord_4535580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535580).length < 2 ^ (prefixWord ++ tailWord_4535580).sum := by decide
  have hdescent : baseEnd_4535580 < baseStart_4535580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535587 : List Nat := [1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 3]
def baseStart_4535587 : Nat := 118140960795 + 4535587 * 2 ^ 59
def prefixEnd_4535587 : Nat := 4983230072969 + 3 ^ 40 * 4535587 * 2
def baseEnd_4535587 : Nat := 2328936181284051228703721

theorem tailTrace_4535587 : CollatzResearch.WordTrace tailWord_4535587 prefixEnd_4535587 2328936181284051228703721 := by
  unfold tailWord_4535587
  simp only [CollatzResearch.WordTrace]
  refine ⟨165426448219350390434333015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110284298812900260289555343 165426448219350390434333015)
  ·
    refine ⟨248139672329025585651499523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165426448219350390434333015 248139672329025585651499523)
    ·
      refine ⟨372209508493538378477249285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248139672329025585651499523 372209508493538378477249285)
      ·
        refine ⟨69789282842538445964484241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 372209508493538378477249285 69789282842538445964484241)
        ·
          refine ⟨52341962131903834473363181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69789282842538445964484241 52341962131903834473363181)
          ·
            refine ⟨19628235799463937927511193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52341962131903834473363181 19628235799463937927511193)
            ·
              refine ⟨14721176849597953445633395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19628235799463937927511193 14721176849597953445633395)
              ·
                refine ⟨22081765274396930168450093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14721176849597953445633395 22081765274396930168450093)
                ·
                  refine ⟨8280661977898848813168785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22081765274396930168450093 8280661977898848813168785)
                  ·
                    refine ⟨6210496483424136609876589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8280661977898848813168785 6210496483424136609876589)
                    ·
                      refine ⟨2328936181284051228703721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6210496483424136609876589 2328936181284051228703721)
                      ·
                        rfl

theorem cell23_4535587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_4535587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535587 prefixEnd_4535587 := by exact prefixLift 4535587
  have htrace : WordTrace (prefixWord ++ tailWord_4535587) baseStart_4535587 baseEnd_4535587 := by
    simpa [prefixWord, tailWord_4535587, baseEnd_4535587] using wordTrace_append hprefix tailTrace_4535587
  have hstable : (prefixWord ++ tailWord_4535587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535587).length < 2 ^ (prefixWord ++ tailWord_4535587).sum := by decide
  have hdescent : baseEnd_4535587 < baseStart_4535587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535601 : List Nat := [1, 2, 2, 3, 3, 3, 2, 1, 1, 1, 4]
def baseStart_4535601 : Nat := 118140960795 + 4535601 * 2 ^ 59
def prefixEnd_4535601 : Nat := 4983230072969 + 3 ^ 40 * 4535601 * 2
def baseEnd_4535601 : Nat := 2328943370013214173928657

theorem tailTrace_4535601 : CollatzResearch.WordTrace tailWord_4535601 prefixEnd_4535601 2328943370013214173928657 := by
  unfold tailWord_4535601
  simp only [CollatzResearch.WordTrace]
  refine ⟨165426958841299670825342657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110284639227533113883561771 165426958841299670825342657)
  ·
    refine ⟨124070219130974753119006993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165426958841299670825342657 124070219130974753119006993)
    ·
      refine ⟨93052664348231064839255245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124070219130974753119006993 93052664348231064839255245)
      ·
        refine ⟨34894749130586649314720717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93052664348231064839255245 34894749130586649314720717)
        ·
          refine ⟨13085530923969993493020269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34894749130586649314720717 13085530923969993493020269)
          ·
            refine ⟨4907074096488747559882601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13085530923969993493020269 4907074096488747559882601)
            ·
              refine ⟨3680305572366560669911951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4907074096488747559882601 3680305572366560669911951)
              ·
                refine ⟨5520458358549841004867927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3680305572366560669911951 5520458358549841004867927)
                ·
                  refine ⟨8280687537824761507301891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5520458358549841004867927 8280687537824761507301891)
                  ·
                    refine ⟨12421031306737142260952837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8280687537824761507301891 12421031306737142260952837)
                    ·
                      refine ⟨2328943370013214173928657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12421031306737142260952837 2328943370013214173928657)
                      ·
                        rfl

theorem cell23_4535601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_4535601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535601 prefixEnd_4535601 := by exact prefixLift 4535601
  have htrace : WordTrace (prefixWord ++ tailWord_4535601) baseStart_4535601 baseEnd_4535601 := by
    simpa [prefixWord, tailWord_4535601, baseEnd_4535601] using wordTrace_append hprefix tailTrace_4535601
  have hstable : (prefixWord ++ tailWord_4535601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535601).length < 2 ^ (prefixWord ++ tailWord_4535601).sum := by decide
  have hdescent : baseEnd_4535601 < baseStart_4535601 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535661 : List Nat := [1, 5, 1, 1, 1, 3, 2, 3, 1, 3, 2]
def baseStart_4535661 : Nat := 118140960795 + 4535661 * 2 ^ 59
def prefixEnd_4535661 : Nat := 4983230072969 + 3 ^ 40 * 4535661 * 2
def baseEnd_4535661 : Nat := 2328974178852483939178381

theorem tailTrace_4535661 : CollatzResearch.WordTrace tailWord_4535661 prefixEnd_4535661 2328974178852483939178381 := by
  unfold tailWord_4535661
  simp only [CollatzResearch.WordTrace]
  refine ⟨165429147221082301072526837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110286098147388200715017891 165429147221082301072526837)
  ·
    refine ⟨15508982551976465725549391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165429147221082301072526837 15508982551976465725549391)
    ·
      refine ⟨23263473827964698588324087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15508982551976465725549391 23263473827964698588324087)
      ·
        refine ⟨34895210741947047882486131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23263473827964698588324087 34895210741947047882486131)
        ·
          refine ⟨52342816112920571823729197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34895210741947047882486131 52342816112920571823729197)
          ·
            refine ⟨19628556042345214433898449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52342816112920571823729197 19628556042345214433898449)
            ·
              refine ⟨14721417031758910825423837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19628556042345214433898449 14721417031758910825423837)
              ·
                refine ⟨5520531386909591559533939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14721417031758910825423837 5520531386909591559533939)
                ·
                  refine ⟨8280797080364387339300909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5520531386909591559533939 8280797080364387339300909)
                  ·
                    refine ⟨3105298905136645252237841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8280797080364387339300909 3105298905136645252237841)
                    ·
                      refine ⟨2328974178852483939178381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105298905136645252237841 2328974178852483939178381)
                      ·
                        rfl

theorem cell23_4535661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 3, 2].length) (baseStart_4535661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535661 prefixEnd_4535661 := by exact prefixLift 4535661
  have htrace : WordTrace (prefixWord ++ tailWord_4535661) baseStart_4535661 baseEnd_4535661 := by
    simpa [prefixWord, tailWord_4535661, baseEnd_4535661] using wordTrace_append hprefix tailTrace_4535661
  have hstable : (prefixWord ++ tailWord_4535661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535661).length < 2 ^ (prefixWord ++ tailWord_4535661).sum := by decide
  have hdescent : baseEnd_4535661 < baseStart_4535661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535677 : List Nat := [1, 4, 1, 1, 2, 2, 2, 1, 2, 4, 3]
def baseStart_4535677 : Nat := 118140960795 + 4535677 * 2 ^ 59
def prefixEnd_4535677 : Nat := 4983230072969 + 3 ^ 40 * 4535677 * 2
def baseEnd_4535677 : Nat := 2328982394542955876578307

theorem tailTrace_4535677 : CollatzResearch.WordTrace tailWord_4535677 prefixEnd_4535677 2328982394542955876578307 := by
  unfold tailWord_4535677
  simp only [CollatzResearch.WordTrace]
  refine ⟨165429730789024335805109285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110286487192682890536739523 165429730789024335805109285)
  ·
    refine ⟨31018074522942062963457991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165429730789024335805109285 31018074522942062963457991)
    ·
      refine ⟨46527111784413094445186987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31018074522942062963457991 46527111784413094445186987)
      ·
        refine ⟨69790667676619641667780481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46527111784413094445186987 69790667676619641667780481)
        ·
          refine ⟨52343000757464731250835361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69790667676619641667780481 52343000757464731250835361)
          ·
            refine ⟨39257250568098548438126521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52343000757464731250835361 39257250568098548438126521)
            ·
              refine ⟨29442937926073911328594891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39257250568098548438126521 29442937926073911328594891)
              ·
                refine ⟨44164406889110866992892337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29442937926073911328594891 44164406889110866992892337)
                ·
                  refine ⟨33123305166833150244669253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44164406889110866992892337 33123305166833150244669253)
                  ·
                    refine ⟨6210619718781215670875485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33123305166833150244669253 6210619718781215670875485)
                    ·
                      refine ⟨2328982394542955876578307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6210619718781215670875485 2328982394542955876578307)
                      ·
                        rfl

theorem cell23_4535677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 4, 3].length) (baseStart_4535677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535677 prefixEnd_4535677 := by exact prefixLift 4535677
  have htrace : WordTrace (prefixWord ++ tailWord_4535677) baseStart_4535677 baseEnd_4535677 := by
    simpa [prefixWord, tailWord_4535677, baseEnd_4535677] using wordTrace_append hprefix tailTrace_4535677
  have hstable : (prefixWord ++ tailWord_4535677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535677).length < 2 ^ (prefixWord ++ tailWord_4535677).sum := by decide
  have hdescent : baseEnd_4535677 < baseStart_4535677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535691 : List Nat := [1, 1, 1, 1, 4, 3, 3, 3, 2, 2, 2]
def baseStart_4535691 : Nat := 118140960795 + 4535691 * 2 ^ 59
def prefixEnd_4535691 : Nat := 4983230072969 + 3 ^ 40 * 4535691 * 2
def baseEnd_4535691 : Nat := 2328989583272118821803243

theorem tailTrace_4535691 : CollatzResearch.WordTrace tailWord_4535691 prefixEnd_4535691 2328989583272118821803243 := by
  unfold tailWord_4535691
  simp only [CollatzResearch.WordTrace]
  refine ⟨165430241410973616196118927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110286827607315744130745951 165430241410973616196118927)
  ·
    refine ⟨248145362116460424294178391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165430241410973616196118927 248145362116460424294178391)
    ·
      refine ⟨372218043174690636441267587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248145362116460424294178391 372218043174690636441267587)
      ·
        refine ⟨558327064762035954661901381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372218043174690636441267587 558327064762035954661901381)
        ·
          refine ⟨104686324642881741499106509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 558327064762035954661901381 104686324642881741499106509)
          ·
            refine ⟨39257371741080653062164941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104686324642881741499106509 39257371741080653062164941)
            ·
              refine ⟨14721514402905244898311853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39257371741080653062164941 14721514402905244898311853)
              ·
                refine ⟨5520567901089466836866945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14721514402905244898311853 5520567901089466836866945)
                ·
                  refine ⟨4140425925817100127650209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5520567901089466836866945 4140425925817100127650209)
                  ·
                    refine ⟨3105319444362825095737657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4140425925817100127650209 3105319444362825095737657)
                    ·
                      refine ⟨2328989583272118821803243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105319444362825095737657 2328989583272118821803243)
                      ·
                        rfl

theorem cell23_4535691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 2, 2].length) (baseStart_4535691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535691 prefixEnd_4535691 := by exact prefixLift 4535691
  have htrace : WordTrace (prefixWord ++ tailWord_4535691) baseStart_4535691 baseEnd_4535691 := by
    simpa [prefixWord, tailWord_4535691, baseEnd_4535691] using wordTrace_append hprefix tailTrace_4535691
  have hstable : (prefixWord ++ tailWord_4535691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535691).length < 2 ^ (prefixWord ++ tailWord_4535691).sum := by decide
  have hdescent : baseEnd_4535691 < baseStart_4535691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535708 : List Nat := [2, 2, 3, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_4535708 : Nat := 118140960795 + 4535708 * 2 ^ 59
def prefixEnd_4535708 : Nat := 4983230072969 + 3 ^ 40 * 4535708 * 2
def baseEnd_4535708 : Nat := 2328998312443245255290665

theorem tailTrace_4535708 : CollatzResearch.WordTrace tailWord_4535708 prefixEnd_4535708 2328998312443245255290665 := by
  unfold tailWord_4535708
  simp only [CollatzResearch.WordTrace]
  refine ⟨82715430725956014049743889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110287240967941352066325185 82715430725956014049743889)
  ·
    refine ⟨62036573044467010537307917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82715430725956014049743889 62036573044467010537307917)
    ·
      refine ⟨23263714891675128951490469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62036573044467010537307917 23263714891675128951490469)
      ·
        refine ⟨4361946542189086678404463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23263714891675128951490469 4361946542189086678404463)
        ·
          refine ⟨6542919813283630017606695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4361946542189086678404463 6542919813283630017606695)
          ·
            refine ⟨9814379719925445026410043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6542919813283630017606695 9814379719925445026410043)
            ·
              refine ⟨14721569579888167539615065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9814379719925445026410043 14721569579888167539615065)
              ·
                refine ⟨11041177184916125654711299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14721569579888167539615065 11041177184916125654711299)
                ·
                  refine ⟨16561765777374188482066949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11041177184916125654711299 16561765777374188482066949)
                  ·
                    refine ⟨3105331083257660340387553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16561765777374188482066949 3105331083257660340387553)
                    ·
                      refine ⟨2328998312443245255290665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105331083257660340387553 2328998312443245255290665)
                      ·
                        rfl

theorem cell23_4535708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_4535708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535708 prefixEnd_4535708 := by exact prefixLift 4535708
  have htrace : WordTrace (prefixWord ++ tailWord_4535708) baseStart_4535708 baseEnd_4535708 := by
    simpa [prefixWord, tailWord_4535708, baseEnd_4535708] using wordTrace_append hprefix tailTrace_4535708
  have hstable : (prefixWord ++ tailWord_4535708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535708).length < 2 ^ (prefixWord ++ tailWord_4535708).sum := by decide
  have hdescent : baseEnd_4535708 < baseStart_4535708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535725 : List Nat := [1, 5, 2, 2, 1, 2, 2, 2, 2, 2, 2]
def baseStart_4535725 : Nat := 118140960795 + 4535725 * 2 ^ 59
def prefixEnd_4535725 : Nat := 4983230072969 + 3 ^ 40 * 4535725 * 2
def baseEnd_4535725 : Nat := 2329007041614371688778087

theorem tailTrace_4535725 : CollatzResearch.WordTrace tailWord_4535725 prefixEnd_4535725 2329007041614371688778087 := by
  unfold tailWord_4535725
  simp only [CollatzResearch.WordTrace]
  refine ⟨165431481492850440002856629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110287654328566960001904419 165431481492850440002856629)
  ·
    refine ⟨15509201389954728750267809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165431481492850440002856629 15509201389954728750267809)
    ·
      refine ⟨11631901042466046562700857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15509201389954728750267809 11631901042466046562700857)
      ·
        refine ⟨8723925781849534922025643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11631901042466046562700857 8723925781849534922025643)
        ·
          refine ⟨13085888672774302383038465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8723925781849534922025643 13085888672774302383038465)
          ·
            refine ⟨9814416504580726787278849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13085888672774302383038465 9814416504580726787278849)
            ·
              refine ⟨7360812378435545090459137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9814416504580726787278849 7360812378435545090459137)
              ·
                refine ⟨5520609283826658817844353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7360812378435545090459137 5520609283826658817844353)
                ·
                  refine ⟨4140456962869994113383265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5520609283826658817844353 4140456962869994113383265)
                  ·
                    refine ⟨3105342722152495585037449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4140456962869994113383265 3105342722152495585037449)
                    ·
                      refine ⟨2329007041614371688778087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105342722152495585037449 2329007041614371688778087)
                      ·
                        rfl

theorem cell23_4535725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_4535725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535725 prefixEnd_4535725 := by exact prefixLift 4535725
  have htrace : WordTrace (prefixWord ++ tailWord_4535725) baseStart_4535725 baseEnd_4535725 := by
    simpa [prefixWord, tailWord_4535725, baseEnd_4535725] using wordTrace_append hprefix tailTrace_4535725
  have hstable : (prefixWord ++ tailWord_4535725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535725).length < 2 ^ (prefixWord ++ tailWord_4535725).sum := by decide
  have hdescent : baseEnd_4535725 < baseStart_4535725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535747 : List Nat := [1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 4]
def baseStart_4535747 : Nat := 118140960795 + 4535747 * 2 ^ 59
def prefixEnd_4535747 : Nat := 4983230072969 + 3 ^ 40 * 4535747 * 2
def baseEnd_4535747 : Nat := 2329018338188770602702985

theorem tailTrace_4535747 : CollatzResearch.WordTrace tailWord_4535747 prefixEnd_4535747 2329018338188770602702985 := by
  unfold tailWord_4535747
  simp only [CollatzResearch.WordTrace]
  refine ⟨165432283898770737760157495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110288189265847158506771663 165432283898770737760157495)
  ·
    refine ⟨248148425848156106640236243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165432283898770737760157495 248148425848156106640236243)
    ·
      refine ⟨372222638772234159960354365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248148425848156106640236243 372222638772234159960354365)
      ·
        refine ⟨139583489539587809985132887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 372222638772234159960354365 139583489539587809985132887)
        ·
          refine ⟨209375234309381714977699331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139583489539587809985132887 209375234309381714977699331)
          ·
            refine ⟨314062851464072572466548997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209375234309381714977699331 314062851464072572466548997)
            ·
              refine ⟨58886784649513607337477937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 314062851464072572466548997 58886784649513607337477937)
              ·
                refine ⟨44165088487135205503108453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58886784649513607337477937 44165088487135205503108453)
                ·
                  refine ⟨8280954091337851031832835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44165088487135205503108453 8280954091337851031832835)
                  ·
                    refine ⟨12421431137006776547749253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8280954091337851031832835 12421431137006776547749253)
                    ·
                      refine ⟨2329018338188770602702985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12421431137006776547749253 2329018338188770602702985)
                      ·
                        rfl

theorem cell23_4535747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 2, 4, 1, 4].length) (baseStart_4535747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535747 prefixEnd_4535747 := by exact prefixLift 4535747
  have htrace : WordTrace (prefixWord ++ tailWord_4535747) baseStart_4535747 baseEnd_4535747 := by
    simpa [prefixWord, tailWord_4535747, baseEnd_4535747] using wordTrace_append hprefix tailTrace_4535747
  have hstable : (prefixWord ++ tailWord_4535747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535747).length < 2 ^ (prefixWord ++ tailWord_4535747).sum := by decide
  have hdescent : baseEnd_4535747 < baseStart_4535747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535777 : List Nat := [1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 6]
def baseStart_4535777 : Nat := 118140960795 + 4535777 * 2 ^ 59
def prefixEnd_4535777 : Nat := 4983230072969 + 3 ^ 40 * 4535777 * 2
def baseEnd_4535777 : Nat := 2329033742608405485327847

theorem tailTrace_4535777 : CollatzResearch.WordTrace tailWord_4535777 prefixEnd_4535777 2329033742608405485327847 := by
  unfold tailWord_4535777
  simp only [CollatzResearch.WordTrace]
  refine ⟨165433378088662052883749585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110288918725774701922499723 165433378088662052883749585)
  ·
    refine ⟨124075033566496539662812189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165433378088662052883749585 124075033566496539662812189)
    ·
      refine ⟨46528137587436202373554571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124075033566496539662812189 46528137587436202373554571)
      ·
        refine ⟨69792206381154303560331857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46528137587436202373554571 69792206381154303560331857)
        ·
          refine ⟨52344154785865727670248893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69792206381154303560331857 52344154785865727670248893)
          ·
            refine ⟨19629058044699647876343335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52344154785865727670248893 19629058044699647876343335)
            ·
              refine ⟨29443587067049471814515003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19629058044699647876343335 29443587067049471814515003)
              ·
                refine ⟨44165380600574207721772505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29443587067049471814515003 44165380600574207721772505)
                ·
                  refine ⟨33124035450430655791329379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44165380600574207721772505 33124035450430655791329379)
                  ·
                    refine ⟨49686053175645983686994069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33124035450430655791329379 49686053175645983686994069)
                    ·
                      refine ⟨2329033742608405485327847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 49686053175645983686994069 2329033742608405485327847)
                      ·
                        rfl

theorem cell23_4535777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 1, 2, 1, 6].length) (baseStart_4535777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535777 prefixEnd_4535777 := by exact prefixLift 4535777
  have htrace : WordTrace (prefixWord ++ tailWord_4535777) baseStart_4535777 baseEnd_4535777 := by
    simpa [prefixWord, tailWord_4535777, baseEnd_4535777] using wordTrace_append hprefix tailTrace_4535777
  have hstable : (prefixWord ++ tailWord_4535777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535777).length < 2 ^ (prefixWord ++ tailWord_4535777).sum := by decide
  have hdescent : baseEnd_4535777 < baseStart_4535777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535781 : List Nat := [1, 3, 1, 5, 1, 1, 1, 2, 2, 4, 2]
def baseStart_4535781 : Nat := 118140960795 + 4535781 * 2 ^ 59
def prefixEnd_4535781 : Nat := 4983230072969 + 3 ^ 40 * 4535781 * 2
def baseEnd_4535781 : Nat := 2329035796531023469677829

theorem tailTrace_4535781 : CollatzResearch.WordTrace tailWord_4535781 prefixEnd_4535781 2329035796531023469677829 := by
  unfold tailWord_4535781
  simp only [CollatzResearch.WordTrace]
  refine ⟨165433523980647561566895197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110289015987098374377930131 165433523980647561566895197)
  ·
    refine ⟨62037571492742835587585699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165433523980647561566895197 62037571492742835587585699)
    ·
      refine ⟨93056357239114253381378549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62037571492742835587585699 93056357239114253381378549)
      ·
        refine ⟨8724033491166961254504239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93056357239114253381378549 8724033491166961254504239)
        ·
          refine ⟨13086050236750441881756359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8724033491166961254504239 13086050236750441881756359)
          ·
            refine ⟨19629075355125662822634539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13086050236750441881756359 19629075355125662822634539)
            ·
              refine ⟨29443613032688494233951809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19629075355125662822634539 29443613032688494233951809)
              ·
                refine ⟨22082709774516370675463857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29443613032688494233951809 22082709774516370675463857)
                ·
                  refine ⟨16562032330887278006597893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22082709774516370675463857 16562032330887278006597893)
                  ·
                    refine ⟨3105381062041364626237105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16562032330887278006597893 3105381062041364626237105)
                    ·
                      refine ⟨2329035796531023469677829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105381062041364626237105 2329035796531023469677829)
                      ·
                        rfl

theorem cell23_4535781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 4, 2].length) (baseStart_4535781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535781 prefixEnd_4535781 := by exact prefixLift 4535781
  have htrace : WordTrace (prefixWord ++ tailWord_4535781) baseStart_4535781 baseEnd_4535781 := by
    simpa [prefixWord, tailWord_4535781, baseEnd_4535781] using wordTrace_append hprefix tailTrace_4535781
  have hstable : (prefixWord ++ tailWord_4535781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535781).length < 2 ^ (prefixWord ++ tailWord_4535781).sum := by decide
  have hdescent : baseEnd_4535781 < baseStart_4535781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535784 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 4, 2, 3]
def baseStart_4535784 : Nat := 118140960795 + 4535784 * 2 ^ 59
def prefixEnd_4535784 : Nat := 4983230072969 + 3 ^ 40 * 4535784 * 2
def baseEnd_4535784 : Nat := 2329037336972986957940315

theorem tailTrace_4535784 : CollatzResearch.WordTrace tailWord_4535784 prefixEnd_4535784 2329037336972986957940315 := by
  unfold tailWord_4535784
  simp only [CollatzResearch.WordTrace]
  refine ⟨82716816699818346539627203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110289088933091128719502937 82716816699818346539627203)
  ·
    refine ⟨124075225049727519809440805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82716816699818346539627203 124075225049727519809440805)
    ·
      refine ⟨23264104696823909964270151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124075225049727519809440805 23264104696823909964270151)
      ·
        refine ⟨34896157045235864946405227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23264104696823909964270151 34896157045235864946405227)
        ·
          refine ⟨52344235567853797419607841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34896157045235864946405227 52344235567853797419607841)
          ·
            refine ⟨39258176675890348064705881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52344235567853797419607841 39258176675890348064705881)
            ·
              refine ⟨29443632506917761048529411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39258176675890348064705881 29443632506917761048529411)
              ·
                refine ⟨44165448760376641572794117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29443632506917761048529411 44165448760376641572794117)
                ·
                  refine ⟨8281021642570620294898897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44165448760376641572794117 8281021642570620294898897)
                  ·
                    refine ⟨6210766231927965221174173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8281021642570620294898897 6210766231927965221174173)
                    ·
                      refine ⟨2329037336972986957940315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6210766231927965221174173 2329037336972986957940315)
                      ·
                        rfl

theorem cell23_4535784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 4, 2, 3].length) (baseStart_4535784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535784 prefixEnd_4535784 := by exact prefixLift 4535784
  have htrace : WordTrace (prefixWord ++ tailWord_4535784) baseStart_4535784 baseEnd_4535784 := by
    simpa [prefixWord, tailWord_4535784, baseEnd_4535784] using wordTrace_append hprefix tailTrace_4535784
  have hstable : (prefixWord ++ tailWord_4535784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535784).length < 2 ^ (prefixWord ++ tailWord_4535784).sum := by decide
  have hdescent : baseEnd_4535784 < baseStart_4535784 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535787 : List Nat := [1, 1, 1, 1, 2, 3, 2, 6, 6]
def baseStart_4535787 : Nat := 118140960795 + 4535787 * 2 ^ 59
def prefixEnd_4535787 : Nat := 4983230072969 + 3 ^ 40 * 4535787 * 2
def baseEnd_4535787 : Nat := 258782097490550049578089

theorem tailTrace_4535787 : CollatzResearch.WordTrace tailWord_4535787 prefixEnd_4535787 258782097490550049578089 := by
  unfold tailWord_4535787
  simp only [CollatzResearch.WordTrace]
  refine ⟨165433742818625824591613615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110289161879083883061075743 165433742818625824591613615)
  ·
    refine ⟨248150614227938736887420423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165433742818625824591613615 248150614227938736887420423)
    ·
      refine ⟨372225921341908105331130635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248150614227938736887420423 372225921341908105331130635)
      ·
        refine ⟨558338882012862157996695953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372225921341908105331130635 558338882012862157996695953)
        ·
          refine ⟨418754161509646618497521965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 558338882012862157996695953 418754161509646618497521965)
          ·
            refine ⟨157032810566117481936570737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 418754161509646618497521965 157032810566117481936570737)
            ·
              refine ⟨117774607924588111452428053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157032810566117481936570737 117774607924588111452428053)
              ·
                refine ⟨5520684746465067724332565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 117774607924588111452428053 5520684746465067724332565)
                ·
                  refine ⟨258782097490550049578089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5520684746465067724332565 258782097490550049578089)
                  ·
                    rfl

theorem cell23_4535787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 6, 6].length) (baseStart_4535787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535787 prefixEnd_4535787 := by exact prefixLift 4535787
  have htrace : WordTrace (prefixWord ++ tailWord_4535787) baseStart_4535787 baseEnd_4535787 := by
    simpa [prefixWord, tailWord_4535787, baseEnd_4535787] using wordTrace_append hprefix tailTrace_4535787
  have hstable : (prefixWord ++ tailWord_4535787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535787).length < 2 ^ (prefixWord ++ tailWord_4535787).sum := by decide
  have hdescent : baseEnd_4535787 < baseStart_4535787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535791 : List Nat := [1, 1, 2, 1, 4, 1, 4, 4, 1, 4]
def baseStart_4535791 : Nat := 118140960795 + 4535791 * 2 ^ 59
def prefixEnd_4535791 : Nat := 4983230072969 + 3 ^ 40 * 4535791 * 2
def baseEnd_4535791 : Nat := 776346977112522810184261

theorem tailTrace_4535791 : CollatzResearch.WordTrace tailWord_4535791 prefixEnd_4535791 776346977112522810184261 := by
  unfold tailWord_4535791
  simp only [CollatzResearch.WordTrace]
  refine ⟨165433888710611333274759227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110289259140407555516506151 165433888710611333274759227)
  ·
    refine ⟨248150833065916999912138841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165433888710611333274759227 248150833065916999912138841)
    ·
      refine ⟨186113124799437749934104131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248150833065916999912138841 186113124799437749934104131)
      ·
        refine ⟨279169687199156624901156197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186113124799437749934104131 279169687199156624901156197)
        ·
          refine ⟨52344316349841867168966787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 279169687199156624901156197 52344316349841867168966787)
          ·
            refine ⟨78516474524762800753450181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52344316349841867168966787 78516474524762800753450181)
            ·
              refine ⟨14721838973393025141271909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78516474524762800753450181 14721838973393025141271909)
              ·
                refine ⟨2760344807511192213988483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14721838973393025141271909 2760344807511192213988483)
                ·
                  refine ⟨4140517211266788320982725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760344807511192213988483 4140517211266788320982725)
                  ·
                    refine ⟨776346977112522810184261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4140517211266788320982725 776346977112522810184261)
                    ·
                      rfl

theorem cell23_4535791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 1, 4].length) (baseStart_4535791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535791 prefixEnd_4535791 := by exact prefixLift 4535791
  have htrace : WordTrace (prefixWord ++ tailWord_4535791) baseStart_4535791 baseEnd_4535791 := by
    simpa [prefixWord, tailWord_4535791, baseEnd_4535791] using wordTrace_append hprefix tailTrace_4535791
  have hstable : (prefixWord ++ tailWord_4535791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535791).length < 2 ^ (prefixWord ++ tailWord_4535791).sum := by decide
  have hdescent : baseEnd_4535791 < baseStart_4535791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535841 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 4, 3, 2]
def baseStart_4535841 : Nat := 118140960795 + 4535841 * 2 ^ 59
def prefixEnd_4535841 : Nat := 4983230072969 + 3 ^ 40 * 4535841 * 2
def baseEnd_4535841 : Nat := 2329066605370293234927553

theorem tailTrace_4535841 : CollatzResearch.WordTrace tailWord_4535841 prefixEnd_4535841 2329066605370293234927553 := by
  unfold tailWord_4535841
  simp only [CollatzResearch.WordTrace]
  refine ⟨165435712360430191814079377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110290474906953461209386251 165435712360430191814079377)
  ·
    refine ⟨124076784270322643860559533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165435712360430191814079377 124076784270322643860559533)
    ·
      refine ⟨46528794101370991447709825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124076784270322643860559533 46528794101370991447709825)
      ·
        refine ⟨34896595576028243585782369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46528794101370991447709825 34896595576028243585782369)
        ·
          refine ⟨26172446682021182689336777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34896595576028243585782369 26172446682021182689336777)
          ·
            refine ⟨19629335011515887017002583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26172446682021182689336777 19629335011515887017002583)
            ·
              refine ⟨29444002517273830525503875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19629335011515887017002583 29444002517273830525503875)
              ·
                refine ⟨44166003775910745788255813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29444002517273830525503875 44166003775910745788255813)
                ·
                  refine ⟨8281125707983264835297965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44166003775910745788255813 8281125707983264835297965)
                  ·
                    refine ⟨3105422140493724313236737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8281125707983264835297965 3105422140493724313236737)
                    ·
                      refine ⟨2329066605370293234927553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105422140493724313236737 2329066605370293234927553)
                      ·
                        rfl

theorem cell23_4535841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_4535841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535841 prefixEnd_4535841 := by exact prefixLift 4535841
  have htrace : WordTrace (prefixWord ++ tailWord_4535841) baseStart_4535841 baseEnd_4535841 := by
    simpa [prefixWord, tailWord_4535841, baseEnd_4535841] using wordTrace_append hprefix tailTrace_4535841
  have hstable : (prefixWord ++ tailWord_4535841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535841).length < 2 ^ (prefixWord ++ tailWord_4535841).sum := by decide
  have hdescent : baseEnd_4535841 < baseStart_4535841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535867 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 4]
def baseStart_4535867 : Nat := 118140960795 + 4535867 * 2 ^ 59
def prefixEnd_4535867 : Nat := 4983230072969 + 3 ^ 40 * 4535867 * 2
def baseEnd_4535867 : Nat := 2329079955867310133202433

theorem tailTrace_4535867 : CollatzResearch.WordTrace tailWord_4535867 prefixEnd_4535867 2329079955867310133202433 := by
  unfold tailWord_4535867
  simp only [CollatzResearch.WordTrace]
  refine ⟨165436660658335998254525855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110291107105557332169683903 165436660658335998254525855)
  ·
    refine ⟨248154990987503997381788783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165436660658335998254525855 248154990987503997381788783)
    ·
      refine ⟨372232486481255996072683175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248154990987503997381788783 372232486481255996072683175)
      ·
        refine ⟨558348729721883994109024763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372232486481255996072683175 558348729721883994109024763)
        ·
          refine ⟨837523094582825991163537145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558348729721883994109024763 837523094582825991163537145)
          ·
            refine ⟨628142320937119493372652859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 837523094582825991163537145 628142320937119493372652859)
            ·
              refine ⟨942213481405679240058979289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 628142320937119493372652859 942213481405679240058979289)
              ·
                refine ⟨706660111054259430044234467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 942213481405679240058979289 706660111054259430044234467)
                ·
                  refine ⟨1059990166581389145066351701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706660111054259430044234467 1059990166581389145066351701)
                  ·
                    refine ⟨12421759764625654043746309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1059990166581389145066351701 12421759764625654043746309)
                    ·
                      refine ⟨2329079955867310133202433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12421759764625654043746309 2329079955867310133202433)
                      ·
                        rfl

theorem cell23_4535867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1, 8, 4].length) (baseStart_4535867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535867 prefixEnd_4535867 := by exact prefixLift 4535867
  have htrace : WordTrace (prefixWord ++ tailWord_4535867) baseStart_4535867 baseEnd_4535867 := by
    simpa [prefixWord, tailWord_4535867, baseEnd_4535867] using wordTrace_append hprefix tailTrace_4535867
  have hstable : (prefixWord ++ tailWord_4535867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535867).length < 2 ^ (prefixWord ++ tailWord_4535867).sum := by decide
  have hdescent : baseEnd_4535867 < baseStart_4535867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535868 : List Nat := [2, 2, 2, 2, 4, 2, 1, 2, 1, 5]
def baseStart_4535868 : Nat := 118140960795 + 4535868 * 2 ^ 59
def prefixEnd_4535868 : Nat := 4983230072969 + 3 ^ 40 * 4535868 * 2
def baseEnd_4535868 : Nat := 776360156449321543096643

theorem tailTrace_4535868 : CollatzResearch.WordTrace tailWord_4535868 prefixEnd_4535868 776360156449321543096643 := by
  unfold tailWord_4535868
  simp only [CollatzResearch.WordTrace]
  refine ⟨82718348565666187712656129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110291131420888250283541505 82718348565666187712656129)
  ·
    refine ⟨62038761424249640784492097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82718348565666187712656129 62038761424249640784492097)
    ·
      refine ⟨46529071068187230588369073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62038761424249640784492097 46529071068187230588369073)
      ·
        refine ⟨34896803301140422941276805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46529071068187230588369073 34896803301140422941276805)
        ·
          refine ⟨6543150618963829301489401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34896803301140422941276805 6543150618963829301489401)
          ·
            refine ⟨4907362964222871976117051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6543150618963829301489401 4907362964222871976117051)
            ·
              refine ⟨7361044446334307964175577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4907362964222871976117051 7361044446334307964175577)
              ·
                refine ⟨5520783334750730973131683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7361044446334307964175577 5520783334750730973131683)
                ·
                  refine ⟨8281175002126096459697525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5520783334750730973131683 8281175002126096459697525)
                  ·
                    refine ⟨776360156449321543096643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8281175002126096459697525 776360156449321543096643)
                    ·
                      rfl

theorem cell23_4535868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_4535868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535868 prefixEnd_4535868 := by exact prefixLift 4535868
  have htrace : WordTrace (prefixWord ++ tailWord_4535868) baseStart_4535868 baseEnd_4535868 := by
    simpa [prefixWord, tailWord_4535868, baseEnd_4535868] using wordTrace_append hprefix tailTrace_4535868
  have hstable : (prefixWord ++ tailWord_4535868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535868).length < 2 ^ (prefixWord ++ tailWord_4535868).sum := by decide
  have hdescent : baseEnd_4535868 < baseStart_4535868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535871 : List Nat := [1, 1, 2, 2, 3, 3, 3, 2, 1, 1, 4]
def baseStart_4535871 : Nat := 118140960795 + 4535871 * 2 ^ 59
def prefixEnd_4535871 : Nat := 4983230072969 + 3 ^ 40 * 4535871 * 2
def baseEnd_4535871 : Nat := 2329082009789928117552415

theorem tailTrace_4535871 : CollatzResearch.WordTrace tailWord_4535871 prefixEnd_4535871 2329082009789928117552415 := by
  unfold tailWord_4535871
  simp only [CollatzResearch.WordTrace]
  refine ⟨165436806550321506937671467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110291204366881004625114311 165436806550321506937671467)
  ·
    refine ⟨248155209825482260406507201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165436806550321506937671467 248155209825482260406507201)
    ·
      refine ⟨186116407369111695304880401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 248155209825482260406507201 186116407369111695304880401)
      ·
        refine ⟨139587305526833771478660301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186116407369111695304880401 139587305526833771478660301)
        ·
          refine ⟨52345239572562664304497613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139587305526833771478660301 52345239572562664304497613)
          ·
            refine ⟨19629464839710999114186605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52345239572562664304497613 19629464839710999114186605)
            ·
              refine ⟨7361049314891624667819977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19629464839710999114186605 7361049314891624667819977)
              ·
                refine ⟨5520786986168718500864983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7361049314891624667819977 5520786986168718500864983)
                ·
                  refine ⟨8281180479253077751297475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5520786986168718500864983 8281180479253077751297475)
                  ·
                    refine ⟨12421770718879616626946213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8281180479253077751297475 12421770718879616626946213)
                    ·
                      refine ⟨2329082009789928117552415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12421770718879616626946213 2329082009789928117552415)
                      ·
                        rfl

theorem cell23_4535871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 1, 4].length) (baseStart_4535871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535871 prefixEnd_4535871 := by exact prefixLift 4535871
  have htrace : WordTrace (prefixWord ++ tailWord_4535871) baseStart_4535871 baseEnd_4535871 := by
    simpa [prefixWord, tailWord_4535871, baseEnd_4535871] using wordTrace_append hprefix tailTrace_4535871
  have hstable : (prefixWord ++ tailWord_4535871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535871).length < 2 ^ (prefixWord ++ tailWord_4535871).sum := by decide
  have hdescent : baseEnd_4535871 < baseStart_4535871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535877 : List Nat := [1, 3, 1, 1, 1, 4, 1, 11]
def baseStart_4535877 : Nat := 118140960795 + 4535877 * 2 ^ 59
def prefixEnd_4535877 : Nat := 4983230072969 + 3 ^ 40 * 4535877 * 2
def baseEnd_4535877 : Nat := 86262410765698336817681

theorem tailTrace_4535877 : CollatzResearch.WordTrace tailWord_4535877 prefixEnd_4535877 86262410765698336817681 := by
  unfold tailWord_4535877
  simp only [CollatzResearch.WordTrace]
  refine ⟨165437025388299769962389885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110291350258866513308259923 165437025388299769962389885)
  ·
    refine ⟨62038884520612413735896207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 165437025388299769962389885 62038884520612413735896207)
    ·
      refine ⟨93058326780918620603844311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62038884520612413735896207 93058326780918620603844311)
      ·
        refine ⟨139587490171377930905766467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93058326780918620603844311 139587490171377930905766467)
        ·
          refine ⟨209381235257066896358649701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139587490171377930905766467 209381235257066896358649701)
          ·
            refine ⟨39258981610700043067246819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 209381235257066896358649701 39258981610700043067246819)
            ·
              refine ⟨58888472416050064600870229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39258981610700043067246819 58888472416050064600870229)
              ·
                refine ⟨86262410765698336817681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 58888472416050064600870229 86262410765698336817681)
                ·
                  rfl

theorem cell23_4535877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 11].length) (baseStart_4535877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535877 prefixEnd_4535877 := by exact prefixLift 4535877
  have htrace : WordTrace (prefixWord ++ tailWord_4535877) baseStart_4535877 baseEnd_4535877 := by
    simpa [prefixWord, tailWord_4535877, baseEnd_4535877] using wordTrace_append hprefix tailTrace_4535877
  have hstable : (prefixWord ++ tailWord_4535877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535877).length < 2 ^ (prefixWord ++ tailWord_4535877).sum := by decide
  have hdescent : baseEnd_4535877 < baseStart_4535877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535884 : List Nat := [2, 2, 1, 3, 1, 3, 1, 1, 3, 2, 4]
def baseStart_4535884 : Nat := 118140960795 + 4535884 * 2 ^ 59
def prefixEnd_4535884 : Nat := 4983230072969 + 3 ^ 40 * 4535884 * 2
def baseEnd_4535884 : Nat := 2329088685038436566689855

theorem tailTrace_4535884 : CollatzResearch.WordTrace tailWord_4535884 prefixEnd_4535884 2329088685038436566689855 := by
  unfold tailWord_4535884
  simp only [CollatzResearch.WordTrace]
  refine ⟨82718640349637205078947353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110291520466182940105263137 82718640349637205078947353)
  ·
    refine ⟨62038980262227903809210515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82718640349637205078947353 62038980262227903809210515)
    ·
      refine ⟨93058470393341855713815773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62038980262227903809210515 93058470393341855713815773)
      ·
        refine ⟨34896926397503195892680915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93058470393341855713815773 34896926397503195892680915)
        ·
          refine ⟨52345389596254793839021373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34896926397503195892680915 52345389596254793839021373)
          ·
            refine ⟨19629521098595547689633015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52345389596254793839021373 19629521098595547689633015)
            ·
              refine ⟨29444281647893321534449523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19629521098595547689633015 29444281647893321534449523)
              ·
                refine ⟨44166422471839982301674285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29444281647893321534449523 44166422471839982301674285)
                ·
                  refine ⟨16562408426939993363127857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44166422471839982301674285 16562408426939993363127857)
                  ·
                    refine ⟨12421806320204995022345893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16562408426939993363127857 12421806320204995022345893)
                    ·
                      refine ⟨2329088685038436566689855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12421806320204995022345893 2329088685038436566689855)
                      ·
                        rfl

theorem cell23_4535884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_4535884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535884 prefixEnd_4535884 := by exact prefixLift 4535884
  have htrace : WordTrace (prefixWord ++ tailWord_4535884) baseStart_4535884 baseEnd_4535884 := by
    simpa [prefixWord, tailWord_4535884, baseEnd_4535884] using wordTrace_append hprefix tailTrace_4535884
  have hstable : (prefixWord ++ tailWord_4535884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535884).length < 2 ^ (prefixWord ++ tailWord_4535884).sum := by decide
  have hdescent : baseEnd_4535884 < baseStart_4535884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535885 : List Nat := [1, 6, 1, 1, 3, 1, 3, 1, 1, 5]
def baseStart_4535885 : Nat := 118140960795 + 4535885 * 2 ^ 59
def prefixEnd_4535885 : Nat := 4983230072969 + 3 ^ 40 * 4535885 * 2
def baseEnd_4535885 : Nat := 776363066173030354259117

theorem tailTrace_4535885 : CollatzResearch.WordTrace tailWord_4535885 prefixEnd_4535885 776363066173030354259117 := by
  unfold tailWord_4535885
  simp only [CollatzResearch.WordTrace]
  refine ⟨165437317172270787328681109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110291544781513858219120739 165437317172270787328681109)
  ·
    refine ⟨7754874242450193156031927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 165437317172270787328681109 7754874242450193156031927)
    ·
      refine ⟨11632311363675289734047891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7754874242450193156031927 11632311363675289734047891)
      ·
        refine ⟨17448467045512934601071837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11632311363675289734047891 17448467045512934601071837)
        ·
          refine ⟨6543175142067350475401939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17448467045512934601071837 6543175142067350475401939)
          ·
            refine ⟨9814762713101025713102909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6543175142067350475401939 9814762713101025713102909)
            ·
              refine ⟨3680536017412884642413591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9814762713101025713102909 3680536017412884642413591)
              ·
                refine ⟨5520804026119326963620387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3680536017412884642413591 5520804026119326963620387)
                ·
                  refine ⟨8281206039178990445430581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5520804026119326963620387 8281206039178990445430581)
                  ·
                    refine ⟨776363066173030354259117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8281206039178990445430581 776363066173030354259117)
                    ·
                      rfl

theorem cell23_4535885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 1, 5].length) (baseStart_4535885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535885 prefixEnd_4535885 := by exact prefixLift 4535885
  have htrace : WordTrace (prefixWord ++ tailWord_4535885) baseStart_4535885 baseEnd_4535885 := by
    simpa [prefixWord, tailWord_4535885, baseEnd_4535885] using wordTrace_append hprefix tailTrace_4535885
  have hstable : (prefixWord ++ tailWord_4535885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535885).length < 2 ^ (prefixWord ++ tailWord_4535885).sum := by decide
  have hdescent : baseEnd_4535885 < baseStart_4535885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535904 : List Nat := [2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 3]
def baseStart_4535904 : Nat := 118140960795 + 4535904 * 2 ^ 59
def prefixEnd_4535904 : Nat := 4983230072969 + 3 ^ 40 * 4535904 * 2
def baseEnd_4535904 : Nat := 2329098954651526488439763

theorem tailTrace_4535904 : CollatzResearch.WordTrace tailWord_4535904 prefixEnd_4535904 2329098954651526488439763 := by
  unfold tailWord_4535904
  simp only [CollatzResearch.WordTrace]
  refine ⟨82719005079600976786811383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110292006772801302382415177 82719005079600976786811383)
  ·
    refine ⟨124078507619401465180217075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82719005079600976786811383 124078507619401465180217075)
    ·
      refine ⟨186117761429102197770325613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124078507619401465180217075 186117761429102197770325613)
      ·
        refine ⟨69794160535913324163872105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186117761429102197770325613 69794160535913324163872105)
        ·
          refine ⟨52345620401934993122904079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69794160535913324163872105 52345620401934993122904079)
          ·
            refine ⟨78518430602902489684356119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52345620401934993122904079 78518430602902489684356119)
            ·
              refine ⟨117777645904353734526534179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78518430602902489684356119 117777645904353734526534179)
              ·
                refine ⟨176666468856530601789801269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117777645904353734526534179 176666468856530601789801269)
                ·
                  refine ⟨16562481455299743917793869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 176666468856530601789801269 16562481455299743917793869)
                  ·
                    refine ⟨6210930545737403969172701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16562481455299743917793869 6210930545737403969172701)
                    ·
                      refine ⟨2329098954651526488439763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6210930545737403969172701 2329098954651526488439763)
                      ·
                        rfl

theorem cell23_4535904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_4535904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535904 prefixEnd_4535904 := by exact prefixLift 4535904
  have htrace : WordTrace (prefixWord ++ tailWord_4535904) baseStart_4535904 baseEnd_4535904 := by
    simpa [prefixWord, tailWord_4535904, baseEnd_4535904] using wordTrace_append hprefix tailTrace_4535904
  have hstable : (prefixWord ++ tailWord_4535904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535904).length < 2 ^ (prefixWord ++ tailWord_4535904).sum := by decide
  have hdescent : baseEnd_4535904 < baseStart_4535904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535905 : List Nat := [1, 2, 3, 1, 1, 3, 3, 4, 1, 2, 2]
def baseStart_4535905 : Nat := 118140960795 + 4535905 * 2 ^ 59
def prefixEnd_4535905 : Nat := 4983230072969 + 3 ^ 40 * 4535905 * 2
def baseEnd_4535905 : Nat := 2329099468132180984527259

theorem tailTrace_4535905 : CollatzResearch.WordTrace tailWord_4535905 prefixEnd_4535905 2329099468132180984527259 := by
  unfold tailWord_4535905
  simp only [CollatzResearch.WordTrace]
  refine ⟨165438046632198330744409169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110292031088132220496272779 165438046632198330744409169)
  ·
    refine ⟨124078534974148748058306877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 165438046632198330744409169 124078534974148748058306877)
    ·
      refine ⟨46529450615305780521865079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124078534974148748058306877 46529450615305780521865079)
      ·
        refine ⟨69794175922958670782797619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46529450615305780521865079 69794175922958670782797619)
        ·
          refine ⟨104691263884438006174196429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69794175922958670782797619 104691263884438006174196429)
          ·
            refine ⟨39259223956664252315323661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104691263884438006174196429 39259223956664252315323661)
            ·
              refine ⟨14722208983749094618246373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39259223956664252315323661 14722208983749094618246373)
              ·
                refine ⟨2760414184452955240921195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14722208983749094618246373 2760414184452955240921195)
                ·
                  refine ⟨4140621276679432861381793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760414184452955240921195 4140621276679432861381793)
                  ·
                    refine ⟨3105465957509574646036345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4140621276679432861381793 3105465957509574646036345)
                    ·
                      refine ⟨2329099468132180984527259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105465957509574646036345 2329099468132180984527259)
                      ·
                        rfl

theorem cell23_4535905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 1, 2, 2].length) (baseStart_4535905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535905 prefixEnd_4535905 := by exact prefixLift 4535905
  have htrace : WordTrace (prefixWord ++ tailWord_4535905) baseStart_4535905 baseEnd_4535905 := by
    simpa [prefixWord, tailWord_4535905, baseEnd_4535905] using wordTrace_append hprefix tailTrace_4535905
  have hstable : (prefixWord ++ tailWord_4535905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535905).length < 2 ^ (prefixWord ++ tailWord_4535905).sum := by decide
  have hdescent : baseEnd_4535905 < baseStart_4535905 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535918 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 1, 2, 4]
def baseStart_4535918 : Nat := 118140960795 + 4535918 * 2 ^ 59
def prefixEnd_4535918 : Nat := 4983230072969 + 3 ^ 40 * 4535918 * 2
def baseEnd_4535918 : Nat := 2329106143380689433664699

theorem tailTrace_4535918 : CollatzResearch.WordTrace tailWord_4535918 prefixEnd_4535918 2329106143380689433664699 := by
  unfold tailWord_4535918
  simp only [CollatzResearch.WordTrace]
  refine ⟨20679815097643904245579051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 110292347187434155976421605 20679815097643904245579051)
  ·
    refine ⟨31019722646465856368368577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20679815097643904245579051 31019722646465856368368577)
    ·
      refine ⟨23264791984849392276276433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31019722646465856368368577 23264791984849392276276433)
      ·
        refine ⟨17448593988637044207207325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23264791984849392276276433 17448593988637044207207325)
        ·
          refine ⟨6543222745738891577702747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17448593988637044207207325 6543222745738891577702747)
          ·
            refine ⟨9814834118608337366554121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6543222745738891577702747 9814834118608337366554121)
            ·
              refine ⟨7361125588956253024915591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9814834118608337366554121 7361125588956253024915591)
              ·
                refine ⟨11041688383434379537373387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7361125588956253024915591 11041688383434379537373387)
                ·
                  refine ⟨16562532575151569306060081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11041688383434379537373387 16562532575151569306060081)
                  ·
                    refine ⟨12421899431363676979545061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16562532575151569306060081 12421899431363676979545061)
                    ·
                      refine ⟨2329106143380689433664699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12421899431363676979545061 2329106143380689433664699)
                      ·
                        rfl

theorem cell23_4535918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_4535918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535918 prefixEnd_4535918 := by exact prefixLift 4535918
  have htrace : WordTrace (prefixWord ++ tailWord_4535918) baseStart_4535918 baseEnd_4535918 := by
    simpa [prefixWord, tailWord_4535918, baseEnd_4535918] using wordTrace_append hprefix tailTrace_4535918
  have hstable : (prefixWord ++ tailWord_4535918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535918).length < 2 ^ (prefixWord ++ tailWord_4535918).sum := by decide
  have hdescent : baseEnd_4535918 < baseStart_4535918 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535931 : List Nat := [1, 1, 1, 1, 1, 4, 3, 3, 3, 3, 2]
def baseStart_4535931 : Nat := 118140960795 + 4535931 * 2 ^ 59
def prefixEnd_4535931 : Nat := 4983230072969 + 3 ^ 40 * 4535931 * 2
def baseEnd_4535931 : Nat := 2329112818629197882802139

theorem tailTrace_4535931 : CollatzResearch.WordTrace tailWord_4535931 prefixEnd_4535931 2329112818629197882802139 := by
  unfold tailWord_4535931
  simp only [CollatzResearch.WordTrace]
  refine ⟨165438994930104137184855647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110292663286736091456570431 165438994930104137184855647)
  ·
    refine ⟨248158492395156205777283471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165438994930104137184855647 248158492395156205777283471)
    ·
      refine ⟨372237738592734308665925207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248158492395156205777283471 372237738592734308665925207)
      ·
        refine ⟨558356607889101462998887811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 372237738592734308665925207 558356607889101462998887811)
        ·
          refine ⟨837534911833652194498331717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 558356607889101462998887811 837534911833652194498331717)
          ·
            refine ⟨157037795968809786468437197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 837534911833652194498331717 157037795968809786468437197)
            ·
              refine ⟨58889173488303669925663949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 157037795968809786468437197 58889173488303669925663949)
              ·
                refine ⟨22083440058113876222123981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58889173488303669925663949 22083440058113876222123981)
                ·
                  refine ⟨8281290021792703583296493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22083440058113876222123981 8281290021792703583296493)
                  ·
                    refine ⟨3105483758172263843736185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8281290021792703583296493 3105483758172263843736185)
                    ·
                      refine ⟨2329112818629197882802139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105483758172263843736185 2329112818629197882802139)
                      ·
                        rfl

theorem cell23_4535931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 3, 2].length) (baseStart_4535931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535931 prefixEnd_4535931 := by exact prefixLift 4535931
  have htrace : WordTrace (prefixWord ++ tailWord_4535931) baseStart_4535931 baseEnd_4535931 := by
    simpa [prefixWord, tailWord_4535931, baseEnd_4535931] using wordTrace_append hprefix tailTrace_4535931
  have hstable : (prefixWord ++ tailWord_4535931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535931).length < 2 ^ (prefixWord ++ tailWord_4535931).sum := by decide
  have hdescent : baseEnd_4535931 < baseStart_4535931 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535948 : List Nat := [2, 2, 1, 2, 1, 1, 5, 3, 1, 3, 2]
def baseStart_4535948 : Nat := 118140960795 + 4535948 * 2 ^ 59
def prefixEnd_4535948 : Nat := 4983230072969 + 3 ^ 40 * 4535948 * 2
def baseEnd_4535948 : Nat := 2329121547800324316289561

theorem tailTrace_4535948 : CollatzResearch.WordTrace tailWord_4535948 prefixEnd_4535948 2329121547800324316289561 := by
  unfold tailWord_4535948
  simp only [CollatzResearch.WordTrace]
  refine ⟨82719807485521274544112249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110293076647361699392149665 82719807485521274544112249)
  ·
    refine ⟨62039855614140955908084187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82719807485521274544112249 62039855614140955908084187)
    ·
      refine ⟨93059783421211433862126281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62039855614140955908084187 93059783421211433862126281)
      ·
        refine ⟨69794837565908575396594711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93059783421211433862126281 69794837565908575396594711)
        ·
          refine ⟨104692256348862863094892067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69794837565908575396594711 104692256348862863094892067)
          ·
            refine ⟨157038384523294294642338101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104692256348862863094892067 157038384523294294642338101)
            ·
              refine ⟨14722348549058840122719197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157038384523294294642338101 14722348549058840122719197)
              ·
                refine ⟨5520880705897065046019699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14722348549058840122719197 5520880705897065046019699)
                ·
                  refine ⟨8281321058845597569029549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5520880705897065046019699 8281321058845597569029549)
                  ·
                    refine ⟨3105495397067099088386081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8281321058845597569029549 3105495397067099088386081)
                    ·
                      refine ⟨2329121547800324316289561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105495397067099088386081 2329121547800324316289561)
                      ·
                        rfl

theorem cell23_4535948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 3, 1, 3, 2].length) (baseStart_4535948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535948 prefixEnd_4535948 := by exact prefixLift 4535948
  have htrace : WordTrace (prefixWord ++ tailWord_4535948) baseStart_4535948 baseEnd_4535948 := by
    simpa [prefixWord, tailWord_4535948, baseEnd_4535948] using wordTrace_append hprefix tailTrace_4535948
  have hstable : (prefixWord ++ tailWord_4535948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535948).length < 2 ^ (prefixWord ++ tailWord_4535948).sum := by decide
  have hdescent : baseEnd_4535948 < baseStart_4535948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535981 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 2, 1, 5]
def baseStart_4535981 : Nat := 118140960795 + 4535981 * 2 ^ 59
def prefixEnd_4535981 : Nat := 4983230072969 + 3 ^ 40 * 4535981 * 2
def baseEnd_4535981 : Nat := 2329138492661922687176909

theorem tailTrace_4535981 : CollatzResearch.WordTrace tailWord_4535981 prefixEnd_4535981 2329138492661922687176909 := by
  unfold tailWord_4535981
  simp only [CollatzResearch.WordTrace]
  refine ⟨165440818579922995724175797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110293879053281997149450531 165440818579922995724175797)
  ·
    refine ⟨15510076741867780849141481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 165440818579922995724175797 15510076741867780849141481)
    ·
      refine ⟨11632557556400835636856111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15510076741867780849141481 11632557556400835636856111)
      ·
        refine ⟨17448836334601253455284167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11632557556400835636856111 17448836334601253455284167)
        ·
          refine ⟨26173254501901880182926251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17448836334601253455284167 26173254501901880182926251)
          ·
            refine ⟨39259881752852820274389377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26173254501901880182926251 39259881752852820274389377)
            ·
              refine ⟨29444911314639615205792033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39259881752852820274389377 29444911314639615205792033)
              ·
                refine ⟨22083683485979711404344025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29444911314639615205792033 22083683485979711404344025)
                ·
                  refine ⟨16562762614484783553258019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22083683485979711404344025 16562762614484783553258019)
                  ·
                    refine ⟨24844143921727175329887029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16562762614484783553258019 24844143921727175329887029)
                    ·
                      refine ⟨2329138492661922687176909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24844143921727175329887029 2329138492661922687176909)
                      ·
                        rfl

theorem cell23_4535981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_4535981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535981 prefixEnd_4535981 := by exact prefixLift 4535981
  have htrace : WordTrace (prefixWord ++ tailWord_4535981) baseStart_4535981 baseEnd_4535981 := by
    simpa [prefixWord, tailWord_4535981, baseEnd_4535981] using wordTrace_append hprefix tailTrace_4535981
  have hstable : (prefixWord ++ tailWord_4535981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535981).length < 2 ^ (prefixWord ++ tailWord_4535981).sum := by decide
  have hdescent : baseEnd_4535981 < baseStart_4535981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4535984 : List Nat := [2, 1, 1, 1, 2, 1, 6, 2, 7]
def baseStart_4535984 : Nat := 118140960795 + 4535984 * 2 ^ 59
def prefixEnd_4535984 : Nat := 4983230072969 + 3 ^ 40 * 4535984 * 2
def baseEnd_4535984 : Nat := 258793337011542908382155

theorem tailTrace_4535984 : CollatzResearch.WordTrace tailWord_4535984 prefixEnd_4535984 258793337011542908382155 := by
  unfold tailWord_4535984
  simp only [CollatzResearch.WordTrace]
  refine ⟨82720463999456063618267503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110293951999274751491023337 82720463999456063618267503)
  ·
    refine ⟨124080695999184095427401255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82720463999456063618267503 124080695999184095427401255)
    ·
      refine ⟨186121043998776143141101883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124080695999184095427401255 186121043998776143141101883)
      ·
        refine ⟨279181565998164214711652825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186121043998776143141101883 279181565998164214711652825)
        ·
          refine ⟨209386174498623161033739619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279181565998164214711652825 209386174498623161033739619)
          ·
            refine ⟨314079261747934741550609429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209386174498623161033739619 314079261747934741550609429)
            ·
              refine ⟨14722465394434441010184817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 314079261747934741550609429 14722465394434441010184817)
              ·
                refine ⟨11041849045825830757638613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14722465394434441010184817 11041849045825830757638613)
                ·
                  refine ⟨258793337011542908382155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11041849045825830757638613 258793337011542908382155)
                  ·
                    rfl

theorem cell23_4535984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 6, 2, 7].length) (baseStart_4535984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4535984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4535984 prefixEnd_4535984 := by exact prefixLift 4535984
  have htrace : WordTrace (prefixWord ++ tailWord_4535984) baseStart_4535984 baseEnd_4535984 := by
    simpa [prefixWord, tailWord_4535984, baseEnd_4535984] using wordTrace_append hprefix tailTrace_4535984
  have hstable : (prefixWord ++ tailWord_4535984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4535984).length < 2 ^ (prefixWord ++ tailWord_4535984).sum := by decide
  have hdescent : baseEnd_4535984 < baseStart_4535984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4535984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536018 : List Nat := [3, 2, 2, 2, 2, 3, 1, 1, 7]
def baseStart_4536018 : Nat := 118140960795 + 4536018 * 2 ^ 59
def prefixEnd_4536018 : Nat := 4983230072969 + 3 ^ 40 * 4536018 * 2
def baseEnd_4536018 : Nat := 258795276827348782490471

theorem tailTrace_4536018 : CollatzResearch.WordTrace tailWord_4536018 prefixEnd_4536018 258795276827348782490471 := by
  unfold tailWord_4536018
  simp only [CollatzResearch.WordTrace]
  refine ⟨41360542020197237760818177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 110294778720525967362181805 41360542020197237760818177)
  ·
    refine ⟨31020406515147928320613633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41360542020197237760818177 31020406515147928320613633)
    ·
      refine ⟨23265304886360946240460225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31020406515147928320613633 23265304886360946240460225)
      ·
        refine ⟨17448978664770709680345169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23265304886360946240460225 17448978664770709680345169)
        ·
          refine ⟨13086733998578032260258877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17448978664770709680345169 13086733998578032260258877)
          ·
            refine ⟨4907525249466762097597079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13086733998578032260258877 4907525249466762097597079)
            ·
              refine ⟨7361287874200143146395619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4907525249466762097597079 7361287874200143146395619)
              ·
                refine ⟨11041931811300214719593429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7361287874200143146395619 11041931811300214719593429)
                ·
                  refine ⟨258795276827348782490471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11041931811300214719593429 258795276827348782490471)
                  ·
                    rfl

theorem cell23_4536018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 1, 7].length) (baseStart_4536018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536018 prefixEnd_4536018 := by exact prefixLift 4536018
  have htrace : WordTrace (prefixWord ++ tailWord_4536018) baseStart_4536018 baseEnd_4536018 := by
    simpa [prefixWord, tailWord_4536018, baseEnd_4536018] using wordTrace_append hprefix tailTrace_4536018
  have hstable : (prefixWord ++ tailWord_4536018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536018).length < 2 ^ (prefixWord ++ tailWord_4536018).sum := by decide
  have hdescent : baseEnd_4536018 < baseStart_4536018 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536029 : List Nat := [1, 4, 3, 3, 1, 1, 1, 3, 2, 2, 2]
def baseStart_4536029 : Nat := 118140960795 + 4536029 * 2 ^ 59
def prefixEnd_4536029 : Nat := 4983230072969 + 3 ^ 40 * 4536029 * 2
def baseEnd_4536029 : Nat := 2329163139733338499376689

theorem tailTrace_4536029 : CollatzResearch.WordTrace tailWord_4536029 prefixEnd_4536029 2329163139733338499376689 := by
  unfold tailWord_4536029
  simp only [CollatzResearch.WordTrace]
  refine ⟨165442569283749099921923141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110295046189166066614615427 165442569283749099921923141)
  ·
    refine ⟨31020481740702956235360589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165442569283749099921923141 31020481740702956235360589)
    ·
      refine ⟨11632680652763608588260221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31020481740702956235360589 11632680652763608588260221)
      ·
        refine ⟨4362255244786353220597583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11632680652763608588260221 4362255244786353220597583)
        ·
          refine ⟨6543382867179529830896375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4362255244786353220597583 6543382867179529830896375)
          ·
            refine ⟨9815074300769294746344563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6543382867179529830896375 9815074300769294746344563)
            ·
              refine ⟨14722611451153942119516845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9815074300769294746344563 14722611451153942119516845)
              ·
                refine ⟨5520979294182728294818817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14722611451153942119516845 5520979294182728294818817)
                ·
                  refine ⟨4140734470637046221114113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5520979294182728294818817 4140734470637046221114113)
                  ·
                    refine ⟨3105550852977784665835585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4140734470637046221114113 3105550852977784665835585)
                    ·
                      refine ⟨2329163139733338499376689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3105550852977784665835585 2329163139733338499376689)
                      ·
                        rfl

theorem cell23_4536029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_4536029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536029 prefixEnd_4536029 := by exact prefixLift 4536029
  have htrace : WordTrace (prefixWord ++ tailWord_4536029) baseStart_4536029 baseEnd_4536029 := by
    simpa [prefixWord, tailWord_4536029, baseEnd_4536029] using wordTrace_append hprefix tailTrace_4536029
  have hstable : (prefixWord ++ tailWord_4536029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536029).length < 2 ^ (prefixWord ++ tailWord_4536029).sum := by decide
  have hdescent : baseEnd_4536029 < baseStart_4536029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536044 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 2, 8]
def baseStart_4536044 : Nat := 118140960795 + 4536044 * 2 ^ 59
def prefixEnd_4536044 : Nat := 4983230072969 + 3 ^ 40 * 4536044 * 2
def baseEnd_4536044 : Nat := 776390280647718646896373

theorem tailTrace_4536044 : CollatzResearch.WordTrace tailWord_4536044 prefixEnd_4536044 776390280647718646896373 := by
  unfold tailWord_4536044
  simp only [CollatzResearch.WordTrace]
  refine ⟨82721558189347378741859593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 110295410919129838322479457 82721558189347378741859593)
  ·
    refine ⟨62041168642010534056394695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82721558189347378741859593 62041168642010534056394695)
    ·
      refine ⟨93061752963015801084592043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62041168642010534056394695 93061752963015801084592043)
      ·
        refine ⟨139592629444523701626888065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93061752963015801084592043 139592629444523701626888065)
        ·
          refine ⟨104694472083392776220166049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139592629444523701626888065 104694472083392776220166049)
          ·
            refine ⟨78520854062544582165124537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104694472083392776220166049 78520854062544582165124537)
            ·
              refine ⟨58890640546908436623843403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78520854062544582165124537 58890640546908436623843403)
              ·
                refine ⟨88335960820362654935765105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58890640546908436623843403 88335960820362654935765105)
                ·
                  refine ⟨66251970615271991201823829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 88335960820362654935765105 66251970615271991201823829)
                  ·
                    refine ⟨776390280647718646896373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66251970615271991201823829 776390280647718646896373)
                    ·
                      rfl

theorem cell23_4536044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 8].length) (baseStart_4536044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536044 prefixEnd_4536044 := by exact prefixLift 4536044
  have htrace : WordTrace (prefixWord ++ tailWord_4536044) baseStart_4536044 baseEnd_4536044 := by
    simpa [prefixWord, tailWord_4536044, baseEnd_4536044] using wordTrace_append hprefix tailTrace_4536044
  have hstable : (prefixWord ++ tailWord_4536044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536044).length < 2 ^ (prefixWord ++ tailWord_4536044).sum := by decide
  have hdescent : baseEnd_4536044 < baseStart_4536044 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536051 : List Nat := [1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 4]
def baseStart_4536051 : Nat := 118140960795 + 4536051 * 2 ^ 59
def prefixEnd_4536051 : Nat := 4983230072969 + 3 ^ 40 * 4536051 * 2
def baseEnd_4536051 : Nat := 2329174436307737413301587

theorem tailTrace_4536051 : CollatzResearch.WordTrace tailWord_4536051 prefixEnd_4536051 2329174436307737413301587 := by
  unfold tailWord_4536051
  simp only [CollatzResearch.WordTrace]
  refine ⟨165443371689669397679224007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110295581126446265119482671 165443371689669397679224007)
  ·
    refine ⟨248165057534504096518836011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 165443371689669397679224007 248165057534504096518836011)
    ·
      refine ⟨372247586301756144778254017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 248165057534504096518836011 372247586301756144778254017)
      ·
        refine ⟨279185689726317108583690513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 372247586301756144778254017 279185689726317108583690513)
        ·
          refine ⟨209389267294737831437767885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279185689726317108583690513 209389267294737831437767885)
          ·
            refine ⟨78520975235526686789162957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209389267294737831437767885 78520975235526686789162957)
            ·
              refine ⟨29445365713322507545936109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78520975235526686789162957 29445365713322507545936109)
              ·
                refine ⟨11042012142495940329726041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29445365713322507545936109 11042012142495940329726041)
                ·
                  refine ⟨8281509106871955247294531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11042012142495940329726041 8281509106871955247294531)
                  ·
                    refine ⟨12422263660307932870941797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8281509106871955247294531 12422263660307932870941797)
                    ·
                      refine ⟨2329174436307737413301587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12422263660307932870941797 2329174436307737413301587)
                      ·
                        rfl

theorem cell23_4536051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 2, 1, 4].length) (baseStart_4536051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536051 prefixEnd_4536051 := by exact prefixLift 4536051
  have htrace : WordTrace (prefixWord ++ tailWord_4536051) baseStart_4536051 baseEnd_4536051 := by
    simpa [prefixWord, tailWord_4536051, baseEnd_4536051] using wordTrace_append hprefix tailTrace_4536051
  have hstable : (prefixWord ++ tailWord_4536051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536051).length < 2 ^ (prefixWord ++ tailWord_4536051).sum := by decide
  have hdescent : baseEnd_4536051 < baseStart_4536051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4536061 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 7, 4]
def baseStart_4536061 : Nat := 118140960795 + 4536061 * 2 ^ 59
def prefixEnd_4536061 : Nat := 4983230072969 + 3 ^ 40 * 4536061 * 2
def baseEnd_4536061 : Nat := 776393190371427458058847

theorem tailTrace_4536061 : CollatzResearch.WordTrace tailWord_4536061 prefixEnd_4536061 776393190371427458058847 := by
  unfold tailWord_4536061
  simp only [CollatzResearch.WordTrace]
  refine ⟨165443736419633169387088037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 110295824279755446258058691 165443736419633169387088037)
  ·
    refine ⟨31020700578681219260079007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 165443736419633169387088037 31020700578681219260079007)
    ·
      refine ⟨46531050868021828890118511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31020700578681219260079007 46531050868021828890118511)
      ·
        refine ⟨69796576302032743335177767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46531050868021828890118511 69796576302032743335177767)
        ·
          refine ⟨104694864453049115002766651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69796576302032743335177767 104694864453049115002766651)
          ·
            refine ⟨157042296679573672504149977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104694864453049115002766651 157042296679573672504149977)
            ·
              refine ⟨117781722509680254378112483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157042296679573672504149977 117781722509680254378112483)
              ·
                refine ⟨176672583764520381567168725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117781722509680254378112483 176672583764520381567168725)
                ·
                  refine ⟨4140763681980946442980517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 176672583764520381567168725 4140763681980946442980517)
                  ·
                    refine ⟨776393190371427458058847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4140763681980946442980517 776393190371427458058847)
                    ·
                      rfl

theorem cell23_4536061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 7, 4].length) (baseStart_4536061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4536061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4536061 prefixEnd_4536061 := by exact prefixLift 4536061
  have htrace : WordTrace (prefixWord ++ tailWord_4536061) baseStart_4536061 baseEnd_4536061 := by
    simpa [prefixWord, tailWord_4536061, baseEnd_4536061] using wordTrace_append hprefix tailTrace_4536061
  have hstable : (prefixWord ++ tailWord_4536061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4536061).length < 2 ^ (prefixWord ++ tailWord_4536061).sum := by decide
  have hdescent : baseEnd_4536061 < baseStart_4536061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4536061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
