import V185TrunkScan23Chunk0104

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_621237 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 3, 5]
def baseStart_621237 : Nat := 118140960795 + 621237 * 2 ^ 59
def prefixEnd_621237 : Nat := 4983230072969 + 3 ^ 40 * 621237 * 2
def baseEnd_621237 : Nat := 106331060452430380360163

theorem tailTrace_621237 : CollatzResearch.WordTrace tailWord_621237 prefixEnd_621237 106331060452430380360163 := by
  unfold tailWord_621237
  simp only [CollatzResearch.WordTrace]
  refine ⟨22658374850371922677749965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15105583233581281785166643 22658374850371922677749965)
  ·
    refine ⟨8496890568889471004156237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22658374850371922677749965 8496890568889471004156237)
    ·
      refine ⟨3186333963333551626558589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8496890568889471004156237 3186333963333551626558589)
      ·
        refine ⟨1194875236250081859959471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3186333963333551626558589 1194875236250081859959471)
        ·
          refine ⟨1792312854375122789939207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1194875236250081859959471 1792312854375122789939207)
          ·
            refine ⟨2688469281562684184908811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792312854375122789939207 2688469281562684184908811)
            ·
              refine ⟨4032703922344026277363217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2688469281562684184908811 4032703922344026277363217)
              ·
                refine ⟨3024527941758019708022413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4032703922344026277363217 3024527941758019708022413)
                ·
                  refine ⟨1134197978159257390508405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3024527941758019708022413 1134197978159257390508405)
                  ·
                    refine ⟨106331060452430380360163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1134197978159257390508405 106331060452430380360163)
                    ·
                      rfl

theorem cell23_621237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_621237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621237 prefixEnd_621237 := by exact prefixLift 621237
  have htrace : WordTrace (prefixWord ++ tailWord_621237) baseStart_621237 baseEnd_621237 := by
    simpa [prefixWord, tailWord_621237, baseEnd_621237] using wordTrace_append hprefix tailTrace_621237
  have hstable : (prefixWord ++ tailWord_621237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621237).length < 2 ^ (prefixWord ++ tailWord_621237).sum := by decide
  have hdescent : baseEnd_621237 < baseStart_621237 := by decide
  rcases family_descends (prefixWord ++ tailWord_621237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621274 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2]
def baseStart_621274 : Nat := 118140960795 + 621274 * 2 ^ 59
def prefixEnd_621274 : Nat := 4983230072969 + 3 ^ 40 * 621274 * 2
def baseEnd_621274 : Nat := 319012180141507496317819

theorem tailTrace_621274 : CollatzResearch.WordTrace tailWord_621274 prefixEnd_621274 319012180141507496317819 := by
  unfold tailWord_621274
  simp only [CollatzResearch.WordTrace]
  refine ⟨5664931087809469499211719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15106482900825251997897917 5664931087809469499211719)
  ·
    refine ⟨8497396631714204248817579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5664931087809469499211719 8497396631714204248817579)
    ·
      refine ⟨12746094947571306373226369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8497396631714204248817579 12746094947571306373226369)
      ·
        refine ⟨9559571210678479779919777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12746094947571306373226369 9559571210678479779919777)
        ·
          refine ⟨7169678408008859834939833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9559571210678479779919777 7169678408008859834939833)
          ·
            refine ⟨5377258806006644876204875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7169678408008859834939833 5377258806006644876204875)
            ·
              refine ⟨8065888209009967314307313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5377258806006644876204875 8065888209009967314307313)
              ·
                refine ⟨6049416156757475485730485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8065888209009967314307313 6049416156757475485730485)
                ·
                  refine ⟨567132764696013326787233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 6049416156757475485730485 567132764696013326787233)
                  ·
                    refine ⟨425349573522009995090425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 567132764696013326787233 425349573522009995090425)
                    ·
                      refine ⟨319012180141507496317819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 425349573522009995090425 319012180141507496317819)
                      ·
                        rfl

theorem cell23_621274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 5, 2, 2].length) (baseStart_621274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621274 prefixEnd_621274 := by exact prefixLift 621274
  have htrace : WordTrace (prefixWord ++ tailWord_621274) baseStart_621274 baseEnd_621274 := by
    simpa [prefixWord, tailWord_621274, baseEnd_621274] using wordTrace_append hprefix tailTrace_621274
  have hstable : (prefixWord ++ tailWord_621274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621274).length < 2 ^ (prefixWord ++ tailWord_621274).sum := by decide
  have hdescent : baseEnd_621274 < baseStart_621274 := by decide
  rcases family_descends (prefixWord ++ tailWord_621274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621284 : List Nat := [2, 3, 1, 1, 1, 4, 3, 2, 2, 4]
def baseStart_621284 : Nat := 118140960795 + 621284 * 2 ^ 59
def prefixEnd_621284 : Nat := 4983230072969 + 3 ^ 40 * 621284 * 2
def baseEnd_621284 : Nat := 106339104982684152397591

theorem tailTrace_621284 : CollatzResearch.WordTrace tailWord_621284 prefixEnd_621284 106339104982684152397591 := by
  unfold tailWord_621284
  simp only [CollatzResearch.WordTrace]
  refine ⟨11330044540600824852355453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15106726054134433136473937 11330044540600824852355453)
  ·
    refine ⟨4248766702725309319633295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11330044540600824852355453 4248766702725309319633295)
    ·
      refine ⟨6373150054087963979449943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4248766702725309319633295 6373150054087963979449943)
      ·
        refine ⟨9559725081131945969174915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6373150054087963979449943 9559725081131945969174915)
        ·
          refine ⟨14339587621697918953762373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9559725081131945969174915 14339587621697918953762373)
          ·
            refine ⟨2688672679068359803830445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14339587621697918953762373 2688672679068359803830445)
            ·
              refine ⟨1008252254650634926436417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2688672679068359803830445 1008252254650634926436417)
              ·
                refine ⟨756189190987976194827313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1008252254650634926436417 756189190987976194827313)
                ·
                  refine ⟨567141893240982146120485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 756189190987976194827313 567141893240982146120485)
                  ·
                    refine ⟨106339104982684152397591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 567141893240982146120485 106339104982684152397591)
                    ·
                      rfl

theorem cell23_621284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 2, 4].length) (baseStart_621284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621284 prefixEnd_621284 := by exact prefixLift 621284
  have htrace : WordTrace (prefixWord ++ tailWord_621284) baseStart_621284 baseEnd_621284 := by
    simpa [prefixWord, tailWord_621284, baseEnd_621284] using wordTrace_append hprefix tailTrace_621284
  have hstable : (prefixWord ++ tailWord_621284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621284).length < 2 ^ (prefixWord ++ tailWord_621284).sum := by decide
  have hdescent : baseEnd_621284 < baseStart_621284 := by decide
  rcases family_descends (prefixWord ++ tailWord_621284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621290 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_621290 : Nat := 118140960795 + 621290 * 2 ^ 59
def prefixEnd_621290 : Nat := 4983230072969 + 3 ^ 40 * 621290 * 2
def baseEnd_621290 : Nat := 319020395831979433717745

theorem tailTrace_621290 : CollatzResearch.WordTrace tailWord_621290 prefixEnd_621290 319020395831979433717745 := by
  unfold tailWord_621290
  simp only [CollatzResearch.WordTrace]
  refine ⟨5665076979794978182357331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15106871946119941819619549 5665076979794978182357331)
  ·
    refine ⟨8497615469692467273535997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5665076979794978182357331 8497615469692467273535997)
    ·
      refine ⟨3186605801134675227575999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8497615469692467273535997 3186605801134675227575999)
      ·
        refine ⟨4779908701702012841363999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3186605801134675227575999 4779908701702012841363999)
        ·
          refine ⟨7169863052553019262045999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4779908701702012841363999 7169863052553019262045999)
          ·
            refine ⟨10754794578829528893068999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7169863052553019262045999 10754794578829528893068999)
            ·
              refine ⟨16132191868244293339603499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10754794578829528893068999 16132191868244293339603499)
              ·
                refine ⟨24198287802366440009405249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16132191868244293339603499 24198287802366440009405249)
                ·
                  refine ⟨18148715851774830007053937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24198287802366440009405249 18148715851774830007053937)
                  ·
                    refine ⟨13611536888831122505290453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18148715851774830007053937 13611536888831122505290453)
                    ·
                      refine ⟨319020395831979433717745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13611536888831122505290453 319020395831979433717745)
                      ·
                        rfl

theorem cell23_621290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_621290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621290 prefixEnd_621290 := by exact prefixLift 621290
  have htrace : WordTrace (prefixWord ++ tailWord_621290) baseStart_621290 baseEnd_621290 := by
    simpa [prefixWord, tailWord_621290, baseEnd_621290] using wordTrace_append hprefix tailTrace_621290
  have hstable : (prefixWord ++ tailWord_621290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621290).length < 2 ^ (prefixWord ++ tailWord_621290).sum := by decide
  have hdescent : baseEnd_621290 < baseStart_621290 := by decide
  rcases family_descends (prefixWord ++ tailWord_621290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621314 : List Nat := [3, 4, 1, 1, 1, 2, 4, 7]
def baseStart_621314 : Nat := 118140960795 + 621314 * 2 ^ 59
def prefixEnd_621314 : Nat := 4983230072969 + 3 ^ 40 * 621314 * 2
def baseEnd_621314 : Nat := 11816026643247679252505

theorem tailTrace_621314 : CollatzResearch.WordTrace tailWord_621314 prefixEnd_621314 11816026643247679252505 := by
  unfold tailWord_621314
  simp only [CollatzResearch.WordTrace]
  refine ⟨5665295817773241207075749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15107455514061976552201997 5665295817773241207075749)
  ·
    refine ⟨1062242965832482726326703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5665295817773241207075749 1062242965832482726326703)
    ·
      refine ⟨1593364448748724089490055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1062242965832482726326703 1593364448748724089490055)
      ·
        refine ⟨2390046673123086134235083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1593364448748724089490055 2390046673123086134235083)
        ·
          refine ⟨3585070009684629201352625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2390046673123086134235083 3585070009684629201352625)
          ·
            refine ⟨2688802507263471901014469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3585070009684629201352625 2688802507263471901014469)
            ·
              refine ⟨504150470111900981440213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2688802507263471901014469 504150470111900981440213)
              ·
                refine ⟨11816026643247679252505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 504150470111900981440213 11816026643247679252505)
                ·
                  rfl

theorem cell23_621314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 7].length) (baseStart_621314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621314 prefixEnd_621314 := by exact prefixLift 621314
  have htrace : WordTrace (prefixWord ++ tailWord_621314) baseStart_621314 baseEnd_621314 := by
    simpa [prefixWord, tailWord_621314, baseEnd_621314] using wordTrace_append hprefix tailTrace_621314
  have hstable : (prefixWord ++ tailWord_621314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621314).length < 2 ^ (prefixWord ++ tailWord_621314).sum := by decide
  have hdescent : baseEnd_621314 < baseStart_621314 := by decide
  rcases family_descends (prefixWord ++ tailWord_621314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621317 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 2, 7, 2]
def baseStart_621317 : Nat := 118140960795 + 621317 * 2 ^ 59
def prefixEnd_621317 : Nat := 4983230072969 + 3 ^ 40 * 621317 * 2
def baseEnd_621317 : Nat := 319034259809650828080121

theorem tailTrace_621317 : CollatzResearch.WordTrace tailWord_621317 prefixEnd_621317 319034259809650828080121 := by
  unfold tailWord_621317
  simp only [CollatzResearch.WordTrace]
  refine ⟨22661292690082096340662205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15107528460054730893774803 22661292690082096340662205)
  ·
    refine ⟨8497984758780786127748327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22661292690082096340662205 8497984758780786127748327)
    ·
      refine ⟨12746977138171179191622491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8497984758780786127748327 12746977138171179191622491)
      ·
        refine ⟨19120465707256768787433737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12746977138171179191622491 19120465707256768787433737)
        ·
          refine ⟨14340349280442576590575303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19120465707256768787433737 14340349280442576590575303)
          ·
            refine ⟨21510523920663864885862955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14340349280442576590575303 21510523920663864885862955)
            ·
              refine ⟨32265785880995797328794433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21510523920663864885862955 32265785880995797328794433)
              ·
                refine ⟨24199339410746847996595825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32265785880995797328794433 24199339410746847996595825)
                ·
                  refine ⟨18149504558060135997446869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24199339410746847996595825 18149504558060135997446869)
                  ·
                    refine ⟨425379013079534437440161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18149504558060135997446869 425379013079534437440161)
                    ·
                      refine ⟨319034259809650828080121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 425379013079534437440161 319034259809650828080121)
                      ·
                        rfl

theorem cell23_621317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 2, 7, 2].length) (baseStart_621317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621317 prefixEnd_621317 := by exact prefixLift 621317
  have htrace : WordTrace (prefixWord ++ tailWord_621317) baseStart_621317 baseEnd_621317 := by
    simpa [prefixWord, tailWord_621317, baseEnd_621317] using wordTrace_append hprefix tailTrace_621317
  have hstable : (prefixWord ++ tailWord_621317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621317).length < 2 ^ (prefixWord ++ tailWord_621317).sum := by decide
  have hdescent : baseEnd_621317 < baseStart_621317 := by decide
  rcases family_descends (prefixWord ++ tailWord_621317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621358 : List Nat := [4, 1, 3, 2, 1, 2, 1, 3, 2, 1, 3]
def baseStart_621358 : Nat := 118140960795 + 621358 * 2 ^ 59
def prefixEnd_621358 : Nat := 4983230072969 + 3 ^ 40 * 621358 * 2
def baseEnd_621358 : Nat := 319055312516485167667433

theorem tailTrace_621358 : CollatzResearch.WordTrace tailWord_621358 prefixEnd_621358 319055312516485167667433 := by
  unfold tailWord_621358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2832848510366695042863091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15108525388622373561936485 2832848510366695042863091)
  ·
    refine ⟨4249272765550042564294637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2832848510366695042863091 4249272765550042564294637)
    ·
      refine ⟨1593477287081265961610489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4249272765550042564294637 1593477287081265961610489)
      ·
        refine ⟨1195107965310949471207867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1593477287081265961610489 1195107965310949471207867)
        ·
          refine ⟨1792661947966424206811801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195107965310949471207867 1792661947966424206811801)
          ·
            refine ⟨1344496460974818155108851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1792661947966424206811801 1344496460974818155108851)
            ·
              refine ⟨2016744691462227232663277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1344496460974818155108851 2016744691462227232663277)
              ·
                refine ⟨756279259298335212248729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2016744691462227232663277 756279259298335212248729)
                ·
                  refine ⟨567209444473751409186547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 756279259298335212248729 567209444473751409186547)
                  ·
                    refine ⟨850814166710627113779821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 567209444473751409186547 850814166710627113779821)
                    ·
                      refine ⟨319055312516485167667433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 850814166710627113779821 319055312516485167667433)
                      ·
                        rfl

theorem cell23_621358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_621358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621358 prefixEnd_621358 := by exact prefixLift 621358
  have htrace : WordTrace (prefixWord ++ tailWord_621358) baseStart_621358 baseEnd_621358 := by
    simpa [prefixWord, tailWord_621358, baseEnd_621358] using wordTrace_append hprefix tailTrace_621358
  have hstable : (prefixWord ++ tailWord_621358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621358).length < 2 ^ (prefixWord ++ tailWord_621358).sum := by decide
  have hdescent : baseEnd_621358 < baseStart_621358 := by decide
  rcases family_descends (prefixWord ++ tailWord_621358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621360 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 6]
def baseStart_621360 : Nat := 118140960795 + 621360 * 2 ^ 59
def prefixEnd_621360 : Nat := 4983230072969 + 3 ^ 40 * 621360 * 2
def baseEnd_621360 : Nat := 319056339477794159842423

theorem tailTrace_621360 : CollatzResearch.WordTrace tailWord_621360 prefixEnd_621360 319056339477794159842423 := by
  unfold tailWord_621360
  simp only [CollatzResearch.WordTrace]
  refine ⟨11331430514463157342238767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15108574019284209789651689 11331430514463157342238767)
  ·
    refine ⟨16997145771694736013358151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11331430514463157342238767 16997145771694736013358151)
    ·
      refine ⟨25495718657542104020037227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16997145771694736013358151 25495718657542104020037227)
      ·
        refine ⟨38243577986313156030055841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25495718657542104020037227 38243577986313156030055841)
        ·
          refine ⟨28682683489734867022541881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38243577986313156030055841 28682683489734867022541881)
          ·
            refine ⟨21512012617301150266906411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28682683489734867022541881 21512012617301150266906411)
            ·
              refine ⟨32268018925951725400359617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21512012617301150266906411 32268018925951725400359617)
              ·
                refine ⟨24201014194463794050269713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32268018925951725400359617 24201014194463794050269713)
                ·
                  refine ⟨18150760645847845537702285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24201014194463794050269713 18150760645847845537702285)
                  ·
                    refine ⟨6806535242192942076638357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18150760645847845537702285 6806535242192942076638357)
                    ·
                      refine ⟨319056339477794159842423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6806535242192942076638357 319056339477794159842423)
                      ·
                        rfl

theorem cell23_621360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 6].length) (baseStart_621360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621360 prefixEnd_621360 := by exact prefixLift 621360
  have htrace : WordTrace (prefixWord ++ tailWord_621360) baseStart_621360 baseEnd_621360 := by
    simpa [prefixWord, tailWord_621360, baseEnd_621360] using wordTrace_append hprefix tailTrace_621360
  have hstable : (prefixWord ++ tailWord_621360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621360).length < 2 ^ (prefixWord ++ tailWord_621360).sum := by decide
  have hdescent : baseEnd_621360 < baseStart_621360 := by decide
  rcases family_descends (prefixWord ++ tailWord_621360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621471 : List Nat := [1, 1, 2, 5, 2, 1, 2, 1, 2, 4, 2]
def baseStart_621471 : Nat := 118140960795 + 621471 * 2 ^ 59
def prefixEnd_621471 : Nat := 4983230072969 + 3 ^ 40 * 621471 * 2
def baseEnd_621471 : Nat := 319113335830443225554413

theorem tailTrace_621471 : CollatzResearch.WordTrace tailWord_621471 prefixEnd_621471 319113335830443225554413 := by
  unfold tailWord_621471
  simp only [CollatzResearch.WordTrace]
  refine ⟨22666909531524180641768267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15111273021016120427845511 22666909531524180641768267)
  ·
    refine ⟨34000364297286270962652401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22666909531524180641768267 34000364297286270962652401)
    ·
      refine ⟨25500273222964703221989301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34000364297286270962652401 25500273222964703221989301)
      ·
        refine ⟨2390650614652940927061497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25500273222964703221989301 2390650614652940927061497)
        ·
          refine ⟨1792987960989705695296123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2390650614652940927061497 1792987960989705695296123)
          ·
            refine ⟨2689481941484558542944185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1792987960989705695296123 2689481941484558542944185)
            ·
              refine ⟨2017111456113418907208139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2689481941484558542944185 2017111456113418907208139)
              ·
                refine ⟨3025667184170128360812209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2017111456113418907208139 3025667184170128360812209)
                ·
                  refine ⟨2269250388127596270609157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3025667184170128360812209 2269250388127596270609157)
                  ·
                    refine ⟨425484447773924300739217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2269250388127596270609157 425484447773924300739217)
                    ·
                      refine ⟨319113335830443225554413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 425484447773924300739217 319113335830443225554413)
                      ·
                        rfl

theorem cell23_621471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_621471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621471 prefixEnd_621471 := by exact prefixLift 621471
  have htrace : WordTrace (prefixWord ++ tailWord_621471) baseStart_621471 baseEnd_621471 := by
    simpa [prefixWord, tailWord_621471, baseEnd_621471] using wordTrace_append hprefix tailTrace_621471
  have hstable : (prefixWord ++ tailWord_621471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621471).length < 2 ^ (prefixWord ++ tailWord_621471).sum := by decide
  have hdescent : baseEnd_621471 < baseStart_621471 := by decide
  rcases family_descends (prefixWord ++ tailWord_621471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621547 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 5]
def baseStart_621547 : Nat := 118140960795 + 621547 * 2 ^ 59
def prefixEnd_621547 : Nat := 4983230072969 + 3 ^ 40 * 621547 * 2
def baseEnd_621547 : Nat := 319152360360184928204063

theorem tailTrace_621547 : CollatzResearch.WordTrace tailWord_621547 prefixEnd_621547 319152360360184928204063 := by
  unfold tailWord_621547
  simp only [CollatzResearch.WordTrace]
  refine ⟨22669681479248845621534895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15113120986165897081023263 22669681479248845621534895)
  ·
    refine ⟨34004522218873268432302343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22669681479248845621534895 34004522218873268432302343)
    ·
      refine ⟨51006783328309902648453515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34004522218873268432302343 51006783328309902648453515)
      ·
        refine ⟨76510174992464853972680273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51006783328309902648453515 76510174992464853972680273)
        ·
          refine ⟨57382631244348640479510205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76510174992464853972680273 57382631244348640479510205)
          ·
            refine ⟨21518486716630740179816327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57382631244348640479510205 21518486716630740179816327)
            ·
              refine ⟨32277730074946110269724491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21518486716630740179816327 32277730074946110269724491)
              ·
                refine ⟨48416595112419165404586737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32277730074946110269724491 48416595112419165404586737)
                ·
                  refine ⟨36312446334314374053440053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48416595112419165404586737 36312446334314374053440053)
                  ·
                    refine ⟨3404291843841972567510005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36312446334314374053440053 3404291843841972567510005)
                    ·
                      refine ⟨319152360360184928204063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3404291843841972567510005 319152360360184928204063)
                      ·
                        rfl

theorem cell23_621547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 5, 5].length) (baseStart_621547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621547 prefixEnd_621547 := by exact prefixLift 621547
  have htrace : WordTrace (prefixWord ++ tailWord_621547) baseStart_621547 baseEnd_621547 := by
    simpa [prefixWord, tailWord_621547, baseEnd_621547] using wordTrace_append hprefix tailTrace_621547
  have hstable : (prefixWord ++ tailWord_621547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621547).length < 2 ^ (prefixWord ++ tailWord_621547).sum := by decide
  have hdescent : baseEnd_621547 < baseStart_621547 := by decide
  rcases family_descends (prefixWord ++ tailWord_621547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621591 : List Nat := [1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 4]
def baseStart_621591 : Nat := 118140960795 + 621591 * 2 ^ 59
def prefixEnd_621591 : Nat := 4983230072969 + 3 ^ 40 * 621591 * 2
def baseEnd_621591 : Nat := 319174953508982756053861

theorem tailTrace_621591 : CollatzResearch.WordTrace tailWord_621591 prefixEnd_621591 319174953508982756053861 := by
  unfold tailWord_621591
  simp only [CollatzResearch.WordTrace]
  refine ⟨22671286291089441136136627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15114190860726294090757751 22671286291089441136136627)
  ·
    refine ⟨34006929436634161704204941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22671286291089441136136627 34006929436634161704204941)
    ·
      refine ⟨12752598538737810639076853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34006929436634161704204941 12752598538737810639076853)
      ·
        refine ⟨1195556113006669747413455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12752598538737810639076853 1195556113006669747413455)
        ·
          refine ⟨1793334169510004621120183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195556113006669747413455 1793334169510004621120183)
          ·
            refine ⟨2690001254265006931680275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1793334169510004621120183 2690001254265006931680275)
            ·
              refine ⟨4035001881397510397520413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2690001254265006931680275 4035001881397510397520413)
              ·
                refine ⟨1513125705524066399070155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4035001881397510397520413 1513125705524066399070155)
                ·
                  refine ⟨2269688558286099598605233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1513125705524066399070155 2269688558286099598605233)
                  ·
                    refine ⟨1702266418714574698953925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2269688558286099598605233 1702266418714574698953925)
                    ·
                      refine ⟨319174953508982756053861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1702266418714574698953925 319174953508982756053861)
                      ·
                        rfl

theorem cell23_621591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_621591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621591 prefixEnd_621591 := by exact prefixLift 621591
  have htrace : WordTrace (prefixWord ++ tailWord_621591) baseStart_621591 baseEnd_621591 := by
    simpa [prefixWord, tailWord_621591, baseEnd_621591] using wordTrace_append hprefix tailTrace_621591
  have hstable : (prefixWord ++ tailWord_621591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621591).length < 2 ^ (prefixWord ++ tailWord_621591).sum := by decide
  have hdescent : baseEnd_621591 < baseStart_621591 := by decide
  rcases family_descends (prefixWord ++ tailWord_621591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621601 : List Nat := [1, 2, 3, 2, 3, 2, 3, 7]
def baseStart_621601 : Nat := 118140960795 + 621601 * 2 ^ 59
def prefixEnd_621601 : Nat := 4983230072969 + 3 ^ 40 * 621601 * 2
def baseEnd_621601 : Nat := 11821484752426952478845

theorem tailTrace_621601 : CollatzResearch.WordTrace tailWord_621601 prefixEnd_621601 11821484752426952478845 := by
  unfold tailWord_621601
  simp only [CollatzResearch.WordTrace]
  refine ⟨22671651021053212844000657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15114434014035475229333771 22671651021053212844000657)
  ·
    refine ⟨17003738265789909633000493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22671651021053212844000657 17003738265789909633000493)
    ·
      refine ⟨6376401849671216112375185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17003738265789909633000493 6376401849671216112375185)
      ·
        refine ⟨4782301387253412084281389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6376401849671216112375185 4782301387253412084281389)
        ·
          refine ⟨1793363020220029531605521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4782301387253412084281389 1793363020220029531605521)
          ·
            refine ⟨1345022265165022148704141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1793363020220029531605521 1345022265165022148704141)
            ·
              refine ⟨504383349436883305764053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1345022265165022148704141 504383349436883305764053)
              ·
                refine ⟨11821484752426952478845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 504383349436883305764053 11821484752426952478845)
                ·
                  rfl

theorem cell23_621601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 7].length) (baseStart_621601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621601 prefixEnd_621601 := by exact prefixLift 621601
  have htrace : WordTrace (prefixWord ++ tailWord_621601) baseStart_621601 baseEnd_621601 := by
    simpa [prefixWord, tailWord_621601, baseEnd_621601] using wordTrace_append hprefix tailTrace_621601
  have hstable : (prefixWord ++ tailWord_621601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621601).length < 2 ^ (prefixWord ++ tailWord_621601).sum := by decide
  have hdescent : baseEnd_621601 < baseStart_621601 := by decide
  rcases family_descends (prefixWord ++ tailWord_621601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621611 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 4, 1, 3]
def baseStart_621611 : Nat := 118140960795 + 621611 * 2 ^ 59
def prefixEnd_621611 : Nat := 4983230072969 + 3 ^ 40 * 621611 * 2
def baseEnd_621611 : Nat := 319185223122072677803769

theorem tailTrace_621611 : CollatzResearch.WordTrace tailWord_621611 prefixEnd_621611 319185223122072677803769 := by
  unfold tailWord_621611
  simp only [CollatzResearch.WordTrace]
  refine ⟨22672015751016984551864687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15114677167344656367909791 22672015751016984551864687)
  ·
    refine ⟨34008023626525476827797031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22672015751016984551864687 34008023626525476827797031)
    ·
      refine ⟨51012035439788215241695547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34008023626525476827797031 51012035439788215241695547)
      ·
        refine ⟨76518053159682322862543321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51012035439788215241695547 76518053159682322862543321)
        ·
          refine ⟨57388539869761742146907491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76518053159682322862543321 57388539869761742146907491)
          ·
            refine ⟨86082809804642613220361237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57388539869761742146907491 86082809804642613220361237)
            ·
              refine ⟨4035131709592622494704433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86082809804642613220361237 4035131709592622494704433)
              ·
                refine ⟨3026348782194466871028325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4035131709592622494704433 3026348782194466871028325)
                ·
                  refine ⟨567440396661462538317811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3026348782194466871028325 567440396661462538317811)
                  ·
                    refine ⟨851160594992193807476717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 567440396661462538317811 851160594992193807476717)
                    ·
                      refine ⟨319185223122072677803769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 851160594992193807476717 319185223122072677803769)
                      ·
                        rfl

theorem cell23_621611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 1, 3].length) (baseStart_621611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621611 prefixEnd_621611 := by exact prefixLift 621611
  have htrace : WordTrace (prefixWord ++ tailWord_621611) baseStart_621611 baseEnd_621611 := by
    simpa [prefixWord, tailWord_621611, baseEnd_621611] using wordTrace_append hprefix tailTrace_621611
  have hstable : (prefixWord ++ tailWord_621611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621611).length < 2 ^ (prefixWord ++ tailWord_621611).sum := by decide
  have hdescent : baseEnd_621611 < baseStart_621611 := by decide
  rcases family_descends (prefixWord ++ tailWord_621611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621628 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 4, 1, 3]
def baseStart_621628 : Nat := 118140960795 + 621628 * 2 ^ 59
def prefixEnd_621628 : Nat := 4983230072969 + 3 ^ 40 * 621628 * 2
def baseEnd_621628 : Nat := 319193952293199111291191

theorem tailTrace_621628 : CollatzResearch.WordTrace tailWord_621628 prefixEnd_621628 319193952293199111291191 := by
  unfold tailWord_621628
  simp only [CollatzResearch.WordTrace]
  refine ⟨11336317895977698227616769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15115090527970264303489025 11336317895977698227616769)
  ·
    refine ⟨8502238421983273670712577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11336317895977698227616769 8502238421983273670712577)
    ·
      refine ⟨6376678816487455253034433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8502238421983273670712577 6376678816487455253034433)
      ·
        refine ⟨4782509112365591439775825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6376678816487455253034433 4782509112365591439775825)
        ·
          refine ⟨3586881834274193579831869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4782509112365591439775825 3586881834274193579831869)
          ·
            refine ⟨1345080687852822592436951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3586881834274193579831869 1345080687852822592436951)
            ·
              refine ⟨2017621031779233888655427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345080687852822592436951 2017621031779233888655427)
              ·
                refine ⟨3026431547668850832983141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2017621031779233888655427 3026431547668850832983141)
                ·
                  refine ⟨567455915187909531184339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3026431547668850832983141 567455915187909531184339)
                  ·
                    refine ⟨851183872781864296776509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 567455915187909531184339 851183872781864296776509)
                    ·
                      refine ⟨319193952293199111291191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 851183872781864296776509 319193952293199111291191)
                      ·
                        rfl

theorem cell23_621628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_621628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621628 prefixEnd_621628 := by exact prefixLift 621628
  have htrace : WordTrace (prefixWord ++ tailWord_621628) baseStart_621628 baseEnd_621628 := by
    simpa [prefixWord, tailWord_621628, baseEnd_621628] using wordTrace_append hprefix tailTrace_621628
  have hstable : (prefixWord ++ tailWord_621628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621628).length < 2 ^ (prefixWord ++ tailWord_621628).sum := by decide
  have hdescent : baseEnd_621628 < baseStart_621628 := by decide
  rcases family_descends (prefixWord ++ tailWord_621628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621645 : List Nat := [1, 6, 1, 1, 1, 4, 1, 1, 1, 3, 3]
def baseStart_621645 : Nat := 118140960795 + 621645 * 2 ^ 59
def prefixEnd_621645 : Nat := 4983230072969 + 3 ^ 40 * 621645 * 2
def baseEnd_621645 : Nat := 319202681464325544778613

theorem tailTrace_621645 : CollatzResearch.WordTrace tailWord_621645 prefixEnd_621645 319202681464325544778613 := by
  unfold tailWord_621645
  simp only [CollatzResearch.WordTrace]
  refine ⟨22673255832893808358602389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15115503888595872239068259 22673255832893808358602389)
  ·
    refine ⟨1062808867166897266809487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 22673255832893808358602389 1062808867166897266809487)
    ·
      refine ⟨1594213300750345900214231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1062808867166897266809487 1594213300750345900214231)
      ·
        refine ⟨2391319951125518850321347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1594213300750345900214231 2391319951125518850321347)
        ·
          refine ⟨3586979926688278275482021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2391319951125518850321347 3586979926688278275482021)
          ·
            refine ⟨672558736254052176652879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3586979926688278275482021 672558736254052176652879)
            ·
              refine ⟨1008838104381078264979319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672558736254052176652879 1008838104381078264979319)
              ·
                refine ⟨1513257156571617397468979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1008838104381078264979319 1513257156571617397468979)
                ·
                  refine ⟨2269885734857426096203469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1513257156571617397468979 2269885734857426096203469)
                  ·
                    refine ⟨851207150571534786076301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2269885734857426096203469 851207150571534786076301)
                    ·
                      refine ⟨319202681464325544778613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 851207150571534786076301 319202681464325544778613)
                      ·
                        rfl

theorem cell23_621645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 3, 3].length) (baseStart_621645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621645 prefixEnd_621645 := by exact prefixLift 621645
  have htrace : WordTrace (prefixWord ++ tailWord_621645) baseStart_621645 baseEnd_621645 := by
    simpa [prefixWord, tailWord_621645, baseEnd_621645] using wordTrace_append hprefix tailTrace_621645
  have hstable : (prefixWord ++ tailWord_621645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621645).length < 2 ^ (prefixWord ++ tailWord_621645).sum := by decide
  have hdescent : baseEnd_621645 < baseStart_621645 := by decide
  rcases family_descends (prefixWord ++ tailWord_621645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621662 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_621662 : Nat := 118140960795 + 621662 * 2 ^ 59
def prefixEnd_621662 : Nat := 4983230072969 + 3 ^ 40 * 621662 * 2
def baseEnd_621662 : Nat := 319211410635451978266035

theorem tailTrace_621662 : CollatzResearch.WordTrace tailWord_621662 prefixEnd_621662 319211410635451978266035 := by
  unfold tailWord_621662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2834234484229027532746405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15115917249221480174647493 2834234484229027532746405)
  ·
    refine ⟨531418965792942662389951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2834234484229027532746405 531418965792942662389951)
    ·
      refine ⟨797128448689413993584927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 531418965792942662389951 797128448689413993584927)
      ·
        refine ⟨1195692673034120990377391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797128448689413993584927 1195692673034120990377391)
        ·
          refine ⟨1793539009551181485566087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1195692673034120990377391 1793539009551181485566087)
          ·
            refine ⟨2690308514326772228349131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1793539009551181485566087 2690308514326772228349131)
            ·
              refine ⟨4035462771490158342523697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2690308514326772228349131 4035462771490158342523697)
              ·
                refine ⟨3026597078617618756892773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4035462771490158342523697 3026597078617618756892773)
                ·
                  refine ⟨567486952240803516917395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3026597078617618756892773 567486952240803516917395)
                  ·
                    refine ⟨851230428361205275376093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 567486952240803516917395 851230428361205275376093)
                    ·
                      refine ⟨319211410635451978266035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 851230428361205275376093 319211410635451978266035)
                      ·
                        rfl

theorem cell23_621662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_621662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621662 prefixEnd_621662 := by exact prefixLift 621662
  have htrace : WordTrace (prefixWord ++ tailWord_621662) baseStart_621662 baseEnd_621662 := by
    simpa [prefixWord, tailWord_621662, baseEnd_621662] using wordTrace_append hprefix tailTrace_621662
  have hstable : (prefixWord ++ tailWord_621662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621662).length < 2 ^ (prefixWord ++ tailWord_621662).sum := by decide
  have hdescent : baseEnd_621662 < baseStart_621662 := by decide
  rcases family_descends (prefixWord ++ tailWord_621662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621671 : List Nat := [1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_621671 : Nat := 118140960795 + 621671 * 2 ^ 59
def prefixEnd_621671 : Nat := 4983230072969 + 3 ^ 40 * 621671 * 2
def baseEnd_621671 : Nat := 319216031961342443053493

theorem tailTrace_621671 : CollatzResearch.WordTrace tailWord_621671 prefixEnd_621671 319216031961342443053493 := by
  unfold tailWord_621671
  simp only [CollatzResearch.WordTrace]
  refine ⟨22674204130799614799048867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15116136087199743199365911 22674204130799614799048867)
  ·
    refine ⟨34011306196199422198573301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22674204130799614799048867 34011306196199422198573301)
    ·
      refine ⟨3188559955893695831116247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34011306196199422198573301 3188559955893695831116247)
      ·
        refine ⟨4782839933840543746674371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3188559955893695831116247 4782839933840543746674371)
        ·
          refine ⟨7174259900760815620011557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4782839933840543746674371 7174259900760815620011557)
          ·
            refine ⟨1345173731392652928752167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7174259900760815620011557 1345173731392652928752167)
            ·
              refine ⟨2017760597088979393128251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345173731392652928752167 2017760597088979393128251)
              ·
                refine ⟨3026640895633469089692377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2017760597088979393128251 3026640895633469089692377)
                ·
                  refine ⟨2269980671725101817269283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3026640895633469089692377 2269980671725101817269283)
                  ·
                    refine ⟨3404971007587652725903925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2269980671725101817269283 3404971007587652725903925)
                    ·
                      refine ⟨319216031961342443053493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3404971007587652725903925 319216031961342443053493)
                      ·
                        rfl

theorem cell23_621671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_621671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621671 prefixEnd_621671 := by exact prefixLift 621671
  have htrace : WordTrace (prefixWord ++ tailWord_621671) baseStart_621671 baseEnd_621671 := by
    simpa [prefixWord, tailWord_621671, baseEnd_621671] using wordTrace_append hprefix tailTrace_621671
  have hstable : (prefixWord ++ tailWord_621671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621671).length < 2 ^ (prefixWord ++ tailWord_621671).sum := by decide
  have hdescent : baseEnd_621671 < baseStart_621671 := by decide
  rcases family_descends (prefixWord ++ tailWord_621671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621691 : List Nat := [1, 1, 1, 1, 1, 4, 1, 8, 5]
def baseStart_621691 : Nat := 118140960795 + 621691 * 2 ^ 59
def prefixEnd_621691 : Nat := 4983230072969 + 3 ^ 40 * 621691 * 2
def baseEnd_621691 : Nat := 35469589063825818311489

theorem tailTrace_621691 : CollatzResearch.WordTrace tailWord_621691 prefixEnd_621691 35469589063825818311489 := by
  unfold tailWord_621691
  simp only [CollatzResearch.WordTrace]
  refine ⟨22674933590727158214776927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15116622393818105476517951 22674933590727158214776927)
  ·
    refine ⟨34012400386090737322165391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22674933590727158214776927 34012400386090737322165391)
    ·
      refine ⟨51018600579136105983248087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34012400386090737322165391 51018600579136105983248087)
      ·
        refine ⟨76527900868704158974872131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51018600579136105983248087 76527900868704158974872131)
        ·
          refine ⟨114791851303056238462308197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76527900868704158974872131 114791851303056238462308197)
          ·
            refine ⟨21523472119323044711682787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114791851303056238462308197 21523472119323044711682787)
            ·
              refine ⟨32285208178984567067524181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21523472119323044711682787 32285208178984567067524181)
              ·
                refine ⟨378342283347475395322549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 32285208178984567067524181 378342283347475395322549)
                ·
                  refine ⟨35469589063825818311489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 378342283347475395322549 35469589063825818311489)
                  ·
                    rfl

theorem cell23_621691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 5].length) (baseStart_621691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621691 prefixEnd_621691 := by exact prefixLift 621691
  have htrace : WordTrace (prefixWord ++ tailWord_621691) baseStart_621691 baseEnd_621691 := by
    simpa [prefixWord, tailWord_621691, baseEnd_621691] using wordTrace_append hprefix tailTrace_621691
  have hstable : (prefixWord ++ tailWord_621691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621691).length < 2 ^ (prefixWord ++ tailWord_621691).sum := by decide
  have hdescent : baseEnd_621691 < baseStart_621691 := by decide
  rcases family_descends (prefixWord ++ tailWord_621691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621778 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 1, 4, 3]
def baseStart_621778 : Nat := 118140960795 + 621778 * 2 ^ 59
def prefixEnd_621778 : Nat := 4983230072969 + 3 ^ 40 * 621778 * 2
def baseEnd_621778 : Nat := 319270974391373524415501

theorem tailTrace_621778 : CollatzResearch.WordTrace tailWord_621778 prefixEnd_621778 319270974391373524415501 := by
  unfold tailWord_621778
  simp only [CollatzResearch.WordTrace]
  refine ⟨5669526685352993018298497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15118737827607981382129325 5669526685352993018298497)
  ·
    refine ⟨4252145014014744763723873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5669526685352993018298497 4252145014014744763723873)
    ·
      refine ⟨3189108760511058572792905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4252145014014744763723873 3189108760511058572792905)
      ·
        refine ⟨2391831570383293929594679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3189108760511058572792905 2391831570383293929594679)
        ·
          refine ⟨3587747355574940894392019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2391831570383293929594679 3587747355574940894392019)
          ·
            refine ⟨5381621033362411341588029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3587747355574940894392019 5381621033362411341588029)
            ·
              refine ⟨2018107887510904253095511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5381621033362411341588029 2018107887510904253095511)
              ·
                refine ⟨3027161831266356379643267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018107887510904253095511 3027161831266356379643267)
                ·
                  refine ⟨4540742746899534569464901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3027161831266356379643267 4540742746899534569464901)
                  ·
                    refine ⟨851389265043662731774669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4540742746899534569464901 851389265043662731774669)
                    ·
                      refine ⟨319270974391373524415501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 851389265043662731774669 319270974391373524415501)
                      ·
                        rfl

theorem cell23_621778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_621778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621778 prefixEnd_621778 := by exact prefixLift 621778
  have htrace : WordTrace (prefixWord ++ tailWord_621778) baseStart_621778 baseEnd_621778 := by
    simpa [prefixWord, tailWord_621778, baseEnd_621778] using wordTrace_append hprefix tailTrace_621778
  have hstable : (prefixWord ++ tailWord_621778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621778).length < 2 ^ (prefixWord ++ tailWord_621778).sum := by decide
  have hdescent : baseEnd_621778 < baseStart_621778 := by decide
  rcases family_descends (prefixWord ++ tailWord_621778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621818 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2]
def baseStart_621818 : Nat := 118140960795 + 621818 * 2 ^ 59
def prefixEnd_621818 : Nat := 4983230072969 + 3 ^ 40 * 621818 * 2
def baseEnd_621818 : Nat := 319291513617553367915317

theorem tailTrace_621818 : CollatzResearch.WordTrace tailWord_621818 prefixEnd_621818 319291513617553367915317 := by
  unfold tailWord_621818
  simp only [CollatzResearch.WordTrace]
  refine ⟨5669891415316764726162527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15119710440844705936433405 5669891415316764726162527)
  ·
    refine ⟨8504837122975147089243791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5669891415316764726162527 8504837122975147089243791)
    ·
      refine ⟨12757255684462720633865687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8504837122975147089243791 12757255684462720633865687)
      ·
        refine ⟨19135883526694080950798531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12757255684462720633865687 19135883526694080950798531)
        ·
          refine ⟨28703825290041121426197797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19135883526694080950798531 28703825290041121426197797)
          ·
            refine ⟨5381967241882710267412087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28703825290041121426197797 5381967241882710267412087)
            ·
              refine ⟨8072950862824065401118131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5381967241882710267412087 8072950862824065401118131)
              ·
                refine ⟨12109426294236098101677197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8072950862824065401118131 12109426294236098101677197)
                ·
                  refine ⟨4541034860338536788128949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12109426294236098101677197 4541034860338536788128949)
                  ·
                    refine ⟨425722018156737823887089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4541034860338536788128949 425722018156737823887089)
                    ·
                      refine ⟨319291513617553367915317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 425722018156737823887089 319291513617553367915317)
                      ·
                        rfl

theorem cell23_621818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 3, 5, 2].length) (baseStart_621818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621818 prefixEnd_621818 := by exact prefixLift 621818
  have htrace : WordTrace (prefixWord ++ tailWord_621818) baseStart_621818 baseEnd_621818 := by
    simpa [prefixWord, tailWord_621818, baseEnd_621818] using wordTrace_append hprefix tailTrace_621818
  have hstable : (prefixWord ++ tailWord_621818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621818).length < 2 ^ (prefixWord ++ tailWord_621818).sum := by decide
  have hdescent : baseEnd_621818 < baseStart_621818 := by decide
  rcases family_descends (prefixWord ++ tailWord_621818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621825 : List Nat := [1, 2, 4, 1, 1, 3, 2, 2, 3, 1, 3]
def baseStart_621825 : Nat := 118140960795 + 621825 * 2 ^ 59
def prefixEnd_621825 : Nat := 4983230072969 + 3 ^ 40 * 621825 * 2
def baseEnd_621825 : Nat := 319295107982134840527785

theorem tailTrace_621825 : CollatzResearch.WordTrace tailWord_621825 prefixEnd_621825 319295107982134840527785 := by
  unfold tailWord_621825
  simp only [CollatzResearch.WordTrace]
  refine ⟨22679820972241699100154929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15119880648161132733436619 22679820972241699100154929)
  ·
    refine ⟨17009865729181274325116197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22679820972241699100154929 17009865729181274325116197)
    ·
      refine ⟨3189349824221488935959287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17009865729181274325116197 3189349824221488935959287)
      ·
        refine ⟨4784024736332233403938931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3189349824221488935959287 4784024736332233403938931)
        ·
          refine ⟨7176037104498350105908397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4784024736332233403938931 7176037104498350105908397)
          ·
            refine ⟨2691013914186881289715649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7176037104498350105908397 2691013914186881289715649)
            ·
              refine ⟨2018260435640160967286737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2691013914186881289715649 2018260435640160967286737)
              ·
                refine ⟨1513695326730120725465053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2018260435640160967286737 1513695326730120725465053)
                ·
                  refine ⟨567635747523795272049395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1513695326730120725465053 567635747523795272049395)
                  ·
                    refine ⟨851453621285692908074093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 567635747523795272049395 851453621285692908074093)
                    ·
                      refine ⟨319295107982134840527785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 851453621285692908074093 319295107982134840527785)
                      ·
                        rfl

theorem cell23_621825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 1, 3].length) (baseStart_621825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621825 prefixEnd_621825 := by exact prefixLift 621825
  have htrace : WordTrace (prefixWord ++ tailWord_621825) baseStart_621825 baseEnd_621825 := by
    simpa [prefixWord, tailWord_621825, baseEnd_621825] using wordTrace_append hprefix tailTrace_621825
  have hstable : (prefixWord ++ tailWord_621825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621825).length < 2 ^ (prefixWord ++ tailWord_621825).sum := by decide
  have hdescent : baseEnd_621825 < baseStart_621825 := by decide
  rcases family_descends (prefixWord ++ tailWord_621825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621841 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 3, 6]
def baseStart_621841 : Nat := 118140960795 + 621841 * 2 ^ 59
def prefixEnd_621841 : Nat := 4983230072969 + 3 ^ 40 * 621841 * 2
def baseEnd_621841 : Nat := 106434441224202259309237

theorem tailTrace_621841 : CollatzResearch.WordTrace tailWord_621841 prefixEnd_621841 106434441224202259309237 := by
  unfold tailWord_621841
  simp only [CollatzResearch.WordTrace]
  refine ⟨22680404540183733832737377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15120269693455822555158251 22680404540183733832737377)
  ·
    refine ⟨17010303405137800374553033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22680404540183733832737377 17010303405137800374553033)
    ·
      refine ⟨12757727553853350280914775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17010303405137800374553033 12757727553853350280914775)
      ·
        refine ⟨19136591330780025421372163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12757727553853350280914775 19136591330780025421372163)
        ·
          refine ⟨28704886996170038132058245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19136591330780025421372163 28704886996170038132058245)
          ·
            refine ⟨5382166311781882149760921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28704886996170038132058245 5382166311781882149760921)
            ·
              refine ⟨4036624733836411612320691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5382166311781882149760921 4036624733836411612320691)
              ·
                refine ⟨6054937100754617418481037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4036624733836411612320691 6054937100754617418481037)
                ·
                  refine ⟨2270601412782981531930389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6054937100754617418481037 2270601412782981531930389)
                  ·
                    refine ⟨106434441224202259309237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2270601412782981531930389 106434441224202259309237)
                    ·
                      rfl

theorem cell23_621841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 6].length) (baseStart_621841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621841 prefixEnd_621841 := by exact prefixLift 621841
  have htrace : WordTrace (prefixWord ++ tailWord_621841) baseStart_621841 baseEnd_621841 := by
    simpa [prefixWord, tailWord_621841, baseEnd_621841] using wordTrace_append hprefix tailTrace_621841
  have hstable : (prefixWord ++ tailWord_621841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621841).length < 2 ^ (prefixWord ++ tailWord_621841).sum := by decide
  have hdescent : baseEnd_621841 < baseStart_621841 := by decide
  rcases family_descends (prefixWord ++ tailWord_621841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621859 : List Nat := [1, 1, 1, 4, 2, 4, 3, 2, 1, 1, 3]
def baseStart_621859 : Nat := 118140960795 + 621859 * 2 ^ 59
def prefixEnd_621859 : Nat := 4983230072969 + 3 ^ 40 * 621859 * 2
def baseEnd_621859 : Nat := 319312566324387707502629

theorem tailTrace_621859 : CollatzResearch.WordTrace tailWord_621859 prefixEnd_621859 319312566324387707502629 := by
  unfold tailWord_621859
  simp only [CollatzResearch.WordTrace]
  refine ⟨22681061054118522906892631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15120707369412348604595087 22681061054118522906892631)
  ·
    refine ⟨34021591581177784360338947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22681061054118522906892631 34021591581177784360338947)
    ·
      refine ⟨51032387371766676540508421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34021591581177784360338947 51032387371766676540508421)
      ·
        refine ⟨9568572632206251851345329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51032387371766676540508421 9568572632206251851345329)
        ·
          refine ⟨7176429474154688888508997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9568572632206251851345329 7176429474154688888508997)
          ·
            refine ⟨1345580526404004166595437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7176429474154688888508997 1345580526404004166595437)
            ·
              refine ⟨504592697401501562473289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1345580526404004166595437 504592697401501562473289)
              ·
                refine ⟨378444523051126171854967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504592697401501562473289 378444523051126171854967)
                ·
                  refine ⟨567666784576689257782451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378444523051126171854967 567666784576689257782451)
                  ·
                    refine ⟨851500176865033886673677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 567666784576689257782451 851500176865033886673677)
                    ·
                      refine ⟨319312566324387707502629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 851500176865033886673677 319312566324387707502629)
                      ·
                        rfl

theorem cell23_621859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 1, 1, 3].length) (baseStart_621859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621859 prefixEnd_621859 := by exact prefixLift 621859
  have htrace : WordTrace (prefixWord ++ tailWord_621859) baseStart_621859 baseEnd_621859 := by
    simpa [prefixWord, tailWord_621859, baseEnd_621859] using wordTrace_append hprefix tailTrace_621859
  have hstable : (prefixWord ++ tailWord_621859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621859).length < 2 ^ (prefixWord ++ tailWord_621859).sum := by decide
  have hdescent : baseEnd_621859 < baseStart_621859 := by decide
  rcases family_descends (prefixWord ++ tailWord_621859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621868 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 3]
def baseStart_621868 : Nat := 118140960795 + 621868 * 2 ^ 59
def prefixEnd_621868 : Nat := 4983230072969 + 3 ^ 40 * 621868 * 2
def baseEnd_621868 : Nat := 319317187650278172290087

theorem tailTrace_621868 : CollatzResearch.WordTrace tailWord_621868 prefixEnd_621868 319317187650278172290087 := by
  unfold tailWord_621868
  simp only [CollatzResearch.WordTrace]
  refine ⟨11340694655542958721985129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15120926207390611629313505 11340694655542958721985129)
  ·
    refine ⟨8505520991657219041488847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11340694655542958721985129 8505520991657219041488847)
    ·
      refine ⟨12758281487485828562233271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8505520991657219041488847 12758281487485828562233271)
      ·
        refine ⟨19137422231228742843349907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12758281487485828562233271 19137422231228742843349907)
        ·
          refine ⟨28706133346843114265024861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19137422231228742843349907 28706133346843114265024861)
          ·
            refine ⟨10764800005066167849384323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28706133346843114265024861 10764800005066167849384323)
            ·
              refine ⟨16147200007599251774076485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10764800005066167849384323 16147200007599251774076485)
              ·
                refine ⟨3027600001424859707639341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16147200007599251774076485 3027600001424859707639341)
                ·
                  refine ⟨1135350000534322390364753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3027600001424859707639341 1135350000534322390364753)
                  ·
                    refine ⟨851512500400741792773565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1135350000534322390364753 851512500400741792773565)
                    ·
                      refine ⟨319317187650278172290087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 851512500400741792773565 319317187650278172290087)
                      ·
                        rfl

theorem cell23_621868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_621868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621868 prefixEnd_621868 := by exact prefixLift 621868
  have htrace : WordTrace (prefixWord ++ tailWord_621868) baseStart_621868 baseEnd_621868 := by
    simpa [prefixWord, tailWord_621868, baseEnd_621868] using wordTrace_append hprefix tailTrace_621868
  have hstable : (prefixWord ++ tailWord_621868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621868).length < 2 ^ (prefixWord ++ tailWord_621868).sum := by decide
  have hdescent : baseEnd_621868 < baseStart_621868 := by decide
  rcases family_descends (prefixWord ++ tailWord_621868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621875 : List Nat := [1, 1, 1, 2, 5, 3, 1, 3, 2, 4]
def baseStart_621875 : Nat := 118140960795 + 621875 * 2 ^ 59
def prefixEnd_621875 : Nat := 4983230072969 + 3 ^ 40 * 621875 * 2
def baseEnd_621875 : Nat := 106440260671619881634185

theorem tailTrace_621875 : CollatzResearch.WordTrace tailWord_621875 prefixEnd_621875 106440260671619881634185 := by
  unfold tailWord_621875
  simp only [CollatzResearch.WordTrace]
  refine ⟨22681644622060557639475079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15121096414707038426316719 22681644622060557639475079)
  ·
    refine ⟨34022466933090836459212619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22681644622060557639475079 34022466933090836459212619)
    ·
      refine ⟨51033700399636254688818929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34022466933090836459212619 51033700399636254688818929)
      ·
        refine ⟨38275275299727191016614197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51033700399636254688818929 38275275299727191016614197)
        ·
          refine ⟨3588307059349424157807581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38275275299727191016614197 3588307059349424157807581)
          ·
            refine ⟨1345615147256034059177843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3588307059349424157807581 1345615147256034059177843)
            ·
              refine ⟨2018422720884051088766765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345615147256034059177843 2018422720884051088766765)
              ·
                refine ⟨756908520331519158287537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2018422720884051088766765 756908520331519158287537)
                ·
                  refine ⟨567681390248639368715653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 756908520331519158287537 567681390248639368715653)
                  ·
                    refine ⟨106440260671619881634185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 567681390248639368715653 106440260671619881634185)
                    ·
                      rfl

theorem cell23_621875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 4].length) (baseStart_621875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621875 prefixEnd_621875 := by exact prefixLift 621875
  have htrace : WordTrace (prefixWord ++ tailWord_621875) baseStart_621875 baseEnd_621875 := by
    simpa [prefixWord, tailWord_621875, baseEnd_621875] using wordTrace_append hprefix tailTrace_621875
  have hstable : (prefixWord ++ tailWord_621875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621875).length < 2 ^ (prefixWord ++ tailWord_621875).sum := by decide
  have hdescent : baseEnd_621875 < baseStart_621875 := by decide
  rcases family_descends (prefixWord ++ tailWord_621875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621902 : List Nat := [4, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3]
def baseStart_621902 : Nat := 118140960795 + 621902 * 2 ^ 59
def prefixEnd_621902 : Nat := 4983230072969 + 3 ^ 40 * 621902 * 2
def baseEnd_621902 : Nat := 319334645992531039264931

theorem tailTrace_621902 : CollatzResearch.WordTrace tailWord_621902 prefixEnd_621902 319334645992531039264931 := by
  unfold tailWord_621902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835328674120342656338495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15121752928641827500471973 2835328674120342656338495)
  ·
    refine ⟨4252993011180513984507743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2835328674120342656338495 4252993011180513984507743)
    ·
      refine ⟨6379489516770770976761615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4252993011180513984507743 6379489516770770976761615)
      ·
        refine ⟨9569234275156156465142423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6379489516770770976761615 9569234275156156465142423)
        ·
          refine ⟨14353851412734234697713635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9569234275156156465142423 14353851412734234697713635)
          ·
            refine ⟨21530777119101352046570453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14353851412734234697713635 21530777119101352046570453)
            ·
              refine ⟨504627588728937938591495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21530777119101352046570453 504627588728937938591495)
              ·
                refine ⟨756941383093406907887243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504627588728937938591495 756941383093406907887243)
                ·
                  refine ⟨1135412074640110361830865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 756941383093406907887243 1135412074640110361830865)
                  ·
                    refine ⟨851559055980082771373149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1135412074640110361830865 851559055980082771373149)
                    ·
                      refine ⟨319334645992531039264931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 851559055980082771373149 319334645992531039264931)
                      ·
                        rfl

theorem cell23_621902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 1, 1, 2, 3].length) (baseStart_621902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621902 prefixEnd_621902 := by exact prefixLift 621902
  have htrace : WordTrace (prefixWord ++ tailWord_621902) baseStart_621902 baseEnd_621902 := by
    simpa [prefixWord, tailWord_621902, baseEnd_621902] using wordTrace_append hprefix tailTrace_621902
  have hstable : (prefixWord ++ tailWord_621902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621902).length < 2 ^ (prefixWord ++ tailWord_621902).sum := by decide
  have hdescent : baseEnd_621902 < baseStart_621902 := by decide
  rcases family_descends (prefixWord ++ tailWord_621902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621910 : List Nat := [5, 2, 3, 1, 1, 1, 1, 4, 1, 1, 3]
def baseStart_621910 : Nat := 118140960795 + 621910 * 2 ^ 59
def prefixEnd_621910 : Nat := 4983230072969 + 3 ^ 40 * 621910 * 2
def baseEnd_621910 : Nat := 319338753837767007964895

theorem tailTrace_621910 : CollatzResearch.WordTrace tailWord_621910 prefixEnd_621910 319338753837767007964895 := by
  unfold tailWord_621910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1417682573558359913562449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15121947451289172411332789 1417682573558359913562449)
  ·
    refine ⟨1063261930168769935171837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1417682573558359913562449 1063261930168769935171837)
    ·
      refine ⟨398723223813288725689439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1063261930168769935171837 398723223813288725689439)
      ·
        refine ⟨598084835719933088534159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398723223813288725689439 598084835719933088534159)
        ·
          refine ⟨897127253579899632801239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598084835719933088534159 897127253579899632801239)
          ·
            refine ⟨1345690880369849449201859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 897127253579899632801239 1345690880369849449201859)
            ·
              refine ⟨2018536320554774173802789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1345690880369849449201859 2018536320554774173802789)
              ·
                refine ⟨378475560104020157588023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2018536320554774173802789 378475560104020157588023)
                ·
                  refine ⟨567713340156030236382035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378475560104020157588023 567713340156030236382035)
                  ·
                    refine ⟨851570010234045354573053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 567713340156030236382035 851570010234045354573053)
                    ·
                      refine ⟨319338753837767007964895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 851570010234045354573053 319338753837767007964895)
                      ·
                        rfl

theorem cell23_621910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_621910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621910 prefixEnd_621910 := by exact prefixLift 621910
  have htrace : WordTrace (prefixWord ++ tailWord_621910) baseStart_621910 baseEnd_621910 := by
    simpa [prefixWord, tailWord_621910, baseEnd_621910] using wordTrace_append hprefix tailTrace_621910
  have hstable : (prefixWord ++ tailWord_621910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621910).length < 2 ^ (prefixWord ++ tailWord_621910).sum := by decide
  have hdescent : baseEnd_621910 < baseStart_621910 := by decide
  rcases family_descends (prefixWord ++ tailWord_621910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621925 : List Nat := [1, 3, 1, 3, 1, 2, 1, 1, 5, 3, 2]
def baseStart_621925 : Nat := 118140960795 + 621925 * 2 ^ 59
def prefixEnd_621925 : Nat := 4983230072969 + 3 ^ 40 * 621925 * 2
def baseEnd_621925 : Nat := 319346456047584449277325

theorem tailTrace_621925 : CollatzResearch.WordTrace tailWord_621925 prefixEnd_621925 319346456047584449277325 := by
  unfold tailWord_621925
  simp only [CollatzResearch.WordTrace]
  refine ⟨22683468271879416178795229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15122312181252944119196819 22683468271879416178795229)
  ·
    refine ⟨8506300601954781067048211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22683468271879416178795229 8506300601954781067048211)
    ·
      refine ⟨12759450902932171600572317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8506300601954781067048211 12759450902932171600572317)
      ·
        refine ⟨4784794088599564350214619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12759450902932171600572317 4784794088599564350214619)
        ·
          refine ⟨7177191132899346525321929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4784794088599564350214619 7177191132899346525321929)
          ·
            refine ⟨5382893349674509893991447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7177191132899346525321929 5382893349674509893991447)
            ·
              refine ⟨8074340024511764840987171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5382893349674509893991447 8074340024511764840987171)
              ·
                refine ⟨12111510036767647261480757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8074340024511764840987171 12111510036767647261480757)
                ·
                  refine ⟨1135454065946966930763821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12111510036767647261480757 1135454065946966930763821)
                  ·
                    refine ⟨425795274730112599036433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1135454065946966930763821 425795274730112599036433)
                    ·
                      refine ⟨319346456047584449277325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 425795274730112599036433 319346456047584449277325)
                      ·
                        rfl

theorem cell23_621925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 1, 5, 3, 2].length) (baseStart_621925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621925 prefixEnd_621925 := by exact prefixLift 621925
  have htrace : WordTrace (prefixWord ++ tailWord_621925) baseStart_621925 baseEnd_621925 := by
    simpa [prefixWord, tailWord_621925, baseEnd_621925] using wordTrace_append hprefix tailTrace_621925
  have hstable : (prefixWord ++ tailWord_621925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621925).length < 2 ^ (prefixWord ++ tailWord_621925).sum := by decide
  have hdescent : baseEnd_621925 < baseStart_621925 := by decide
  rcases family_descends (prefixWord ++ tailWord_621925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621932 : List Nat := [2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 3]
def baseStart_621932 : Nat := 118140960795 + 621932 * 2 ^ 59
def prefixEnd_621932 : Nat := 4983230072969 + 3 ^ 40 * 621932 * 2
def baseEnd_621932 : Nat := 319350050412165921889793

theorem tailTrace_621932 : CollatzResearch.WordTrace tailWord_621932 prefixEnd_621932 319350050412165921889793 := by
  unfold tailWord_621932
  simp only [CollatzResearch.WordTrace]
  refine ⟨11341861791427028187150025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15122482388569370916200033 11341861791427028187150025)
  ·
    refine ⟨8506396343570271140362519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11341861791427028187150025 8506396343570271140362519)
    ·
      refine ⟨12759594515355406710543779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8506396343570271140362519 12759594515355406710543779)
      ·
        refine ⟨19139391773033110065815669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12759594515355406710543779 19139391773033110065815669)
        ·
          refine ⟨1794317978721854068670219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19139391773033110065815669 1794317978721854068670219)
          ·
            refine ⟨2691476968082781103005329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1794317978721854068670219 2691476968082781103005329)
            ·
              refine ⟨2018607726062085827253997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2691476968082781103005329 2018607726062085827253997)
              ·
                refine ⟨756977897273282185220249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2018607726062085827253997 756977897273282185220249)
                ·
                  refine ⟨567733422954961638915187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 756977897273282185220249 567733422954961638915187)
                  ·
                    refine ⟨851600134432442458372781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 567733422954961638915187 851600134432442458372781)
                    ·
                      refine ⟨319350050412165921889793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 851600134432442458372781 319350050412165921889793)
                      ·
                        rfl

theorem cell23_621932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 3].length) (baseStart_621932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621932 prefixEnd_621932 := by exact prefixLift 621932
  have htrace : WordTrace (prefixWord ++ tailWord_621932) baseStart_621932 baseEnd_621932 := by
    simpa [prefixWord, tailWord_621932, baseEnd_621932] using wordTrace_append hprefix tailTrace_621932
  have hstable : (prefixWord ++ tailWord_621932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621932).length < 2 ^ (prefixWord ++ tailWord_621932).sum := by decide
  have hdescent : baseEnd_621932 < baseStart_621932 := by decide
  rcases family_descends (prefixWord ++ tailWord_621932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621938 : List Nat := [3, 2, 1, 2, 1, 2, 1, 2, 2, 3, 4]
def baseStart_621938 : Nat := 118140960795 + 621938 * 2 ^ 59
def prefixEnd_621938 : Nat := 4983230072969 + 3 ^ 40 * 621938 * 2
def baseEnd_621938 : Nat := 319353131296092898414765

theorem tailTrace_621938 : CollatzResearch.WordTrace tailWord_621938 prefixEnd_621938 319353131296092898414765 := by
  unfold tailWord_621938
  simp only [CollatzResearch.WordTrace]
  refine ⟨5670985605208079849754617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15122628280554879599345645 5670985605208079849754617)
  ·
    refine ⟨4253239203906059887315963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5670985605208079849754617 4253239203906059887315963)
    ·
      refine ⟨6379858805859089830973945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4253239203906059887315963 6379858805859089830973945)
      ·
        refine ⟨4784894104394317373230459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6379858805859089830973945 4784894104394317373230459)
        ·
          refine ⟨7177341156591476059845689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4784894104394317373230459 7177341156591476059845689)
          ·
            refine ⟨5383005867443607044884267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7177341156591476059845689 5383005867443607044884267)
            ·
              refine ⟨8074508801165410567326401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5383005867443607044884267 8074508801165410567326401)
              ·
                refine ⟨6055881600874057925494801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8074508801165410567326401 6055881600874057925494801)
                ·
                  refine ⟨4541911200655543444121101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6055881600874057925494801 4541911200655543444121101)
                  ·
                    refine ⟨1703216700245828791545413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4541911200655543444121101 1703216700245828791545413)
                    ·
                      refine ⟨319353131296092898414765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1703216700245828791545413 319353131296092898414765)
                      ·
                        rfl

theorem cell23_621938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_621938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621938 prefixEnd_621938 := by exact prefixLift 621938
  have htrace : WordTrace (prefixWord ++ tailWord_621938) baseStart_621938 baseEnd_621938 := by
    simpa [prefixWord, tailWord_621938, baseEnd_621938] using wordTrace_append hprefix tailTrace_621938
  have hstable : (prefixWord ++ tailWord_621938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621938).length < 2 ^ (prefixWord ++ tailWord_621938).sum := by decide
  have hdescent : baseEnd_621938 < baseStart_621938 := by decide
  rcases family_descends (prefixWord ++ tailWord_621938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621950 : List Nat := [4, 2, 3, 2, 1, 1, 2, 3, 1, 2, 2]
def baseStart_621950 : Nat := 118140960795 + 621950 * 2 ^ 59
def prefixEnd_621950 : Nat := 4983230072969 + 3 ^ 40 * 621950 * 2
def baseEnd_621950 : Nat := 319359293063946851464711

theorem tailTrace_621950 : CollatzResearch.WordTrace tailWord_621950 prefixEnd_621950 319359293063946851464711 := by
  unfold tailWord_621950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835547512098605681056913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15122920064525896965636869 2835547512098605681056913)
  ·
    refine ⟨2126660634073954260792685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2835547512098605681056913 2126660634073954260792685)
    ·
      refine ⟨797497737777732847797257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2126660634073954260792685 797497737777732847797257)
      ·
        refine ⟨598123303333299635847943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 797497737777732847797257 598123303333299635847943)
        ·
          refine ⟨897184954999949453771915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 598123303333299635847943 897184954999949453771915)
          ·
            refine ⟨1345777432499924180657873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 897184954999949453771915 1345777432499924180657873)
            ·
              refine ⟨1009333074374943135493405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1345777432499924180657873 1009333074374943135493405)
              ·
                refine ⟨378499902890603675810027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1009333074374943135493405 378499902890603675810027)
                ·
                  refine ⟨567749854335905513715041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378499902890603675810027 567749854335905513715041)
                  ·
                    refine ⟨425812390751929135286281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 567749854335905513715041 425812390751929135286281)
                    ·
                      refine ⟨319359293063946851464711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 425812390751929135286281 319359293063946851464711)
                      ·
                        rfl

theorem cell23_621950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_621950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621950 prefixEnd_621950 := by exact prefixLift 621950
  have htrace : WordTrace (prefixWord ++ tailWord_621950) baseStart_621950 baseEnd_621950 := by
    simpa [prefixWord, tailWord_621950, baseEnd_621950] using wordTrace_append hprefix tailTrace_621950
  have hstable : (prefixWord ++ tailWord_621950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621950).length < 2 ^ (prefixWord ++ tailWord_621950).sum := by decide
  have hdescent : baseEnd_621950 < baseStart_621950 := by decide
  rcases family_descends (prefixWord ++ tailWord_621950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621959 : List Nat := [1, 1, 4, 2, 2, 2, 4, 1, 1, 3, 2]
def baseStart_621959 : Nat := 118140960795 + 621959 * 2 ^ 59
def prefixEnd_621959 : Nat := 4983230072969 + 3 ^ 40 * 621959 * 2
def baseEnd_621959 : Nat := 319363914389837316252169

theorem tailTrace_621959 : CollatzResearch.WordTrace tailWord_621959 prefixEnd_621959 319363914389837316252169 := by
  unfold tailWord_621959
  simp only [CollatzResearch.WordTrace]
  refine ⟨22684708353756239985532931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15123138902504159990355287 22684708353756239985532931)
  ·
    refine ⟨34027062530634359978299397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22684708353756239985532931 34027062530634359978299397)
    ·
      refine ⟨6380074224493942495931137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34027062530634359978299397 6380074224493942495931137)
      ·
        refine ⟨4785055668370456871948353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6380074224493942495931137 4785055668370456871948353)
        ·
          refine ⟨3588791751277842653961265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4785055668370456871948353 3588791751277842653961265)
          ·
            refine ⟨2691593813458381990470949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3588791751277842653961265 2691593813458381990470949)
            ·
              refine ⟨504673840023446623213303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2691593813458381990470949 504673840023446623213303)
              ·
                refine ⟨757010760035169934819955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 504673840023446623213303 757010760035169934819955)
                ·
                  refine ⟨1135516140052754902229933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757010760035169934819955 1135516140052754902229933)
                  ·
                    refine ⟨425818552519783088336225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1135516140052754902229933 425818552519783088336225)
                    ·
                      refine ⟨319363914389837316252169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 425818552519783088336225 319363914389837316252169)
                      ·
                        rfl

theorem cell23_621959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_621959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621959 prefixEnd_621959 := by exact prefixLift 621959
  have htrace : WordTrace (prefixWord ++ tailWord_621959) baseStart_621959 baseEnd_621959 := by
    simpa [prefixWord, tailWord_621959, baseEnd_621959] using wordTrace_append hprefix tailTrace_621959
  have hstable : (prefixWord ++ tailWord_621959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621959).length < 2 ^ (prefixWord ++ tailWord_621959).sum := by decide
  have hdescent : baseEnd_621959 < baseStart_621959 := by decide
  rcases family_descends (prefixWord ++ tailWord_621959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_621966 : List Nat := [4, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3]
def baseStart_621966 : Nat := 118140960795 + 621966 * 2 ^ 59
def prefixEnd_621966 : Nat := 4983230072969 + 3 ^ 40 * 621966 * 2
def baseEnd_621966 : Nat := 319367508754418788864637

theorem tailTrace_621966 : CollatzResearch.WordTrace tailWord_621966 prefixEnd_621966 319367508754418788864637 := by
  unfold tailWord_621966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2835620458091360022629719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15123309109820586787358501 2835620458091360022629719)
  ·
    refine ⟨4253430687137040033944579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2835620458091360022629719 4253430687137040033944579)
    ·
      refine ⟨6380146030705560050916869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4253430687137040033944579 6380146030705560050916869)
      ·
        refine ⟨1196277380757292509546913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6380146030705560050916869 1196277380757292509546913)
        ·
          refine ⟨897208035567969382160185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1196277380757292509546913 897208035567969382160185)
          ·
            refine ⟨672906026675977036620139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 897208035567969382160185 672906026675977036620139)
            ·
              refine ⟨1009359040013965554930209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 672906026675977036620139 1009359040013965554930209)
              ·
                refine ⟨757019280010474166197657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1009359040013965554930209 757019280010474166197657)
                ·
                  refine ⟨567764460007855624648243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 757019280010474166197657 567764460007855624648243)
                  ·
                    refine ⟨851646690011783436972365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 567764460007855624648243 851646690011783436972365)
                    ·
                      refine ⟨319367508754418788864637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 851646690011783436972365 319367508754418788864637)
                      ·
                        rfl

theorem cell23_621966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_621966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_621966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_621966 prefixEnd_621966 := by exact prefixLift 621966
  have htrace : WordTrace (prefixWord ++ tailWord_621966) baseStart_621966 baseEnd_621966 := by
    simpa [prefixWord, tailWord_621966, baseEnd_621966] using wordTrace_append hprefix tailTrace_621966
  have hstable : (prefixWord ++ tailWord_621966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_621966).length < 2 ^ (prefixWord ++ tailWord_621966).sum := by decide
  have hdescent : baseEnd_621966 < baseStart_621966 := by decide
  rcases family_descends (prefixWord ++ tailWord_621966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622008 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 1, 7]
def baseStart_622008 : Nat := 118140960795 + 622008 * 2 ^ 59
def prefixEnd_622008 : Nat := 4983230072969 + 3 ^ 40 * 622008 * 2
def baseEnd_622008 : Nat := 106463024980635874846481

theorem tailTrace_622008 : CollatzResearch.WordTrace tailWord_622008 prefixEnd_622008 106463024980635874846481 := by
  unfold tailWord_622008
  simp only [CollatzResearch.WordTrace]
  refine ⟨11343247765289360677033339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15124330353719147569377785 11343247765289360677033339)
  ·
    refine ⟨17014871647934041015550009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11343247765289360677033339 17014871647934041015550009)
    ·
      refine ⟨12761153735950530761662507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17014871647934041015550009 12761153735950530761662507)
      ·
        refine ⟨19141730603925796142493761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12761153735950530761662507 19141730603925796142493761)
        ·
          refine ⟨14356297952944347106870321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19141730603925796142493761 14356297952944347106870321)
          ·
            refine ⟨10767223464708260330152741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14356297952944347106870321 10767223464708260330152741)
            ·
              refine ⟨2018854399632798811903639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10767223464708260330152741 2018854399632798811903639)
              ·
                refine ⟨3028281599449198217855459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2018854399632798811903639 3028281599449198217855459)
                ·
                  refine ⟨4542422399173797326783189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3028281599449198217855459 4542422399173797326783189)
                  ·
                    refine ⟨106463024980635874846481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4542422399173797326783189 106463024980635874846481)
                    ·
                      rfl

theorem cell23_622008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 7].length) (baseStart_622008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622008 prefixEnd_622008 := by exact prefixLift 622008
  have htrace : WordTrace (prefixWord ++ tailWord_622008) baseStart_622008 baseEnd_622008 := by
    simpa [prefixWord, tailWord_622008, baseEnd_622008] using wordTrace_append hprefix tailTrace_622008
  have hstable : (prefixWord ++ tailWord_622008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622008).length < 2 ^ (prefixWord ++ tailWord_622008).sum := by decide
  have hdescent : baseEnd_622008 < baseStart_622008 := by decide
  rcases family_descends (prefixWord ++ tailWord_622008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622062 : List Nat := [4, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4]
def baseStart_622062 : Nat := 118140960795 + 622062 * 2 ^ 59
def prefixEnd_622062 : Nat := 4983230072969 + 3 ^ 40 * 622062 * 2
def baseEnd_622062 : Nat := 319416802897250413264195

theorem tailTrace_622062 : CollatzResearch.WordTrace tailWord_622062 prefixEnd_622062 319416802897250413264195 := by
  unfold tailWord_622062
  simp only [CollatzResearch.WordTrace]
  refine ⟨2836058134047886072066555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15125643381588725717688293 2836058134047886072066555)
  ·
    refine ⟨4254087201071829108099833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2836058134047886072066555 4254087201071829108099833)
    ·
      refine ⟨3190565400803871831074875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4254087201071829108099833 3190565400803871831074875)
      ·
        refine ⟨4785848101205807746612313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3190565400803871831074875 4785848101205807746612313)
        ·
          refine ⟨3589386075904355809959235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4785848101205807746612313 3589386075904355809959235)
          ·
            refine ⟨5384079113856533714938853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3589386075904355809959235 5384079113856533714938853)
            ·
              refine ⟨1009514833848100071551035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5384079113856533714938853 1009514833848100071551035)
              ·
                refine ⟨1514272250772150107326553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009514833848100071551035 1514272250772150107326553)
                ·
                  refine ⟨1135704188079112580494915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1514272250772150107326553 1135704188079112580494915)
                  ·
                    refine ⟨1703556282118668870742373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1135704188079112580494915 1703556282118668870742373)
                    ·
                      refine ⟨319416802897250413264195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1703556282118668870742373 319416802897250413264195)
                      ·
                        rfl

theorem cell23_622062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_622062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622062 prefixEnd_622062 := by exact prefixLift 622062
  have htrace : WordTrace (prefixWord ++ tailWord_622062) baseStart_622062 baseEnd_622062 := by
    simpa [prefixWord, tailWord_622062, baseEnd_622062] using wordTrace_append hprefix tailTrace_622062
  have hstable : (prefixWord ++ tailWord_622062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622062).length < 2 ^ (prefixWord ++ tailWord_622062).sum := by decide
  have hdescent : baseEnd_622062 < baseStart_622062 := by decide
  rcases family_descends (prefixWord ++ tailWord_622062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622110 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_622110 : Nat := 118140960795 + 622110 * 2 ^ 59
def prefixEnd_622110 : Nat := 4983230072969 + 3 ^ 40 * 622110 * 2
def baseEnd_622110 : Nat := 106480483322888741821325

theorem tailTrace_622110 : CollatzResearch.WordTrace tailWord_622110 prefixEnd_622110 106480483322888741821325 := by
  unfold tailWord_622110
  simp only [CollatzResearch.WordTrace]
  refine ⟨2836276972026149096784973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15126810517472795182853189 2836276972026149096784973)
  ·
    refine ⟨1063603864509805911294365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2836276972026149096784973 1063603864509805911294365)
    ·
      refine ⟨398851449191177216735387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1063603864509805911294365 398851449191177216735387)
      ·
        refine ⟨598277173786765825103081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 398851449191177216735387 598277173786765825103081)
        ·
          refine ⟨448707880340074368827311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 598277173786765825103081 448707880340074368827311)
          ·
            refine ⟨673061820510111553240967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 448707880340074368827311 673061820510111553240967)
            ·
              refine ⟨1009592730765167329861451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673061820510111553240967 1009592730765167329861451)
              ·
                refine ⟨1514389096147750994792177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009592730765167329861451 1514389096147750994792177)
                ·
                  refine ⟨1135791822110813246094133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1514389096147750994792177 1135791822110813246094133)
                  ·
                    refine ⟨106480483322888741821325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1135791822110813246094133 106480483322888741821325)
                    ·
                      rfl

theorem cell23_622110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_622110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622110 prefixEnd_622110 := by exact prefixLift 622110
  have htrace : WordTrace (prefixWord ++ tailWord_622110) baseStart_622110 baseEnd_622110 := by
    simpa [prefixWord, tailWord_622110, baseEnd_622110] using wordTrace_append hprefix tailTrace_622110
  have hstable : (prefixWord ++ tailWord_622110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622110).length < 2 ^ (prefixWord ++ tailWord_622110).sum := by decide
  have hdescent : baseEnd_622110 < baseStart_622110 := by decide
  rcases family_descends (prefixWord ++ tailWord_622110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622162 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_622162 : Nat := 118140960795 + 622162 * 2 ^ 59
def prefixEnd_622162 : Nat := 4983230072969 + 3 ^ 40 * 622162 * 2
def baseEnd_622162 : Nat := 106489383654233340671245

theorem tailTrace_622162 : CollatzResearch.WordTrace tailWord_622162 prefixEnd_622162 106489383654233340671245 := by
  unfold tailWord_622162
  simp only [CollatzResearch.WordTrace]
  refine ⟨5673028093005201413793185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15128074914680537103448493 5673028093005201413793185)
  ·
    refine ⟨4254771069753901060344889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5673028093005201413793185 4254771069753901060344889)
    ·
      refine ⟨3191078302315425795258667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4254771069753901060344889 3191078302315425795258667)
      ·
        refine ⟨4786617453473138692888001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3191078302315425795258667 4786617453473138692888001)
        ·
          refine ⟨3589963090104854019666001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4786617453473138692888001 3589963090104854019666001)
          ·
            refine ⟨2692472317578640514749501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3589963090104854019666001 2692472317578640514749501)
            ·
              refine ⟨1009677119091990193031063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2692472317578640514749501 1009677119091990193031063)
              ·
                refine ⟨1514515678637985289546595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009677119091990193031063 1514515678637985289546595)
                ·
                  refine ⟨2271773517956977934319893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514515678637985289546595 2271773517956977934319893)
                  ·
                    refine ⟨106489383654233340671245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2271773517956977934319893 106489383654233340671245)
                    ·
                      rfl

theorem cell23_622162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_622162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622162 prefixEnd_622162 := by exact prefixLift 622162
  have htrace : WordTrace (prefixWord ++ tailWord_622162) baseStart_622162 baseEnd_622162 := by
    simpa [prefixWord, tailWord_622162, baseEnd_622162] using wordTrace_append hprefix tailTrace_622162
  have hstable : (prefixWord ++ tailWord_622162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622162).length < 2 ^ (prefixWord ++ tailWord_622162).sum := by decide
  have hdescent : baseEnd_622162 < baseStart_622162 := by decide
  rcases family_descends (prefixWord ++ tailWord_622162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622189 : List Nat := [1, 5, 1, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_622189 : Nat := 118140960795 + 622189 * 2 ^ 59
def prefixEnd_622189 : Nat := 4983230072969 + 3 ^ 40 * 622189 * 2
def baseEnd_622189 : Nat := 319482014940371416376111

theorem tailTrace_622189 : CollatzResearch.WordTrace tailWord_622189 prefixEnd_622189 319482014940371416376111 := by
  unfold tailWord_622189
  simp only [CollatzResearch.WordTrace]
  refine ⟨22693097142922989266405621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15128731428615326177603747 22693097142922989266405621)
  ·
    refine ⟨2127477857149030243725527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22693097142922989266405621 2127477857149030243725527)
    ·
      refine ⟨3191216785723545365588291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2127477857149030243725527 3191216785723545365588291)
      ·
        refine ⟨4786825178585318048382437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3191216785723545365588291 4786825178585318048382437)
        ·
          refine ⟨897529720984747134071707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4786825178585318048382437 897529720984747134071707)
          ·
            refine ⟨1346294581477120701107561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 897529720984747134071707 1346294581477120701107561)
            ·
              refine ⟨1009720936107840525830671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1346294581477120701107561 1009720936107840525830671)
              ·
                refine ⟨1514581404161760788746007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009720936107840525830671 1514581404161760788746007)
                ·
                  refine ⟨2271872106242641183119011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514581404161760788746007 2271872106242641183119011)
                  ·
                    refine ⟨3407808159363961774678517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2271872106242641183119011 3407808159363961774678517)
                    ·
                      refine ⟨319482014940371416376111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3407808159363961774678517 319482014940371416376111)
                      ·
                        rfl

theorem cell23_622189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_622189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622189 prefixEnd_622189 := by exact prefixLift 622189
  have htrace : WordTrace (prefixWord ++ tailWord_622189) baseStart_622189 baseEnd_622189 := by
    simpa [prefixWord, tailWord_622189, baseEnd_622189] using wordTrace_append hprefix tailTrace_622189
  have hstable : (prefixWord ++ tailWord_622189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622189).length < 2 ^ (prefixWord ++ tailWord_622189).sum := by decide
  have hdescent : baseEnd_622189 < baseStart_622189 := by decide
  rcases family_descends (prefixWord ++ tailWord_622189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622203 : List Nat := [1, 1, 1, 1, 1, 4, 7, 2, 1, 2, 2]
def baseStart_622203 : Nat := 118140960795 + 622203 * 2 ^ 59
def prefixEnd_622203 : Nat := 4983230072969 + 3 ^ 40 * 622203 * 2
def baseEnd_622203 : Nat := 319489203669534361601047

theorem tailTrace_622203 : CollatzResearch.WordTrace tailWord_622203 prefixEnd_622203 319489203669534361601047 := by
  unfold tailWord_622203
  simp only [CollatzResearch.WordTrace]
  refine ⟨22693607764872269657415263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15129071843248179771610175 22693607764872269657415263)
  ·
    refine ⟨34040411647308404486122895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22693607764872269657415263 34040411647308404486122895)
    ·
      refine ⟨51060617470962606729184343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34040411647308404486122895 51060617470962606729184343)
      ·
        refine ⟨76590926206443910093776515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51060617470962606729184343 76590926206443910093776515)
        ·
          refine ⟨114886389309665865140664773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76590926206443910093776515 114886389309665865140664773)
          ·
            refine ⟨21541197995562349713874645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114886389309665865140664773 21541197995562349713874645)
            ·
              refine ⟨504871828020992571418937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21541197995562349713874645 504871828020992571418937)
              ·
                refine ⟨378653871015744428564203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504871828020992571418937 378653871015744428564203)
                ·
                  refine ⟨567980806523616642846305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378653871015744428564203 567980806523616642846305)
                  ·
                    refine ⟨425985604892712482134729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 567980806523616642846305 425985604892712482134729)
                    ·
                      refine ⟨319489203669534361601047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 425985604892712482134729 319489203669534361601047)
                      ·
                        rfl

theorem cell23_622203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 2, 1, 2, 2].length) (baseStart_622203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622203 prefixEnd_622203 := by exact prefixLift 622203
  have htrace : WordTrace (prefixWord ++ tailWord_622203) baseStart_622203 baseEnd_622203 := by
    simpa [prefixWord, tailWord_622203, baseEnd_622203] using wordTrace_append hprefix tailTrace_622203
  have hstable : (prefixWord ++ tailWord_622203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622203).length < 2 ^ (prefixWord ++ tailWord_622203).sum := by decide
  have hdescent : baseEnd_622203 < baseStart_622203 := by decide
  rcases family_descends (prefixWord ++ tailWord_622203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622219 : List Nat := [1, 1, 1, 1, 4, 1, 5, 3, 2, 1, 3]
def baseStart_622219 : Nat := 118140960795 + 622219 * 2 ^ 59
def prefixEnd_622219 : Nat := 4983230072969 + 3 ^ 40 * 622219 * 2
def baseEnd_622219 : Nat := 319497419360006299000973

theorem tailTrace_622219 : CollatzResearch.WordTrace tailWord_622219 prefixEnd_622219 319497419360006299000973 := by
  unfold tailWord_622219
  simp only [CollatzResearch.WordTrace]
  refine ⟨22694191332814304389997711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15129460888542869593331807 22694191332814304389997711)
  ·
    refine ⟨34041286999221456584996567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22694191332814304389997711 34041286999221456584996567)
    ·
      refine ⟨51061930498832184877494851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34041286999221456584996567 51061930498832184877494851)
      ·
        refine ⟨76592895748248277316242277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51061930498832184877494851 76592895748248277316242277)
        ·
          refine ⟨14361167952796551996795427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76592895748248277316242277 14361167952796551996795427)
          ·
            refine ⟨21541751929194827995193141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14361167952796551996795427 21541751929194827995193141)
            ·
              refine ⟨2019539243362015124549357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21541751929194827995193141 2019539243362015124549357)
              ·
                refine ⟨757327216260755671706009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2019539243362015124549357 757327216260755671706009)
                ·
                  refine ⟨567995412195566753779507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 757327216260755671706009 567995412195566753779507)
                  ·
                    refine ⟨851993118293350130669261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 567995412195566753779507 851993118293350130669261)
                    ·
                      refine ⟨319497419360006299000973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 851993118293350130669261 319497419360006299000973)
                      ·
                        rfl

theorem cell23_622219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 1, 3].length) (baseStart_622219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622219 prefixEnd_622219 := by exact prefixLift 622219
  have htrace : WordTrace (prefixWord ++ tailWord_622219) baseStart_622219 baseEnd_622219 := by
    simpa [prefixWord, tailWord_622219, baseEnd_622219] using wordTrace_append hprefix tailTrace_622219
  have hstable : (prefixWord ++ tailWord_622219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622219).length < 2 ^ (prefixWord ++ tailWord_622219).sum := by decide
  have hdescent : baseEnd_622219 < baseStart_622219 := by decide
  rcases family_descends (prefixWord ++ tailWord_622219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622225 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 4]
def baseStart_622225 : Nat := 118140960795 + 622225 * 2 ^ 59
def prefixEnd_622225 : Nat := 4983230072969 + 3 ^ 40 * 622225 * 2
def baseEnd_622225 : Nat := 319500500243933275525945

theorem tailTrace_622225 : CollatzResearch.WordTrace tailWord_622225 prefixEnd_622225 319500500243933275525945 := by
  unfold tailWord_622225
  simp only [CollatzResearch.WordTrace]
  refine ⟨22694410170792567414716129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15129606780528378276477419 22694410170792567414716129)
  ·
    refine ⟨17020807628094425561037097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22694410170792567414716129 17020807628094425561037097)
    ·
      refine ⟨12765605721070819170777823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17020807628094425561037097 12765605721070819170777823)
      ·
        refine ⟨19148408581606228756166735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12765605721070819170777823 19148408581606228756166735)
        ·
          refine ⟨28722612872409343134250103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19148408581606228756166735 28722612872409343134250103)
          ·
            refine ⟨43083919308614014701375155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28722612872409343134250103 43083919308614014701375155)
            ·
              refine ⟨64625878962921022052062733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43083919308614014701375155 64625878962921022052062733)
              ·
                refine ⟨24234704611095383269523525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64625878962921022052062733 24234704611095383269523525)
                ·
                  refine ⟨4544007114580384363035661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24234704611095383269523525 4544007114580384363035661)
                  ·
                    refine ⟨1704002667967644136138373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4544007114580384363035661 1704002667967644136138373)
                    ·
                      refine ⟨319500500243933275525945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1704002667967644136138373 319500500243933275525945)
                      ·
                        rfl

theorem cell23_622225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_622225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622225 prefixEnd_622225 := by exact prefixLift 622225
  have htrace : WordTrace (prefixWord ++ tailWord_622225) baseStart_622225 baseEnd_622225 := by
    simpa [prefixWord, tailWord_622225, baseEnd_622225] using wordTrace_append hprefix tailTrace_622225
  have hstable : (prefixWord ++ tailWord_622225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622225).length < 2 ^ (prefixWord ++ tailWord_622225).sum := by decide
  have hdescent : baseEnd_622225 < baseStart_622225 := by decide
  rcases family_descends (prefixWord ++ tailWord_622225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622254 : List Nat := [4, 1, 4, 1, 2, 2, 2, 2, 1, 2, 2]
def baseStart_622254 : Nat := 118140960795 + 622254 * 2 ^ 59
def prefixEnd_622254 : Nat := 4983230072969 + 3 ^ 40 * 622254 * 2
def baseEnd_622254 : Nat := 319515391182913662063313

theorem tailTrace_622254 : CollatzResearch.WordTrace tailWord_622254 prefixEnd_622254 319515391182913662063313 := by
  unfold tailWord_622254
  simp only [CollatzResearch.WordTrace]
  refine ⟨2836933485960938170940227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15130311925125003578347877 2836933485960938170940227)
  ·
    refine ⟨4255400228941407256410341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2836933485960938170940227 4255400228941407256410341)
    ·
      refine ⟨797887542926513860576939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4255400228941407256410341 797887542926513860576939)
      ·
        refine ⟨1196831314389770790865409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 797887542926513860576939 1196831314389770790865409)
        ·
          refine ⟨897623485792328093149057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1196831314389770790865409 897623485792328093149057)
          ·
            refine ⟨673217614344246069861793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 897623485792328093149057 673217614344246069861793)
            ·
              refine ⟨504913210758184552396345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 673217614344246069861793 504913210758184552396345)
              ·
                refine ⟨378684908068638414297259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 504913210758184552396345 378684908068638414297259)
                ·
                  refine ⟨568027362102957621445889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378684908068638414297259 568027362102957621445889)
                  ·
                    refine ⟨426020521577218216084417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 568027362102957621445889 426020521577218216084417)
                    ·
                      refine ⟨319515391182913662063313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 426020521577218216084417 319515391182913662063313)
                      ·
                        rfl

theorem cell23_622254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_622254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622254 prefixEnd_622254 := by exact prefixLift 622254
  have htrace : WordTrace (prefixWord ++ tailWord_622254) baseStart_622254 baseEnd_622254 := by
    simpa [prefixWord, tailWord_622254, baseEnd_622254] using wordTrace_append hprefix tailTrace_622254
  have hstable : (prefixWord ++ tailWord_622254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622254).length < 2 ^ (prefixWord ++ tailWord_622254).sum := by decide
  have hdescent : baseEnd_622254 < baseStart_622254 := by decide
  rcases family_descends (prefixWord ++ tailWord_622254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622272 : List Nat := [2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 4]
def baseStart_622272 : Nat := 118140960795 + 622272 * 2 ^ 59
def prefixEnd_622272 : Nat := 4983230072969 + 3 ^ 40 * 622272 * 2
def baseEnd_622272 : Nat := 319524633834694591638229

theorem tailTrace_622272 : CollatzResearch.WordTrace tailWord_622272 prefixEnd_622272 319524633834694591638229 := by
  unfold tailWord_622272
  simp only [CollatzResearch.WordTrace]
  refine ⟨11348062200811147220838535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15130749601081529627784713 11348062200811147220838535)
  ·
    refine ⟨17022093301216720831257803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11348062200811147220838535 17022093301216720831257803)
    ·
      refine ⟨25533139951825081246886705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17022093301216720831257803 25533139951825081246886705)
      ·
        refine ⟨19149854963868810935165029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25533139951825081246886705 19149854963868810935165029)
        ·
          refine ⟨3590597805725402050343443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19149854963868810935165029 3590597805725402050343443)
          ·
            refine ⟨5385896708588103075515165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590597805725402050343443 5385896708588103075515165)
            ·
              refine ⟨2019711265720538653318187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5385896708588103075515165 2019711265720538653318187)
              ·
                refine ⟨3029566898580807979977281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2019711265720538653318187 3029566898580807979977281)
                ·
                  refine ⟨2272175173935605984982961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3029566898580807979977281 2272175173935605984982961)
                  ·
                    refine ⟨1704131380451704488737221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2272175173935605984982961 1704131380451704488737221)
                    ·
                      refine ⟨319524633834694591638229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1704131380451704488737221 319524633834694591638229)
                      ·
                        rfl

theorem cell23_622272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 4].length) (baseStart_622272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622272 prefixEnd_622272 := by exact prefixLift 622272
  have htrace : WordTrace (prefixWord ++ tailWord_622272) baseStart_622272 baseEnd_622272 := by
    simpa [prefixWord, tailWord_622272, baseEnd_622272] using wordTrace_append hprefix tailTrace_622272
  have hstable : (prefixWord ++ tailWord_622272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622272).length < 2 ^ (prefixWord ++ tailWord_622272).sum := by decide
  have hdescent : baseEnd_622272 < baseStart_622272 := by decide
  rcases family_descends (prefixWord ++ tailWord_622272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622276 : List Nat := [2, 3, 3, 1, 1, 1, 4, 1, 1, 4, 2]
def baseStart_622276 : Nat := 118140960795 + 622276 * 2 ^ 59
def prefixEnd_622276 : Nat := 4983230072969 + 3 ^ 40 * 622276 * 2
def baseEnd_622276 : Nat := 319526687757312575988211

theorem tailTrace_622276 : CollatzResearch.WordTrace tailWord_622276 prefixEnd_622276 319526687757312575988211 := by
  unfold tailWord_622276
  simp only [CollatzResearch.WordTrace]
  refine ⟨11348135146803901562411341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15130846862405202083215121 11348135146803901562411341)
  ·
    refine ⟨4255550680051463085904253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11348135146803901562411341 4255550680051463085904253)
    ·
      refine ⟨1595831505019298657214095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4255550680051463085904253 1595831505019298657214095)
      ·
        refine ⟨2393747257528947985821143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1595831505019298657214095 2393747257528947985821143)
        ·
          refine ⟨3590620886293421978731715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393747257528947985821143 3590620886293421978731715)
          ·
            refine ⟨5385931329440132968097573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590620886293421978731715 5385931329440132968097573)
            ·
              refine ⟨1009862124270024931518295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5385931329440132968097573 1009862124270024931518295)
              ·
                refine ⟨1514793186405037397277443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1009862124270024931518295 1514793186405037397277443)
                ·
                  refine ⟨2272189779607556095916165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1514793186405037397277443 2272189779607556095916165)
                  ·
                    refine ⟨426035583676416767984281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2272189779607556095916165 426035583676416767984281)
                    ·
                      refine ⟨319526687757312575988211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 426035583676416767984281 319526687757312575988211)
                      ·
                        rfl

theorem cell23_622276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 1, 1, 4, 2].length) (baseStart_622276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622276 prefixEnd_622276 := by exact prefixLift 622276
  have htrace : WordTrace (prefixWord ++ tailWord_622276) baseStart_622276 baseEnd_622276 := by
    simpa [prefixWord, tailWord_622276, baseEnd_622276] using wordTrace_append hprefix tailTrace_622276
  have hstable : (prefixWord ++ tailWord_622276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622276).length < 2 ^ (prefixWord ++ tailWord_622276).sum := by decide
  have hdescent : baseEnd_622276 < baseStart_622276 := by decide
  rcases family_descends (prefixWord ++ tailWord_622276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622322 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 1, 1, 7]
def baseStart_622322 : Nat := 118140960795 + 622322 * 2 ^ 59
def prefixEnd_622322 : Nat := 4983230072969 + 3 ^ 40 * 622322 * 2
def baseEnd_622322 : Nat := 319550307867419396012999

theorem tailTrace_622322 : CollatzResearch.WordTrace tailWord_622322 prefixEnd_622322 319550307867419396012999 := by
  unfold tailWord_622322
  simp only [CollatzResearch.WordTrace]
  refine ⟨5674487012860288245249305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15131965367627435320664813 5674487012860288245249305)
  ·
    refine ⟨4255865259645216183936979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5674487012860288245249305 4255865259645216183936979)
    ·
      refine ⟨6383797889467824275905469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4255865259645216183936979 6383797889467824275905469)
      ·
        refine ⟨2393924208550434103464551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6383797889467824275905469 2393924208550434103464551)
        ·
          refine ⟨3590886312825651155196827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2393924208550434103464551 3590886312825651155196827)
          ·
            refine ⟨5386329469238476732795241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590886312825651155196827 5386329469238476732795241)
            ·
              refine ⟨4039747101928857549596431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5386329469238476732795241 4039747101928857549596431)
              ·
                refine ⟨6059620652893286324394647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4039747101928857549596431 6059620652893286324394647)
                ·
                  refine ⟨9089430979339929486591971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6059620652893286324394647 9089430979339929486591971)
                  ·
                    refine ⟨13634146469009894229887957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9089430979339929486591971 13634146469009894229887957)
                    ·
                      refine ⟨319550307867419396012999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13634146469009894229887957 319550307867419396012999)
                      ·
                        rfl

theorem cell23_622322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_622322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622322 prefixEnd_622322 := by exact prefixLift 622322
  have htrace : WordTrace (prefixWord ++ tailWord_622322) baseStart_622322 baseEnd_622322 := by
    simpa [prefixWord, tailWord_622322, baseEnd_622322] using wordTrace_append hprefix tailTrace_622322
  have hstable : (prefixWord ++ tailWord_622322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622322).length < 2 ^ (prefixWord ++ tailWord_622322).sum := by decide
  have hdescent : baseEnd_622322 < baseStart_622322 := by decide
  rcases family_descends (prefixWord ++ tailWord_622322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622332 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_622332 : Nat := 118140960795 + 622332 * 2 ^ 59
def prefixEnd_622332 : Nat := 4983230072969 + 3 ^ 40 * 622332 * 2
def baseEnd_622332 : Nat := 319555442673964356887953

theorem tailTrace_622332 : CollatzResearch.WordTrace tailWord_622332 prefixEnd_622332 319555442673964356887953 := by
  unfold tailWord_622332
  simp only [CollatzResearch.WordTrace]
  refine ⟨11349156390702462344430625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15132208520936616459240833 11349156390702462344430625)
  ·
    refine ⟨8511867293026846758322969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11349156390702462344430625 8511867293026846758322969)
    ·
      refine ⟨6383900469770135068742227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8511867293026846758322969 6383900469770135068742227)
      ·
        refine ⟨9575850704655202603113341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6383900469770135068742227 9575850704655202603113341)
        ·
          refine ⟨3590944014245700976167503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9575850704655202603113341 3590944014245700976167503)
          ·
            refine ⟨5386416021368551464251255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3590944014245700976167503 5386416021368551464251255)
            ·
              refine ⟨8079624032052827196376883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5386416021368551464251255 8079624032052827196376883)
              ·
                refine ⟨12119436048079240794565325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8079624032052827196376883 12119436048079240794565325)
                ·
                  refine ⟨4544788518029715297961997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12119436048079240794565325 4544788518029715297961997)
                  ·
                    refine ⟨1704295694261143236735749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4544788518029715297961997 1704295694261143236735749)
                    ·
                      refine ⟨319555442673964356887953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1704295694261143236735749 319555442673964356887953)
                      ·
                        rfl

theorem cell23_622332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_622332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622332 prefixEnd_622332 := by exact prefixLift 622332
  have htrace : WordTrace (prefixWord ++ tailWord_622332) baseStart_622332 baseEnd_622332 := by
    simpa [prefixWord, tailWord_622332, baseEnd_622332] using wordTrace_append hprefix tailTrace_622332
  have hstable : (prefixWord ++ tailWord_622332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622332).length < 2 ^ (prefixWord ++ tailWord_622332).sum := by decide
  have hdescent : baseEnd_622332 < baseStart_622332 := by decide
  rcases family_descends (prefixWord ++ tailWord_622332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622369 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 4, 2, 3]
def baseStart_622369 : Nat := 118140960795 + 622369 * 2 ^ 59
def prefixEnd_622369 : Nat := 4983230072969 + 3 ^ 40 * 622369 * 2
def baseEnd_622369 : Nat := 319574441458180712125283

theorem tailTrace_622369 : CollatzResearch.WordTrace tailWord_622369 prefixEnd_622369 319574441458180712125283 := by
  unfold tailWord_622369
  simp only [CollatzResearch.WordTrace]
  refine ⟨22699662282270880007958161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15133108188180586671972107 22699662282270880007958161)
  ·
    refine ⟨17024746711703160005968621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22699662282270880007958161 17024746711703160005968621)
    ·
      refine ⟨6384280016888685002238233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17024746711703160005968621 6384280016888685002238233)
      ·
        refine ⟨4788210012666513751678675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6384280016888685002238233 4788210012666513751678675)
        ·
          refine ⟨7182315018999770627518013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4788210012666513751678675 7182315018999770627518013)
          ·
            refine ⟨2693368132124913985319255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7182315018999770627518013 2693368132124913985319255)
            ·
              refine ⟨4040052198187370977978883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2693368132124913985319255 4040052198187370977978883)
              ·
                refine ⟨6060078297281056466968325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4040052198187370977978883 6060078297281056466968325)
                ·
                  refine ⟨1136264680740198087556561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6060078297281056466968325 1136264680740198087556561)
                  ·
                    refine ⟨852198510555148565667421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1136264680740198087556561 852198510555148565667421)
                    ·
                      refine ⟨319574441458180712125283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 852198510555148565667421 319574441458180712125283)
                      ·
                        rfl

theorem cell23_622369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_622369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622369 prefixEnd_622369 := by exact prefixLift 622369
  have htrace : WordTrace (prefixWord ++ tailWord_622369) baseStart_622369 baseEnd_622369 := by
    simpa [prefixWord, tailWord_622369, baseEnd_622369] using wordTrace_append hprefix tailTrace_622369
  have hstable : (prefixWord ++ tailWord_622369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622369).length < 2 ^ (prefixWord ++ tailWord_622369).sum := by decide
  have hdescent : baseEnd_622369 < baseStart_622369 := by decide
  rcases family_descends (prefixWord ++ tailWord_622369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622376 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 3, 4]
def baseStart_622376 : Nat := 118140960795 + 622376 * 2 ^ 59
def prefixEnd_622376 : Nat := 4983230072969 + 3 ^ 40 * 622376 * 2
def baseEnd_622376 : Nat := 106526011940920728245917

theorem tailTrace_622376 : CollatzResearch.WordTrace tailWord_622376 prefixEnd_622376 106526011940920728245917 := by
  unfold tailWord_622376
  simp only [CollatzResearch.WordTrace]
  refine ⟨11349958796622760101731491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15133278395497013468975321 11349958796622760101731491)
  ·
    refine ⟨17024938194934140152597237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11349958796622760101731491 17024938194934140152597237)
    ·
      refine ⟨1596087955775075639305991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17024938194934140152597237 1596087955775075639305991)
      ·
        refine ⟨2394131933662613458958987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1596087955775075639305991 2394131933662613458958987)
        ·
          refine ⟨3591197900493920188438481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2394131933662613458958987 3591197900493920188438481)
          ·
            refine ⟨2693398425370440141328861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3591197900493920188438481 2693398425370440141328861)
            ·
              refine ⟨1010024409513915052998323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2693398425370440141328861 1010024409513915052998323)
              ·
                refine ⟨1515036614270872579497485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010024409513915052998323 1515036614270872579497485)
                ·
                  refine ⟨568138730351577217311557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1515036614270872579497485 568138730351577217311557)
                  ·
                    refine ⟨106526011940920728245917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 568138730351577217311557 106526011940920728245917)
                    ·
                      rfl

theorem cell23_622376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_622376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622376 prefixEnd_622376 := by exact prefixLift 622376
  have htrace : WordTrace (prefixWord ++ tailWord_622376) baseStart_622376 baseEnd_622376 := by
    simpa [prefixWord, tailWord_622376, baseEnd_622376] using wordTrace_append hprefix tailTrace_622376
  have hstable : (prefixWord ++ tailWord_622376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622376).length < 2 ^ (prefixWord ++ tailWord_622376).sum := by decide
  have hdescent : baseEnd_622376 < baseStart_622376 := by decide
  rcases family_descends (prefixWord ++ tailWord_622376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622426 : List Nat := [3, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2]
def baseStart_622426 : Nat := 118140960795 + 622426 * 2 ^ 59
def prefixEnd_622426 : Nat := 4983230072969 + 3 ^ 40 * 622426 * 2
def baseEnd_622426 : Nat := 319603709855486989112521

theorem tailTrace_622426 : CollatzResearch.WordTrace tailWord_622426 prefixEnd_622426 319603709855486989112521 := by
  unfold tailWord_622426
  simp only [CollatzResearch.WordTrace]
  refine ⟨5675435310766094685695783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15134494162042919161855421 5675435310766094685695783)
  ·
    refine ⟨8513152966149142028543675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5675435310766094685695783 8513152966149142028543675)
    ·
      refine ⟨12769729449223713042815513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8513152966149142028543675 12769729449223713042815513)
      ·
        refine ⟨9577297086917784782111635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12769729449223713042815513 9577297086917784782111635)
        ·
          refine ⟨14365945630376677173167453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9577297086917784782111635 14365945630376677173167453)
          ·
            refine ⟨5387229611391253939937795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14365945630376677173167453 5387229611391253939937795)
            ·
              refine ⟨8080844417086880909906693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5387229611391253939937795 8080844417086880909906693)
              ·
                refine ⟨1515158328203790170607505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8080844417086880909906693 1515158328203790170607505)
                ·
                  refine ⟨1136368746152842627955629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1515158328203790170607505 1136368746152842627955629)
                  ·
                    refine ⟨426138279807315985483361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1136368746152842627955629 426138279807315985483361)
                    ·
                      refine ⟨319603709855486989112521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 426138279807315985483361 319603709855486989112521)
                      ·
                        rfl

theorem cell23_622426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 4, 2, 3, 2].length) (baseStart_622426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622426 prefixEnd_622426 := by exact prefixLift 622426
  have htrace : WordTrace (prefixWord ++ tailWord_622426) baseStart_622426 baseEnd_622426 := by
    simpa [prefixWord, tailWord_622426, baseEnd_622426] using wordTrace_append hprefix tailTrace_622426
  have hstable : (prefixWord ++ tailWord_622426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622426).length < 2 ^ (prefixWord ++ tailWord_622426).sum := by decide
  have hdescent : baseEnd_622426 < baseStart_622426 := by decide
  rcases family_descends (prefixWord ++ tailWord_622426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622433 : List Nat := [1, 2, 3, 1, 1, 1, 5, 4, 1, 1, 3]
def baseStart_622433 : Nat := 118140960795 + 622433 * 2 ^ 59
def prefixEnd_622433 : Nat := 4983230072969 + 3 ^ 40 * 622433 * 2
def baseEnd_622433 : Nat := 319607304220068461724989

theorem tailTrace_622433 : CollatzResearch.WordTrace tailWord_622433 prefixEnd_622433 319607304220068461724989 := by
  unfold tailWord_622433
  simp only [CollatzResearch.WordTrace]
  refine ⟨22701996554039018938287953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15134664369359345958858635 22701996554039018938287953)
  ·
    refine ⟨17026497415529264203715965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22701996554039018938287953 17026497415529264203715965)
    ·
      refine ⟨6384936530823474076393487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17026497415529264203715965 6384936530823474076393487)
      ·
        refine ⟨9577404796235211114590231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6384936530823474076393487 9577404796235211114590231)
        ·
          refine ⟨14366107194352816671885347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9577404796235211114590231 14366107194352816671885347)
          ·
            refine ⟨21549160791529225007828021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14366107194352816671885347 21549160791529225007828021)
            ·
              refine ⟨2020233824205864844483877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21549160791529225007828021 2020233824205864844483877)
              ·
                refine ⟨378793842038599658340727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2020233824205864844483877 378793842038599658340727)
                ·
                  refine ⟨568190763057899487511091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 378793842038599658340727 568190763057899487511091)
                  ·
                    refine ⟨852286144586849231266637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 568190763057899487511091 852286144586849231266637)
                    ·
                      refine ⟨319607304220068461724989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 852286144586849231266637 319607304220068461724989)
                      ·
                        rfl

theorem cell23_622433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 4, 1, 1, 3].length) (baseStart_622433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622433 prefixEnd_622433 := by exact prefixLift 622433
  have htrace : WordTrace (prefixWord ++ tailWord_622433) baseStart_622433 baseEnd_622433 := by
    simpa [prefixWord, tailWord_622433, baseEnd_622433] using wordTrace_append hprefix tailTrace_622433
  have hstable : (prefixWord ++ tailWord_622433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622433).length < 2 ^ (prefixWord ++ tailWord_622433).sum := by decide
  have hdescent : baseEnd_622433 < baseStart_622433 := by decide
  rcases family_descends (prefixWord ++ tailWord_622433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622439 : List Nat := [1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_622439 : Nat := 118140960795 + 622439 * 2 ^ 59
def prefixEnd_622439 : Nat := 4983230072969 + 3 ^ 40 * 622439 * 2
def baseEnd_622439 : Nat := 319610385103995438249961

theorem tailTrace_622439 : CollatzResearch.WordTrace tailWord_622439 prefixEnd_622439 319610385103995438249961 := by
  unfold tailWord_622439
  simp only [CollatzResearch.WordTrace]
  refine ⟨22702215392017281963006371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15134810261344854642004247 22702215392017281963006371)
  ·
    refine ⟨34053323088025922944509557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22702215392017281963006371 34053323088025922944509557)
    ·
      refine ⟨3192499039502430276047771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34053323088025922944509557 3192499039502430276047771)
      ·
        refine ⟨4788748559253645414071657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3192499039502430276047771 4788748559253645414071657)
        ·
          refine ⟨3591561419440234060553743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4788748559253645414071657 3591561419440234060553743)
          ·
            refine ⟨5387342129160351090830615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3591561419440234060553743 5387342129160351090830615)
            ·
              refine ⟨8081013193740526636245923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5387342129160351090830615 8081013193740526636245923)
              ·
                refine ⟨12121519790610789954368885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8081013193740526636245923 12121519790610789954368885)
                ·
                  refine ⟨1136392480369761558222083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12121519790610789954368885 1136392480369761558222083)
                  ·
                    refine ⟨1704588720554642337333125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1136392480369761558222083 1704588720554642337333125)
                    ·
                      refine ⟨319610385103995438249961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1704588720554642337333125 319610385103995438249961)
                      ·
                        rfl

theorem cell23_622439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_622439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622439 prefixEnd_622439 := by exact prefixLift 622439
  have htrace : WordTrace (prefixWord ++ tailWord_622439) baseStart_622439 baseEnd_622439 := by
    simpa [prefixWord, tailWord_622439, baseEnd_622439] using wordTrace_append hprefix tailTrace_622439
  have hstable : (prefixWord ++ tailWord_622439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622439).length < 2 ^ (prefixWord ++ tailWord_622439).sum := by decide
  have hdescent : baseEnd_622439 < baseStart_622439 := by decide
  rcases family_descends (prefixWord ++ tailWord_622439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622449 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 1, 6]
def baseStart_622449 : Nat := 118140960795 + 622449 * 2 ^ 59
def prefixEnd_622449 : Nat := 4983230072969 + 3 ^ 40 * 622449 * 2
def baseEnd_622449 : Nat := 106538506636846799708305

theorem tailTrace_622449 : CollatzResearch.WordTrace tailWord_622449 prefixEnd_622449 106538506636846799708305 := by
  unfold tailWord_622449
  simp only [CollatzResearch.WordTrace]
  refine ⟨22702580121981053670870401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15135053414654035780580267 22702580121981053670870401)
  ·
    refine ⟨17026935091485790253152801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22702580121981053670870401 17026935091485790253152801)
    ·
      refine ⟨12770201318614342689864601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17026935091485790253152801 12770201318614342689864601)
      ·
        refine ⟨9577650988960757017398451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12770201318614342689864601 9577650988960757017398451)
        ·
          refine ⟨14366476483441135526097677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9577650988960757017398451 14366476483441135526097677)
          ·
            refine ⟨5387428681290425822286629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14366476483441135526097677 5387428681290425822286629)
            ·
              refine ⟨1010142877741954841678743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5387428681290425822286629 1010142877741954841678743)
              ·
                refine ⟨1515214316612932262518115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010142877741954841678743 1515214316612932262518115)
                ·
                  refine ⟨2272821474919398393777173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515214316612932262518115 2272821474919398393777173)
                  ·
                    refine ⟨106538506636846799708305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2272821474919398393777173 106538506636846799708305)
                    ·
                      rfl

theorem cell23_622449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 6].length) (baseStart_622449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622449 prefixEnd_622449 := by exact prefixLift 622449
  have htrace : WordTrace (prefixWord ++ tailWord_622449) baseStart_622449 baseEnd_622449 := by
    simpa [prefixWord, tailWord_622449, baseEnd_622449] using wordTrace_append hprefix tailTrace_622449
  have hstable : (prefixWord ++ tailWord_622449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622449).length < 2 ^ (prefixWord ++ tailWord_622449).sum := by decide
  have hdescent : baseEnd_622449 < baseStart_622449 := by decide
  rcases family_descends (prefixWord ++ tailWord_622449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622469 : List Nat := [1, 3, 1, 1, 3, 2, 1, 4, 1, 2, 4]
def baseStart_622469 : Nat := 118140960795 + 622469 * 2 ^ 59
def prefixEnd_622469 : Nat := 4983230072969 + 3 ^ 40 * 622469 * 2
def baseEnd_622469 : Nat := 319625789523630320874823

theorem tailTrace_622469 : CollatzResearch.WordTrace tailWord_622469 prefixEnd_622469 319625789523630320874823 := by
  unfold tailWord_622469
  simp only [CollatzResearch.WordTrace]
  refine ⟨22703309581908597086598461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15135539721272398057732307 22703309581908597086598461)
  ·
    refine ⟨8513741093215723907474423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22703309581908597086598461 8513741093215723907474423)
    ·
      refine ⟨12770611639823585861211635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8513741093215723907474423 12770611639823585861211635)
      ·
        refine ⟨19155917459735378791817453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12770611639823585861211635 19155917459735378791817453)
        ·
          refine ⟨7183469047400767046931545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19155917459735378791817453 7183469047400767046931545)
          ·
            refine ⟨5387601785550575285198659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7183469047400767046931545 5387601785550575285198659)
            ·
              refine ⟨8081402678325862927797989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5387601785550575285198659 8081402678325862927797989)
              ·
                refine ⟨1515263002186099298962123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8081402678325862927797989 1515263002186099298962123)
                ·
                  refine ⟨2272894503279148948443185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515263002186099298962123 2272894503279148948443185)
                  ·
                    refine ⟨1704670877459361711332389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2272894503279148948443185 1704670877459361711332389)
                    ·
                      refine ⟨319625789523630320874823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1704670877459361711332389 319625789523630320874823)
                      ·
                        rfl

theorem cell23_622469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 2, 4].length) (baseStart_622469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622469 prefixEnd_622469 := by exact prefixLift 622469
  have htrace : WordTrace (prefixWord ++ tailWord_622469) baseStart_622469 baseEnd_622469 := by
    simpa [prefixWord, tailWord_622469, baseEnd_622469] using wordTrace_append hprefix tailTrace_622469
  have hstable : (prefixWord ++ tailWord_622469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622469).length < 2 ^ (prefixWord ++ tailWord_622469).sum := by decide
  have hdescent : baseEnd_622469 < baseStart_622469 := by decide
  rcases family_descends (prefixWord ++ tailWord_622469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622489 : List Nat := [1, 2, 1, 2, 1, 3, 2, 2, 3, 3, 3]
def baseStart_622489 : Nat := 118140960795 + 622489 * 2 ^ 59
def prefixEnd_622489 : Nat := 4983230072969 + 3 ^ 40 * 622489 * 2
def baseEnd_622489 : Nat := 319636059136720242624731

theorem tailTrace_622489 : CollatzResearch.WordTrace tailWord_622489 prefixEnd_622489 319636059136720242624731 := by
  unfold tailWord_622489
  simp only [CollatzResearch.WordTrace]
  refine ⟨22704039041836140502326521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15136026027890760334884347 22704039041836140502326521)
  ·
    refine ⟨17028029281377105376744891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22704039041836140502326521 17028029281377105376744891)
    ·
      refine ⟨25542043922065658065117337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17028029281377105376744891 25542043922065658065117337)
      ·
        refine ⟨19156532941549243548838003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25542043922065658065117337 19156532941549243548838003)
        ·
          refine ⟨28734799412323865323257005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19156532941549243548838003 28734799412323865323257005)
          ·
            refine ⟨10775549779621449496221377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28734799412323865323257005 10775549779621449496221377)
            ·
              refine ⟨8081662334716087122166033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10775549779621449496221377 8081662334716087122166033)
              ·
                refine ⟨6061246751037065341624525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8081662334716087122166033 6061246751037065341624525)
                ·
                  refine ⟨2272967531638899503109197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6061246751037065341624525 2272967531638899503109197)
                  ·
                    refine ⟨852362824364587313665949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2272967531638899503109197 852362824364587313665949)
                    ·
                      refine ⟨319636059136720242624731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 852362824364587313665949 319636059136720242624731)
                      ·
                        rfl

theorem cell23_622489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_622489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622489 prefixEnd_622489 := by exact prefixLift 622489
  have htrace : WordTrace (prefixWord ++ tailWord_622489) baseStart_622489 baseEnd_622489 := by
    simpa [prefixWord, tailWord_622489, baseEnd_622489] using wordTrace_append hprefix tailTrace_622489
  have hstable : (prefixWord ++ tailWord_622489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622489).length < 2 ^ (prefixWord ++ tailWord_622489).sum := by decide
  have hdescent : baseEnd_622489 < baseStart_622489 := by decide
  rcases family_descends (prefixWord ++ tailWord_622489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622490 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2]
def baseStart_622490 : Nat := 118140960795 + 622490 * 2 ^ 59
def prefixEnd_622490 : Nat := 4983230072969 + 3 ^ 40 * 622490 * 2
def baseEnd_622490 : Nat := 319636572617374738712227

theorem tailTrace_622490 : CollatzResearch.WordTrace tailWord_622490 prefixEnd_622490 319636572617374738712227 := by
  unfold tailWord_622490
  simp only [CollatzResearch.WordTrace]
  refine ⟨5676018878708129418278231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15136050343221678448741949 5676018878708129418278231)
  ·
    refine ⟨8514028318062194127417347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5676018878708129418278231 8514028318062194127417347)
    ·
      refine ⟨12771042477093291191126021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8514028318062194127417347 12771042477093291191126021)
      ·
        refine ⟨2394570464454992098336129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12771042477093291191126021 2394570464454992098336129)
        ·
          refine ⟨1795927848341244073752097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2394570464454992098336129 1795927848341244073752097)
          ·
            refine ⟨1346945886255933055314073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1795927848341244073752097 1346945886255933055314073)
            ·
              refine ⟨1010209414691949791485555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1346945886255933055314073 1010209414691949791485555)
              ·
                refine ⟨1515314122037924687228333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010209414691949791485555 1515314122037924687228333)
                ·
                  refine ⟨568242795764221757710625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1515314122037924687228333 568242795764221757710625)
                  ·
                    refine ⟨426182096823166318282969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 568242795764221757710625 426182096823166318282969)
                    ·
                      refine ⟨319636572617374738712227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 426182096823166318282969 319636572617374738712227)
                      ·
                        rfl

theorem cell23_622490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 3, 2, 2].length) (baseStart_622490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622490 prefixEnd_622490 := by exact prefixLift 622490
  have htrace : WordTrace (prefixWord ++ tailWord_622490) baseStart_622490 baseEnd_622490 := by
    simpa [prefixWord, tailWord_622490, baseEnd_622490] using wordTrace_append hprefix tailTrace_622490
  have hstable : (prefixWord ++ tailWord_622490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622490).length < 2 ^ (prefixWord ++ tailWord_622490).sum := by decide
  have hdescent : baseEnd_622490 < baseStart_622490 := by decide
  rcases family_descends (prefixWord ++ tailWord_622490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622503 : List Nat := [1, 1, 6, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_622503 : Nat := 118140960795 + 622503 * 2 ^ 59
def prefixEnd_622503 : Nat := 4983230072969 + 3 ^ 40 * 622503 * 2
def baseEnd_622503 : Nat := 319643247865883187849667

theorem tailTrace_622503 : CollatzResearch.WordTrace tailWord_622503 prefixEnd_622503 319643247865883187849667 := by
  unfold tailWord_622503
  simp only [CollatzResearch.WordTrace]
  refine ⟨22704549663785420893336163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15136366442523613928890775 22704549663785420893336163)
  ·
    refine ⟨34056824495678131340004245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22704549663785420893336163 34056824495678131340004245)
    ·
      refine ⟨1596413648234912406562699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34056824495678131340004245 1596413648234912406562699)
      ·
        refine ⟨2394620472352368609844049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1596413648234912406562699 2394620472352368609844049)
        ·
          refine ⟨1795965354264276457383037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2394620472352368609844049 1795965354264276457383037)
          ·
            refine ⟨673487007849103671518639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1795965354264276457383037 673487007849103671518639)
            ·
              refine ⟨1010230511773655507277959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673487007849103671518639 1010230511773655507277959)
              ·
                refine ⟨1515345767660483260916939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010230511773655507277959 1515345767660483260916939)
                ·
                  refine ⟨2273018651490724891375409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515345767660483260916939 2273018651490724891375409)
                  ·
                    refine ⟨1704763988618043668531557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2273018651490724891375409 1704763988618043668531557)
                    ·
                      refine ⟨319643247865883187849667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1704763988618043668531557 319643247865883187849667)
                      ·
                        rfl

theorem cell23_622503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_622503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622503 prefixEnd_622503 := by exact prefixLift 622503
  have htrace : WordTrace (prefixWord ++ tailWord_622503) baseStart_622503 baseEnd_622503 := by
    simpa [prefixWord, tailWord_622503, baseEnd_622503] using wordTrace_append hprefix tailTrace_622503
  have hstable : (prefixWord ++ tailWord_622503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622503).length < 2 ^ (prefixWord ++ tailWord_622503).sum := by decide
  have hdescent : baseEnd_622503 < baseStart_622503 := by decide
  rcases family_descends (prefixWord ++ tailWord_622503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622567 : List Nat := [1, 1, 5, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_622567 : Nat := 118140960795 + 622567 * 2 ^ 59
def prefixEnd_622567 : Nat := 4983230072969 + 3 ^ 40 * 622567 * 2
def baseEnd_622567 : Nat := 319676110627770937449373

theorem tailTrace_622567 : CollatzResearch.WordTrace tailWord_622567 prefixEnd_622567 319676110627770937449373 := by
  unfold tailWord_622567
  simp only [CollatzResearch.WordTrace]
  refine ⟨22706883935553559823665955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15137922623702373215777303 22706883935553559823665955)
  ·
    refine ⟨34060325903330339735498933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22706883935553559823665955 34060325903330339735498933)
    ·
      refine ⟨3193155553437219350203025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34060325903330339735498933 3193155553437219350203025)
      ·
        refine ⟨2394866665077914512652269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3193155553437219350203025 2394866665077914512652269)
        ·
          refine ⟨898074999404217942244601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2394866665077914512652269 898074999404217942244601)
          ·
            refine ⟨673556249553163456683451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 898074999404217942244601 673556249553163456683451)
            ·
              refine ⟨1010334374329745185025177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 673556249553163456683451 1010334374329745185025177)
              ·
                refine ⟨757750780747308888768883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010334374329745185025177 757750780747308888768883)
                ·
                  refine ⟨1136626171120963333153325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 757750780747308888768883 1136626171120963333153325)
                  ·
                    refine ⟨426234814170361249932497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1136626171120963333153325 426234814170361249932497)
                    ·
                      refine ⟨319676110627770937449373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 426234814170361249932497 319676110627770937449373)
                      ·
                        rfl

theorem cell23_622567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_622567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622567 prefixEnd_622567 := by exact prefixLift 622567
  have htrace : WordTrace (prefixWord ++ tailWord_622567) baseStart_622567 baseEnd_622567 := by
    simpa [prefixWord, tailWord_622567, baseEnd_622567] using wordTrace_append hprefix tailTrace_622567
  have hstable : (prefixWord ++ tailWord_622567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622567).length < 2 ^ (prefixWord ++ tailWord_622567).sum := by decide
  have hdescent : baseEnd_622567 < baseStart_622567 := by decide
  rcases family_descends (prefixWord ++ tailWord_622567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622613 : List Nat := [1, 3, 2, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_622613 : Nat := 118140960795 + 622613 * 2 ^ 59
def prefixEnd_622613 : Nat := 4983230072969 + 3 ^ 40 * 622613 * 2
def baseEnd_622613 : Nat := 319699730737877757474161

theorem tailTrace_622613 : CollatzResearch.WordTrace tailWord_622613 prefixEnd_622613 319699730737877757474161 := by
  unfold tailWord_622613
  simp only [CollatzResearch.WordTrace]
  refine ⟨22708561693386909679840493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15139041128924606453226995 22708561693386909679840493)
  ·
    refine ⟨8515710635020091129940185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22708561693386909679840493 8515710635020091129940185)
    ·
      refine ⟨6386782976265068347455139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8515710635020091129940185 6386782976265068347455139)
      ·
        refine ⟨9580174464397602521182709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6386782976265068347455139 9580174464397602521182709)
        ·
          refine ⟨898141356037275236360879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9580174464397602521182709 898141356037275236360879)
          ·
            refine ⟨1347212034055912854541319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 898141356037275236360879 1347212034055912854541319)
            ·
              refine ⟨2020818051083869281811979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347212034055912854541319 2020818051083869281811979)
              ·
                refine ⟨3031227076625803922717969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2020818051083869281811979 3031227076625803922717969)
                ·
                  refine ⟨2273420307469352942038477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3031227076625803922717969 2273420307469352942038477)
                  ·
                    refine ⟨852532615301007353264429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2273420307469352942038477 852532615301007353264429)
                    ·
                      refine ⟨319699730737877757474161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 852532615301007353264429 319699730737877757474161)
                      ·
                        rfl

theorem cell23_622613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_622613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622613 prefixEnd_622613 := by exact prefixLift 622613
  have htrace : WordTrace (prefixWord ++ tailWord_622613) baseStart_622613 baseEnd_622613 := by
    simpa [prefixWord, tailWord_622613, baseEnd_622613] using wordTrace_append hprefix tailTrace_622613
  have hstable : (prefixWord ++ tailWord_622613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622613).length < 2 ^ (prefixWord ++ tailWord_622613).sum := by decide
  have hdescent : baseEnd_622613 < baseStart_622613 := by decide
  rcases family_descends (prefixWord ++ tailWord_622613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622636 : List Nat := [2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 4]
def baseStart_622636 : Nat := 118140960795 + 622636 * 2 ^ 59
def prefixEnd_622636 : Nat := 4983230072969 + 3 ^ 40 * 622636 * 2
def baseEnd_622636 : Nat := 319711540792931167486555

theorem tailTrace_622636 : CollatzResearch.WordTrace tailWord_622636 prefixEnd_622636 319711540792931167486555 := by
  unfold tailWord_622636
  simp only [CollatzResearch.WordTrace]
  refine ⟨11354700286151792303963881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15139600381535723071951841 11354700286151792303963881)
  ·
    refine ⟨8516025214613844227972911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11354700286151792303963881 8516025214613844227972911)
    ·
      refine ⟨12774037821920766341959367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8516025214613844227972911 12774037821920766341959367)
      ·
        refine ⟨19161056732881149512939051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12774037821920766341959367 19161056732881149512939051)
        ·
          refine ⟨28741585099321724269408577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19161056732881149512939051 28741585099321724269408577)
          ·
            refine ⟨21556188824491293202056433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28741585099321724269408577 21556188824491293202056433)
            ·
              refine ⟨16167141618368469901542325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21556188824491293202056433 16167141618368469901542325)
              ·
                refine ⟨1515669526722044053269593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16167141618368469901542325 1515669526722044053269593)
                ·
                  refine ⟨1136752145041533039952195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1515669526722044053269593 1136752145041533039952195)
                  ·
                    refine ⟨1705128217562299559928293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1136752145041533039952195 1705128217562299559928293)
                    ·
                      refine ⟨319711540792931167486555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1705128217562299559928293 319711540792931167486555)
                      ·
                        rfl

theorem cell23_622636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_622636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622636 prefixEnd_622636 := by exact prefixLift 622636
  have htrace : WordTrace (prefixWord ++ tailWord_622636) baseStart_622636 baseEnd_622636 := by
    simpa [prefixWord, tailWord_622636, baseEnd_622636] using wordTrace_append hprefix tailTrace_622636
  have hstable : (prefixWord ++ tailWord_622636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622636).length < 2 ^ (prefixWord ++ tailWord_622636).sum := by decide
  have hdescent : baseEnd_622636 < baseStart_622636 := by decide
  rcases family_descends (prefixWord ++ tailWord_622636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622639 : List Nat := [1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 5]
def baseStart_622639 : Nat := 118140960795 + 622639 * 2 ^ 59
def prefixEnd_622639 : Nat := 4983230072969 + 3 ^ 40 * 622639 * 2
def baseEnd_622639 : Nat := 319713081234894655749041

theorem tailTrace_622639 : CollatzResearch.WordTrace tailWord_622639 prefixEnd_622639 319713081234894655749041 := by
  unfold tailWord_622639
  simp only [CollatzResearch.WordTrace]
  refine ⟨22709509991292716120286971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15139673327528477413524647 22709509991292716120286971)
  ·
    refine ⟨34064264986939074180430457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22709509991292716120286971 34064264986939074180430457)
    ·
      refine ⟨25548198740204305635322843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34064264986939074180430457 25548198740204305635322843)
      ·
        refine ⟨38322298110306458452984265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25548198740204305635322843 38322298110306458452984265)
        ·
          refine ⟨28741723582729843839738199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38322298110306458452984265 28741723582729843839738199)
          ·
            refine ⟨43112585374094765759607299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28741723582729843839738199 43112585374094765759607299)
            ·
              refine ⟨64668878061142148639410949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43112585374094765759607299 64668878061142148639410949)
              ·
                refine ⟨12125414636464152869889553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64668878061142148639410949 12125414636464152869889553)
                ·
                  refine ⟨9094060977348114652417165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12125414636464152869889553 9094060977348114652417165)
                  ·
                    refine ⟨3410272866505542994656437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9094060977348114652417165 3410272866505542994656437)
                    ·
                      refine ⟨319713081234894655749041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3410272866505542994656437 319713081234894655749041)
                      ·
                        rfl

theorem cell23_622639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_622639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622639 prefixEnd_622639 := by exact prefixLift 622639
  have htrace : WordTrace (prefixWord ++ tailWord_622639) baseStart_622639 baseEnd_622639 := by
    simpa [prefixWord, tailWord_622639, baseEnd_622639] using wordTrace_append hprefix tailTrace_622639
  have hstable : (prefixWord ++ tailWord_622639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622639).length < 2 ^ (prefixWord ++ tailWord_622639).sum := by decide
  have hdescent : baseEnd_622639 < baseStart_622639 := by decide
  rcases family_descends (prefixWord ++ tailWord_622639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622653 : List Nat := [1, 4, 1, 3, 1, 1, 1, 1, 4, 4, 2]
def baseStart_622653 : Nat := 118140960795 + 622653 * 2 ^ 59
def prefixEnd_622653 : Nat := 4983230072969 + 3 ^ 40 * 622653 * 2
def baseEnd_622653 : Nat := 319720269964057600973977

theorem tailTrace_622653 : CollatzResearch.WordTrace tailWord_622653 prefixEnd_622653 319720269964057600973977 := by
  unfold tailWord_622653
  simp only [CollatzResearch.WordTrace]
  refine ⟨22710020613241996511296613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15140013742161331007531075 22710020613241996511296613)
  ·
    refine ⟨4258128864982874345868115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22710020613241996511296613 4258128864982874345868115)
    ·
      refine ⟨6387193297474311518802173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4258128864982874345868115 6387193297474311518802173)
      ·
        refine ⟨2395197486552866819550815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6387193297474311518802173 2395197486552866819550815)
        ·
          refine ⟨3592796229829300229326223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2395197486552866819550815 3592796229829300229326223)
          ·
            refine ⟨5389194344743950343989335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3592796229829300229326223 5389194344743950343989335)
            ·
              refine ⟨8083791517115925515984003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5389194344743950343989335 8083791517115925515984003)
              ·
                refine ⟨12125687275673888273976005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8083791517115925515984003 12125687275673888273976005)
                ·
                  refine ⟨2273566364188854051370501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12125687275673888273976005 2273566364188854051370501)
                  ·
                    refine ⟨426293693285410134631969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2273566364188854051370501 426293693285410134631969)
                    ·
                      refine ⟨319720269964057600973977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 426293693285410134631969 319720269964057600973977)
                      ·
                        rfl

theorem cell23_622653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_622653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622653 prefixEnd_622653 := by exact prefixLift 622653
  have htrace : WordTrace (prefixWord ++ tailWord_622653) baseStart_622653 baseEnd_622653 := by
    simpa [prefixWord, tailWord_622653, baseEnd_622653] using wordTrace_append hprefix tailTrace_622653
  have hstable : (prefixWord ++ tailWord_622653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622653).length < 2 ^ (prefixWord ++ tailWord_622653).sum := by decide
  have hdescent : baseEnd_622653 < baseStart_622653 := by decide
  rcases family_descends (prefixWord ++ tailWord_622653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622663 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 3, 4]
def baseStart_622663 : Nat := 118140960795 + 622663 * 2 ^ 59
def prefixEnd_622663 : Nat := 4983230072969 + 3 ^ 40 * 622663 * 2
def baseEnd_622663 : Nat := 106575134923534187282977

theorem tailTrace_622663 : CollatzResearch.WordTrace tailWord_622663 prefixEnd_622663 106575134923534187282977 := by
  unfold tailWord_622663
  simp only [CollatzResearch.WordTrace]
  refine ⟨22710385343205768219160643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15140256895470512146107095 22710385343205768219160643)
  ·
    refine ⟨34065578014808652328740965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22710385343205768219160643 34065578014808652328740965)
    ·
      refine ⟨6387295877776622311638931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34065578014808652328740965 6387295877776622311638931)
      ·
        refine ⟨9580943816664933467458397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6387295877776622311638931 9580943816664933467458397)
        ·
          refine ⟨3592853931249350050296899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9580943816664933467458397 3592853931249350050296899)
          ·
            refine ⟨5389280896874025075445349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3592853931249350050296899 5389280896874025075445349)
            ·
              refine ⟨1010490168163879701646003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5389280896874025075445349 1010490168163879701646003)
              ·
                refine ⟨1515735252245819552469005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1010490168163879701646003 1515735252245819552469005)
                ·
                  refine ⟨568400719592182332175877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1515735252245819552469005 568400719592182332175877)
                  ·
                    refine ⟨106575134923534187282977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 568400719592182332175877 106575134923534187282977)
                    ·
                      rfl

theorem cell23_622663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_622663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622663 prefixEnd_622663 := by exact prefixLift 622663
  have htrace : WordTrace (prefixWord ++ tailWord_622663) baseStart_622663 baseEnd_622663 := by
    simpa [prefixWord, tailWord_622663, baseEnd_622663] using wordTrace_append hprefix tailTrace_622663
  have hstable : (prefixWord ++ tailWord_622663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622663).length < 2 ^ (prefixWord ++ tailWord_622663).sum := by decide
  have hdescent : baseEnd_622663 < baseStart_622663 := by decide
  rcases family_descends (prefixWord ++ tailWord_622663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622736 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 1, 6]
def baseStart_622736 : Nat := 118140960795 + 622736 * 2 ^ 59
def prefixEnd_622736 : Nat := 4983230072969 + 3 ^ 40 * 622736 * 2
def baseEnd_622736 : Nat := 106587629619460258745365

theorem tailTrace_622736 : CollatzResearch.WordTrace tailWord_622736 prefixEnd_622736 106587629619460258745365 := by
  unfold tailWord_622736
  simp only [CollatzResearch.WordTrace]
  refine ⟨11356523935970650843284031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15142031914627534457712041 11356523935970650843284031)
  ·
    refine ⟨17034785903955976264926047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11356523935970650843284031 17034785903955976264926047)
    ·
      refine ⟨25552178855933964397389071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17034785903955976264926047 25552178855933964397389071)
      ·
        refine ⟨38328268283900946596083607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25552178855933964397389071 38328268283900946596083607)
        ·
          refine ⟨57492402425851419894125411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38328268283900946596083607 57492402425851419894125411)
          ·
            refine ⟨86238603638777129841188117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57492402425851419894125411 86238603638777129841188117)
            ·
              refine ⟨4042434545567677961305693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86238603638777129841188117 4042434545567677961305693)
              ·
                refine ⟨1515912954587879235489635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4042434545567677961305693 1515912954587879235489635)
                ·
                  refine ⟨2273869431881818853234453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515912954587879235489635 2273869431881818853234453)
                  ·
                    refine ⟨106587629619460258745365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2273869431881818853234453 106587629619460258745365)
                    ·
                      rfl

theorem cell23_622736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 1, 6].length) (baseStart_622736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622736 prefixEnd_622736 := by exact prefixLift 622736
  have htrace : WordTrace (prefixWord ++ tailWord_622736) baseStart_622736 baseEnd_622736 := by
    simpa [prefixWord, tailWord_622736, baseEnd_622736] using wordTrace_append hprefix tailTrace_622736
  have hstable : (prefixWord ++ tailWord_622736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622736).length < 2 ^ (prefixWord ++ tailWord_622736).sum := by decide
  have hdescent : baseEnd_622736 < baseStart_622736 := by decide
  rcases family_descends (prefixWord ++ tailWord_622736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622753 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 1, 6]
def baseStart_622753 : Nat := 118140960795 + 622753 * 2 ^ 59
def prefixEnd_622753 : Nat := 4983230072969 + 3 ^ 40 * 622753 * 2
def baseEnd_622753 : Nat := 106590539343169069907839

theorem tailTrace_622753 : CollatzResearch.WordTrace tailWord_622753 prefixEnd_622753 106590539343169069907839 := by
  unfold tailWord_622753
  simp only [CollatzResearch.WordTrace]
  refine ⟨22713667912879713589936913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15142445275253142393291275 22713667912879713589936913)
  ·
    refine ⟨17035250934659785192452685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22713667912879713589936913 17035250934659785192452685)
    ·
      refine ⟨6388219100497419447169757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17035250934659785192452685 6388219100497419447169757)
      ·
        refine ⟨2395582162686532292688659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6388219100497419447169757 2395582162686532292688659)
        ·
          refine ⟨3593373244029798439032989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2395582162686532292688659 3593373244029798439032989)
          ·
            refine ⟨1347514966511174414637371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3593373244029798439032989 1347514966511174414637371)
            ·
              refine ⟨2021272449766761621956057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347514966511174414637371 2021272449766761621956057)
              ·
                refine ⟨1515954337325071216467043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2021272449766761621956057 1515954337325071216467043)
                ·
                  refine ⟨2273931505987606824700565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1515954337325071216467043 2273931505987606824700565)
                  ·
                    refine ⟨106590539343169069907839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2273931505987606824700565 106590539343169069907839)
                    ·
                      rfl

theorem cell23_622753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 6].length) (baseStart_622753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622753 prefixEnd_622753 := by exact prefixLift 622753
  have htrace : WordTrace (prefixWord ++ tailWord_622753) baseStart_622753 baseEnd_622753 := by
    simpa [prefixWord, tailWord_622753, baseEnd_622753] using wordTrace_append hprefix tailTrace_622753
  have hstable : (prefixWord ++ tailWord_622753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622753).length < 2 ^ (prefixWord ++ tailWord_622753).sum := by decide
  have hdescent : baseEnd_622753 < baseStart_622753 := by decide
  rcases family_descends (prefixWord ++ tailWord_622753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622770 : List Nat := [3, 2, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_622770 : Nat := 118140960795 + 622770 * 2 ^ 59
def prefixEnd_622770 : Nat := 4983230072969 + 3 ^ 40 * 622770 * 2
def baseEnd_622770 : Nat := 106593449066877881070313

theorem tailTrace_622770 : CollatzResearch.WordTrace tailWord_622770 prefixEnd_622770 106593449066877881070313 := by
  unfold tailWord_622770
  simp only [CollatzResearch.WordTrace]
  refine ⟨5678571988454531373326441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15142858635878750328870509 5678571988454531373326441)
  ·
    refine ⟨4258928991340898529994831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5678571988454531373326441 4258928991340898529994831)
    ·
      refine ⟨6388393487011347794992247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4258928991340898529994831 6388393487011347794992247)
      ·
        refine ⟨9582590230517021692488371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6388393487011347794992247 9582590230517021692488371)
        ·
          refine ⟨14373885345775532538732557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9582590230517021692488371 14373885345775532538732557)
          ·
            refine ⟨5390207004665824702024709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14373885345775532538732557 5390207004665824702024709)
            ·
              refine ⟨1010663813374842131629633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5390207004665824702024709 1010663813374842131629633)
              ·
                refine ⟨757997860031131598722225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1010663813374842131629633 757997860031131598722225)
                ·
                  refine ⟨568498395023348699041669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 757997860031131598722225 568498395023348699041669)
                  ·
                    refine ⟨106593449066877881070313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 568498395023348699041669 106593449066877881070313)
                    ·
                      rfl

theorem cell23_622770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_622770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622770 prefixEnd_622770 := by exact prefixLift 622770
  have htrace : WordTrace (prefixWord ++ tailWord_622770) baseStart_622770 baseEnd_622770 := by
    simpa [prefixWord, tailWord_622770, baseEnd_622770] using wordTrace_append hprefix tailTrace_622770
  have hstable : (prefixWord ++ tailWord_622770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622770).length < 2 ^ (prefixWord ++ tailWord_622770).sum := by decide
  have hdescent : baseEnd_622770 < baseStart_622770 := by decide
  rcases family_descends (prefixWord ++ tailWord_622770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622844 : List Nat := [2, 2, 2, 1, 4, 2, 3, 1, 2, 1, 3]
def baseStart_622844 : Nat := 118140960795 + 622844 * 2 ^ 59
def prefixEnd_622844 : Nat := 4983230072969 + 3 ^ 40 * 622844 * 2
def baseEnd_622844 : Nat := 319818344769066353685599

theorem tailTrace_622844 : CollatzResearch.WordTrace tailWord_622844 prefixEnd_622844 319818344769066353685599 := by
  unfold tailWord_622844
  simp only [CollatzResearch.WordTrace]
  refine ⟨11358493477775018065749793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15144657970366690754333057 11358493477775018065749793)
  ·
    refine ⟨8518870108331263549312345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11358493477775018065749793 8518870108331263549312345)
    ·
      refine ⟨6389152581248447661984259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8518870108331263549312345 6389152581248447661984259)
      ·
        refine ⟨9583728871872671492976389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6389152581248447661984259 9583728871872671492976389)
        ·
          refine ⟨1796949163476125904933073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9583728871872671492976389 1796949163476125904933073)
          ·
            refine ⟨1347711872607094428699805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1796949163476125904933073 1347711872607094428699805)
            ·
              refine ⟨505391952227660410762427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1347711872607094428699805 505391952227660410762427)
              ·
                refine ⟨758087928341490616143641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505391952227660410762427 758087928341490616143641)
                ·
                  refine ⟨568565946256117962107731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 758087928341490616143641 568565946256117962107731)
                  ·
                    refine ⟨852848919384176943161597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 568565946256117962107731 852848919384176943161597)
                    ·
                      refine ⟨319818344769066353685599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 852848919384176943161597 319818344769066353685599)
                      ·
                        rfl

theorem cell23_622844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_622844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622844 prefixEnd_622844 := by exact prefixLift 622844
  have htrace : WordTrace (prefixWord ++ tailWord_622844) baseStart_622844 baseEnd_622844 := by
    simpa [prefixWord, tailWord_622844, baseEnd_622844] using wordTrace_append hprefix tailTrace_622844
  have hstable : (prefixWord ++ tailWord_622844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622844).length < 2 ^ (prefixWord ++ tailWord_622844).sum := by decide
  have hdescent : baseEnd_622844 < baseStart_622844 := by decide
  rcases family_descends (prefixWord ++ tailWord_622844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622957 : List Nat := [1, 5, 1, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_622957 : Nat := 118140960795 + 622957 * 2 ^ 59
def prefixEnd_622957 : Nat := 4983230072969 + 3 ^ 40 * 622957 * 2
def baseEnd_622957 : Nat := 319876368083024411572579

theorem tailTrace_622957 : CollatzResearch.WordTrace tailWord_622957 prefixEnd_622957 319876368083024411572579 := by
  unfold tailWord_622957
  simp only [CollatzResearch.WordTrace]
  refine ⟨22721108404140656430363125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15147405602760437620242083 22721108404140656430363125)
  ·
    refine ⟨2130103912888186540346543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22721108404140656430363125 2130103912888186540346543)
    ·
      refine ⟨3195155869332279810519815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2130103912888186540346543 3195155869332279810519815)
      ·
        refine ⟨4792733803998419715779723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3195155869332279810519815 4792733803998419715779723)
        ·
          refine ⟨7189100705997629573669585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4792733803998419715779723 7189100705997629573669585)
          ·
            refine ⟨5391825529498222180252189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7189100705997629573669585 5391825529498222180252189)
            ·
              refine ⟨2021934573561833317594571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5391825529498222180252189 2021934573561833317594571)
              ·
                refine ⟨3032901860342749976391857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2021934573561833317594571 3032901860342749976391857)
                ·
                  refine ⟨2274676395257062482293893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3032901860342749976391857 2274676395257062482293893)
                  ·
                    refine ⟨426501824110699215430105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2274676395257062482293893 426501824110699215430105)
                    ·
                      refine ⟨319876368083024411572579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 426501824110699215430105 319876368083024411572579)
                      ·
                        rfl

theorem cell23_622957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_622957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622957 prefixEnd_622957 := by exact prefixLift 622957
  have htrace : WordTrace (prefixWord ++ tailWord_622957) baseStart_622957 baseEnd_622957 := by
    simpa [prefixWord, tailWord_622957, baseEnd_622957] using wordTrace_append hprefix tailTrace_622957
  have hstable : (prefixWord ++ tailWord_622957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622957).length < 2 ^ (prefixWord ++ tailWord_622957).sum := by decide
  have hdescent : baseEnd_622957 < baseStart_622957 := by decide
  rcases family_descends (prefixWord ++ tailWord_622957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622977 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 1, 4, 3]
def baseStart_622977 : Nat := 118140960795 + 622977 * 2 ^ 59
def prefixEnd_622977 : Nat := 4983230072969 + 3 ^ 40 * 622977 * 2
def baseEnd_622977 : Nat := 319886637696114333322487

theorem tailTrace_622977 : CollatzResearch.WordTrace tailWord_622977 prefixEnd_622977 319886637696114333322487 := by
  unfold tailWord_622977
  simp only [CollatzResearch.WordTrace]
  refine ⟨22721837864068199846091185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15147891909378799897394123 22721837864068199846091185)
  ·
    refine ⟨17041378398051149884568389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22721837864068199846091185 17041378398051149884568389)
    ·
      refine ⟨3195258449634590603356573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17041378398051149884568389 3195258449634590603356573)
      ·
        refine ⟨1198221918612971476258715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3195258449634590603356573 1198221918612971476258715)
        ·
          refine ⟨1797332877919457214388073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198221918612971476258715 1797332877919457214388073)
          ·
            refine ⟨1347999658439592910791055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1797332877919457214388073 1347999658439592910791055)
            ·
              refine ⟨2021999487659389366186583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1347999658439592910791055 2021999487659389366186583)
              ·
                refine ⟨3032999231489084049279875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2021999487659389366186583 3032999231489084049279875)
                ·
                  refine ⟨4549498847233626073919813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3032999231489084049279875 4549498847233626073919813)
                  ·
                    refine ⟨853031033856304888859965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4549498847233626073919813 853031033856304888859965)
                    ·
                      refine ⟨319886637696114333322487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 853031033856304888859965 319886637696114333322487)
                      ·
                        rfl

theorem cell23_622977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_622977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622977 prefixEnd_622977 := by exact prefixLift 622977
  have htrace : WordTrace (prefixWord ++ tailWord_622977) baseStart_622977 baseEnd_622977 := by
    simpa [prefixWord, tailWord_622977, baseEnd_622977] using wordTrace_append hprefix tailTrace_622977
  have hstable : (prefixWord ++ tailWord_622977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622977).length < 2 ^ (prefixWord ++ tailWord_622977).sum := by decide
  have hdescent : baseEnd_622977 < baseStart_622977 := by decide
  rcases family_descends (prefixWord ++ tailWord_622977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_622984 : List Nat := [2, 1, 3, 3, 1, 1, 4, 3, 1, 4]
def baseStart_622984 : Nat := 118140960795 + 622984 * 2 ^ 59
def prefixEnd_622984 : Nat := 4983230072969 + 3 ^ 40 * 622984 * 2
def baseEnd_622984 : Nat := 106630077353565268644985

theorem tailTrace_622984 : CollatzResearch.WordTrace tailWord_622984 prefixEnd_622984 106630077353565268644985 := by
  unfold tailWord_622984
  simp only [CollatzResearch.WordTrace]
  refine ⟨11361046587521420020798003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15148062116695226694397337 11361046587521420020798003)
  ·
    refine ⟨17041569881282130031197005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11361046587521420020798003 17041569881282130031197005)
    ·
      refine ⟨6390588705480798761698877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17041569881282130031197005 6390588705480798761698877)
      ·
        refine ⟨2396470764555299535637079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6390588705480798761698877 2396470764555299535637079)
        ·
          refine ⟨3594706146832949303455619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2396470764555299535637079 3594706146832949303455619)
          ·
            refine ⟨5392059220249423955183429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3594706146832949303455619 5392059220249423955183429)
            ·
              refine ⟨1011011103796766991596893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5392059220249423955183429 1011011103796766991596893)
              ·
                refine ⟨379129163923787621848835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1011011103796766991596893 379129163923787621848835)
                ·
                  refine ⟨568693745885681432773253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379129163923787621848835 568693745885681432773253)
                  ·
                    refine ⟨106630077353565268644985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 568693745885681432773253 106630077353565268644985)
                    ·
                      rfl

theorem cell23_622984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_622984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_622984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_622984 prefixEnd_622984 := by exact prefixLift 622984
  have htrace : WordTrace (prefixWord ++ tailWord_622984) baseStart_622984 baseEnd_622984 := by
    simpa [prefixWord, tailWord_622984, baseEnd_622984] using wordTrace_append hprefix tailTrace_622984
  have hstable : (prefixWord ++ tailWord_622984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_622984).length < 2 ^ (prefixWord ++ tailWord_622984).sum := by decide
  have hdescent : baseEnd_622984 < baseStart_622984 := by decide
  rcases family_descends (prefixWord ++ tailWord_622984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623000 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 1, 2, 6]
def baseStart_623000 : Nat := 118140960795 + 623000 * 2 ^ 59
def prefixEnd_623000 : Nat := 4983230072969 + 3 ^ 40 * 623000 * 2
def baseEnd_623000 : Nat := 319898447751167743334881

theorem tailTrace_623000 : CollatzResearch.WordTrace tailWord_623000 prefixEnd_623000 319898447751167743334881 := by
  unfold tailWord_623000
  simp only [CollatzResearch.WordTrace]
  refine ⟨11361338371492437387089227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15148451161989916516118969 11361338371492437387089227)
  ·
    refine ⟨17042007557238656080633841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11361338371492437387089227 17042007557238656080633841)
    ·
      refine ⟨12781505667928992060475381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17042007557238656080633841 12781505667928992060475381)
      ·
        refine ⟨1198266156368343005669567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12781505667928992060475381 1198266156368343005669567)
        ·
          refine ⟨1797399234552514508504351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198266156368343005669567 1797399234552514508504351)
          ·
            refine ⟨2696098851828771762756527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1797399234552514508504351 2696098851828771762756527)
            ·
              refine ⟨4044148277743157644134791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2696098851828771762756527 4044148277743157644134791)
              ·
                refine ⟨6066222416614736466202187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4044148277743157644134791 6066222416614736466202187)
                ·
                  refine ⟨9099333624922104699303281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6066222416614736466202187 9099333624922104699303281)
                  ·
                    refine ⟨6824500218691578524477461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9099333624922104699303281 6824500218691578524477461)
                    ·
                      refine ⟨319898447751167743334881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6824500218691578524477461 319898447751167743334881)
                      ·
                        rfl

theorem cell23_623000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_623000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623000 prefixEnd_623000 := by exact prefixLift 623000
  have htrace : WordTrace (prefixWord ++ tailWord_623000) baseStart_623000 baseEnd_623000 := by
    simpa [prefixWord, tailWord_623000, baseEnd_623000] using wordTrace_append hprefix tailTrace_623000
  have hstable : (prefixWord ++ tailWord_623000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623000).length < 2 ^ (prefixWord ++ tailWord_623000).sum := by decide
  have hdescent : baseEnd_623000 < baseStart_623000 := by decide
  rcases family_descends (prefixWord ++ tailWord_623000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623047 : List Nat := [1, 1, 4, 1, 1, 4, 2, 3, 1, 1, 4]
def baseStart_623047 : Nat := 118140960795 + 623047 * 2 ^ 59
def prefixEnd_623047 : Nat := 4983230072969 + 3 ^ 40 * 623047 * 2
def baseEnd_623047 : Nat := 319922581341929059447165

theorem tailTrace_623047 : CollatzResearch.WordTrace tailWord_623047 prefixEnd_623047 319922581341929059447165 := by
  unfold tailWord_623047
  simp only [CollatzResearch.WordTrace]
  refine ⟨22724390973814601801139395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15149593982543067867426263 22724390973814601801139395)
  ·
    refine ⟨34086586460721902701709093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22724390973814601801139395 34086586460721902701709093)
    ·
      refine ⟨6391234961385356756570455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34086586460721902701709093 6391234961385356756570455)
      ·
        refine ⟨9586852442078035134855683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6391234961385356756570455 9586852442078035134855683)
        ·
          refine ⟨14380278663117052702283525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9586852442078035134855683 14380278663117052702283525)
          ·
            refine ⟨2696302249334447381678161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14380278663117052702283525 2696302249334447381678161)
            ·
              refine ⟨2022226687000835536258621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2696302249334447381678161 2022226687000835536258621)
              ·
                refine ⟨758335007625313326096983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2022226687000835536258621 758335007625313326096983)
                ·
                  refine ⟨1137502511437969989145475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 758335007625313326096983 1137502511437969989145475)
                  ·
                    refine ⟨1706253767156954983718213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1137502511437969989145475 1706253767156954983718213)
                    ·
                      refine ⟨319922581341929059447165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1706253767156954983718213 319922581341929059447165)
                      ·
                        rfl

theorem cell23_623047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_623047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623047 prefixEnd_623047 := by exact prefixLift 623047
  have htrace : WordTrace (prefixWord ++ tailWord_623047) baseStart_623047 baseEnd_623047 := by
    simpa [prefixWord, tailWord_623047, baseEnd_623047] using wordTrace_append hprefix tailTrace_623047
  have hstable : (prefixWord ++ tailWord_623047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623047).length < 2 ^ (prefixWord ++ tailWord_623047).sum := by decide
  have hdescent : baseEnd_623047 < baseStart_623047 := by decide
  rcases family_descends (prefixWord ++ tailWord_623047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623058 : List Nat := [3, 2, 2, 4, 1, 2, 1, 1, 3, 1, 3]
def baseStart_623058 : Nat := 118140960795 + 623058 * 2 ^ 59
def prefixEnd_623058 : Nat := 4983230072969 + 3 ^ 40 * 623058 * 2
def baseEnd_623058 : Nat := 319928229629128516409615

theorem tailTrace_623058 : CollatzResearch.WordTrace tailWord_623058 prefixEnd_623058 319928229629128516409615 := by
  unfold tailWord_623058
  simp only [CollatzResearch.WordTrace]
  refine ⟨5681198044193687669947457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15149861451183167119859885 5681198044193687669947457)
  ·
    refine ⟨4260898533145265752460593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5681198044193687669947457 4260898533145265752460593)
    ·
      refine ⟨3195673899858949314345445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4260898533145265752460593 3195673899858949314345445)
      ·
        refine ⟨599188856223552996439771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3195673899858949314345445 599188856223552996439771)
        ·
          refine ⟨898783284335329494659657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599188856223552996439771 898783284335329494659657)
          ·
            refine ⟨674087463251497120994743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 898783284335329494659657 674087463251497120994743)
            ·
              refine ⟨1011131194877245681492115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674087463251497120994743 1011131194877245681492115)
              ·
                refine ⟨1516696792315868522238173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1011131194877245681492115 1516696792315868522238173)
                ·
                  refine ⟨568761297118450695839315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1516696792315868522238173 568761297118450695839315)
                  ·
                    refine ⟨853141945677676043758973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 568761297118450695839315 853141945677676043758973)
                    ·
                      refine ⟨319928229629128516409615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 853141945677676043758973 319928229629128516409615)
                      ·
                        rfl

theorem cell23_623058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_623058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623058 prefixEnd_623058 := by exact prefixLift 623058
  have htrace : WordTrace (prefixWord ++ tailWord_623058) baseStart_623058 baseEnd_623058 := by
    simpa [prefixWord, tailWord_623058, baseEnd_623058] using wordTrace_append hprefix tailTrace_623058
  have hstable : (prefixWord ++ tailWord_623058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623058).length < 2 ^ (prefixWord ++ tailWord_623058).sum := by decide
  have hdescent : baseEnd_623058 < baseStart_623058 := by decide
  rcases family_descends (prefixWord ++ tailWord_623058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623097 : List Nat := [1, 2, 1, 3, 1, 2, 2, 1, 6, 1, 3]
def baseStart_623097 : Nat := 118140960795 + 623097 * 2 ^ 59
def prefixEnd_623097 : Nat := 4983230072969 + 3 ^ 40 * 623097 * 2
def baseEnd_623097 : Nat := 319948255374653863821935

theorem tailTrace_623097 : CollatzResearch.WordTrace tailWord_623097 prefixEnd_623097 319948255374653863821935 := by
  unfold tailWord_623097
  simp only [CollatzResearch.WordTrace]
  refine ⟨22726214623633460340459545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15150809749088973560306363 22726214623633460340459545)
  ·
    refine ⟨17044660967725095255344659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22726214623633460340459545 17044660967725095255344659)
    ·
      refine ⟨25566991451587642883016989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17044660967725095255344659 25566991451587642883016989)
      ·
        refine ⟨9587621794345366081131371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25566991451587642883016989 9587621794345366081131371)
        ·
          refine ⟨14381432691518049121697057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9587621794345366081131371 14381432691518049121697057)
          ·
            refine ⟨10786074518638536841272793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14381432691518049121697057 10786074518638536841272793)
            ·
              refine ⟨8089555888978902630954595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10786074518638536841272793 8089555888978902630954595)
              ·
                refine ⟨12134333833468353946431893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8089555888978902630954595 12134333833468353946431893)
                ·
                  refine ⟨568796898443829091238995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 12134333833468353946431893 568796898443829091238995)
                  ·
                    refine ⟨853195347665743636858493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 568796898443829091238995 853195347665743636858493)
                    ·
                      refine ⟨319948255374653863821935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 853195347665743636858493 319948255374653863821935)
                      ·
                        rfl

theorem cell23_623097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_623097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623097 prefixEnd_623097 := by exact prefixLift 623097
  have htrace : WordTrace (prefixWord ++ tailWord_623097) baseStart_623097 baseEnd_623097 := by
    simpa [prefixWord, tailWord_623097, baseEnd_623097] using wordTrace_append hprefix tailTrace_623097
  have hstable : (prefixWord ++ tailWord_623097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623097).length < 2 ^ (prefixWord ++ tailWord_623097).sum := by decide
  have hdescent : baseEnd_623097 < baseStart_623097 := by decide
  rcases family_descends (prefixWord ++ tailWord_623097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623115 : List Nat := [1, 1, 1, 1, 7, 3, 2, 2, 1, 2, 2]
def baseStart_623115 : Nat := 118140960795 + 623115 * 2 ^ 59
def prefixEnd_623115 : Nat := 4983230072969 + 3 ^ 40 * 623115 * 2
def baseEnd_623115 : Nat := 319957498026434793396853

theorem tailTrace_623115 : CollatzResearch.WordTrace tailWord_623115 prefixEnd_623115 319957498026434793396853 := by
  unfold tailWord_623115
  simp only [CollatzResearch.WordTrace]
  refine ⟨22726871137568249414614799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15151247425045499609743199 22726871137568249414614799)
  ·
    refine ⟨34090306706352374121922199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22726871137568249414614799 34090306706352374121922199)
    ·
      refine ⟨51135460059528561182883299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34090306706352374121922199 51135460059528561182883299)
      ·
        refine ⟨76703190089292841774324949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51135460059528561182883299 76703190089292841774324949)
        ·
          refine ⟨1797731017717800979085741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 76703190089292841774324949 1797731017717800979085741)
          ·
            refine ⟨674149131644175367157153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1797731017717800979085741 674149131644175367157153)
            ·
              refine ⟨505611848733131525367865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674149131644175367157153 505611848733131525367865)
              ·
                refine ⟨379208886549848644025899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 505611848733131525367865 379208886549848644025899)
                ·
                  refine ⟨568813329824772966038849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379208886549848644025899 568813329824772966038849)
                  ·
                    refine ⟨426609997368579724529137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 568813329824772966038849 426609997368579724529137)
                    ·
                      refine ⟨319957498026434793396853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 426609997368579724529137 319957498026434793396853)
                      ·
                        rfl

theorem cell23_623115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 2, 1, 2, 2].length) (baseStart_623115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623115 prefixEnd_623115 := by exact prefixLift 623115
  have htrace : WordTrace (prefixWord ++ tailWord_623115) baseStart_623115 baseEnd_623115 := by
    simpa [prefixWord, tailWord_623115, baseEnd_623115] using wordTrace_append hprefix tailTrace_623115
  have hstable : (prefixWord ++ tailWord_623115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623115).length < 2 ^ (prefixWord ++ tailWord_623115).sum := by decide
  have hdescent : baseEnd_623115 < baseStart_623115 := by decide
  rcases family_descends (prefixWord ++ tailWord_623115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623130 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 1, 8]
def baseStart_623130 : Nat := 118140960795 + 623130 * 2 ^ 59
def prefixEnd_623130 : Nat := 4983230072969 + 3 ^ 40 * 623130 * 2
def baseEnd_623130 : Nat := 106655066745417411569761

theorem tailTrace_623130 : CollatzResearch.WordTrace tailWord_623130 prefixEnd_623130 106655066745417411569761 := by
  unfold tailWord_623130
  simp only [CollatzResearch.WordTrace]
  refine ⟨5681854558128476744102711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15151612155009271317607229 5681854558128476744102711)
  ·
    refine ⟨8522781837192715116154067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5681854558128476744102711 8522781837192715116154067)
    ·
      refine ⟨12784172755789072674231101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8522781837192715116154067 12784172755789072674231101)
      ·
        refine ⟨4794064783420902252836663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12784172755789072674231101 4794064783420902252836663)
        ·
          refine ⟨7191097175131353379254995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4794064783420902252836663 7191097175131353379254995)
          ·
            refine ⟨10786645762697030068882493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7191097175131353379254995 10786645762697030068882493)
            ·
              refine ⟨4044992161011386275830935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10786645762697030068882493 4044992161011386275830935)
              ·
                refine ⟨6067488241517079413746403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4044992161011386275830935 6067488241517079413746403)
                ·
                  refine ⟨9101232362275619120619605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6067488241517079413746403 9101232362275619120619605)
                  ·
                    refine ⟨106655066745417411569761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9101232362275619120619605 106655066745417411569761)
                    ·
                      rfl

theorem cell23_623130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 8].length) (baseStart_623130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623130 prefixEnd_623130 := by exact prefixLift 623130
  have htrace : WordTrace (prefixWord ++ tailWord_623130) baseStart_623130 baseEnd_623130 := by
    simpa [prefixWord, tailWord_623130, baseEnd_623130] using wordTrace_append hprefix tailTrace_623130
  have hstable : (prefixWord ++ tailWord_623130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623130).length < 2 ^ (prefixWord ++ tailWord_623130).sum := by decide
  have hdescent : baseEnd_623130 < baseStart_623130 := by decide
  rcases family_descends (prefixWord ++ tailWord_623130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623149 : List Nat := [1, 5, 4, 1, 1, 1, 2, 3, 1, 2, 2]
def baseStart_623149 : Nat := 118140960795 + 623149 * 2 ^ 59
def prefixEnd_623149 : Nat := 4983230072969 + 3 ^ 40 * 623149 * 2
def baseEnd_623149 : Nat := 319974956368687660371697

theorem tailTrace_623149 : CollatzResearch.WordTrace tailWord_623149 prefixEnd_623149 319974956368687660371697 := by
  unfold tailWord_623149
  simp only [CollatzResearch.WordTrace]
  refine ⟨22728111219445073221352501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15152074146296715480901667 22728111219445073221352501)
  ·
    refine ⟨2130760426822975614501797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22728111219445073221352501 2130760426822975614501797)
    ·
      refine ⟨399517580029307927719087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2130760426822975614501797 399517580029307927719087)
      ·
        refine ⟨599276370043961891578631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 399517580029307927719087 599276370043961891578631)
        ·
          refine ⟨898914555065942837367947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599276370043961891578631 898914555065942837367947)
          ·
            refine ⟨1348371832598914256051921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 898914555065942837367947 1348371832598914256051921)
            ·
              refine ⟨1011278874449185692038941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1348371832598914256051921 1011278874449185692038941)
              ·
                refine ⟨379229577918444634514603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1011278874449185692038941 379229577918444634514603)
                ·
                  refine ⟨568844366877666951771905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379229577918444634514603 568844366877666951771905)
                  ·
                    refine ⟨426633275158250213828929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 568844366877666951771905 426633275158250213828929)
                    ·
                      refine ⟨319974956368687660371697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 426633275158250213828929 319974956368687660371697)
                      ·
                        rfl

theorem cell23_623149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_623149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623149 prefixEnd_623149 := by exact prefixLift 623149
  have htrace : WordTrace (prefixWord ++ tailWord_623149) baseStart_623149 baseEnd_623149 := by
    simpa [prefixWord, tailWord_623149, baseEnd_623149] using wordTrace_append hprefix tailTrace_623149
  have hstable : (prefixWord ++ tailWord_623149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623149).length < 2 ^ (prefixWord ++ tailWord_623149).sum := by decide
  have hdescent : baseEnd_623149 < baseStart_623149 := by decide
  rcases family_descends (prefixWord ++ tailWord_623149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623154 : List Nat := [3, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2]
def baseStart_623154 : Nat := 118140960795 + 623154 * 2 ^ 59
def prefixEnd_623154 : Nat := 4983230072969 + 3 ^ 40 * 623154 * 2
def baseEnd_623154 : Nat := 319977523771960140809173

theorem tailTrace_623154 : CollatzResearch.WordTrace tailWord_623154 prefixEnd_623154 319977523771960140809173 := by
  unfold tailWord_623154
  simp only [CollatzResearch.WordTrace]
  refine ⟨5682073396106739768821129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15152195722951306050189677 5682073396106739768821129)
  ·
    refine ⟨4261555047080054826615847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5682073396106739768821129 4261555047080054826615847)
    ·
      refine ⟨6392332570620082239923771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4261555047080054826615847 6392332570620082239923771)
      ·
        refine ⟨9588498855930123359885657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6392332570620082239923771 9588498855930123359885657)
        ·
          refine ⟨7191374141947592519914243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9588498855930123359885657 7191374141947592519914243)
          ·
            refine ⟨10787061212921388779871365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7191374141947592519914243 10787061212921388779871365)
            ·
              refine ⟨2022573977422760396225881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10787061212921388779871365 2022573977422760396225881)
              ·
                refine ⟨1516930483067070297169411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2022573977422760396225881 1516930483067070297169411)
                ·
                  refine ⟨2275395724600605445754117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1516930483067070297169411 2275395724600605445754117)
                  ·
                    refine ⟨426636698362613521078897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2275395724600605445754117 426636698362613521078897)
                    ·
                      refine ⟨319977523771960140809173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 426636698362613521078897 319977523771960140809173)
                      ·
                        rfl

theorem cell23_623154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 2, 1, 4, 2].length) (baseStart_623154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623154 prefixEnd_623154 := by exact prefixLift 623154
  have htrace : WordTrace (prefixWord ++ tailWord_623154) baseStart_623154 baseEnd_623154 := by
    simpa [prefixWord, tailWord_623154, baseEnd_623154] using wordTrace_append hprefix tailTrace_623154
  have hstable : (prefixWord ++ tailWord_623154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623154).length < 2 ^ (prefixWord ++ tailWord_623154).sum := by decide
  have hdescent : baseEnd_623154 < baseStart_623154 := by decide
  rcases family_descends (prefixWord ++ tailWord_623154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623158 : List Nat := [5, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2]
def baseStart_623158 : Nat := 118140960795 + 623158 * 2 ^ 59
def prefixEnd_623158 : Nat := 4983230072969 + 3 ^ 40 * 623158 * 2
def baseEnd_623158 : Nat := 319979577694578125159155

theorem tailTrace_623158 : CollatzResearch.WordTrace tailWord_623158 prefixEnd_623158 319979577694578125159155 := by
  unfold tailWord_623158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1420527467275779234901883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15152292984274978505620085 1420527467275779234901883)
  ·
    refine ⟨2130791200913668852352825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1420527467275779234901883 2130791200913668852352825)
    ·
      refine ⟨1598093400685251639264619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2130791200913668852352825 1598093400685251639264619)
      ·
        refine ⟨2397140101027877458896929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1598093400685251639264619 2397140101027877458896929)
        ·
          refine ⟨1797855075770908094172697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2397140101027877458896929 1797855075770908094172697)
          ·
            refine ⟨1348391306828181070629523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1797855075770908094172697 1348391306828181070629523)
            ·
              refine ⟨2022586960242271605944285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1348391306828181070629523 2022586960242271605944285)
              ·
                refine ⟨758470110090851852229107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2022586960242271605944285 758470110090851852229107)
                ·
                  refine ⟨1137705165136277778343661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 758470110090851852229107 1137705165136277778343661)
                  ·
                    refine ⟨426639436926104166878873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1137705165136277778343661 426639436926104166878873)
                    ·
                      refine ⟨319979577694578125159155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 426639436926104166878873 319979577694578125159155)
                      ·
                        rfl

theorem cell23_623158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_623158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623158 prefixEnd_623158 := by exact prefixLift 623158
  have htrace : WordTrace (prefixWord ++ tailWord_623158) baseStart_623158 baseEnd_623158 := by
    simpa [prefixWord, tailWord_623158, baseEnd_623158] using wordTrace_append hprefix tailTrace_623158
  have hstable : (prefixWord ++ tailWord_623158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623158).length < 2 ^ (prefixWord ++ tailWord_623158).sum := by decide
  have hdescent : baseEnd_623158 < baseStart_623158 := by decide
  rcases family_descends (prefixWord ++ tailWord_623158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623160 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 9]
def baseStart_623160 : Nat := 118140960795 + 623160 * 2 ^ 59
def prefixEnd_623160 : Nat := 4983230072969 + 3 ^ 40 * 623160 * 2
def baseEnd_623160 : Nat := 35553400517320790814905

theorem tailTrace_623160 : CollatzResearch.WordTrace tailWord_623160 prefixEnd_623160 35553400517320790814905 := by
  unfold tailWord_623160
  simp only [CollatzResearch.WordTrace]
  refine ⟨11364256211202611050001467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15152341614936814733335289 11364256211202611050001467)
  ·
    refine ⟨17046384316803916575002201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11364256211202611050001467 17046384316803916575002201)
    ·
      refine ⟨12784788237602937431251651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17046384316803916575002201 12784788237602937431251651)
      ·
        refine ⟨19177182356404406146877477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12784788237602937431251651 19177182356404406146877477)
        ·
          refine ⟨3595721691825826152539527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19177182356404406146877477 3595721691825826152539527)
          ·
            refine ⟨5393582537738739228809291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3595721691825826152539527 5393582537738739228809291)
            ·
              refine ⟨8090373806608108843213937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5393582537738739228809291 8090373806608108843213937)
              ·
                refine ⟨6067780354956081632410453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8090373806608108843213937 6067780354956081632410453)
                ·
                  refine ⟨35553400517320790814905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6067780354956081632410453 35553400517320790814905)
                  ·
                    rfl

theorem cell23_623160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 9].length) (baseStart_623160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623160 prefixEnd_623160 := by exact prefixLift 623160
  have htrace : WordTrace (prefixWord ++ tailWord_623160) baseStart_623160 baseEnd_623160 := by
    simpa [prefixWord, tailWord_623160, baseEnd_623160] using wordTrace_append hprefix tailTrace_623160
  have hstable : (prefixWord ++ tailWord_623160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623160).length < 2 ^ (prefixWord ++ tailWord_623160).sum := by decide
  have hdescent : baseEnd_623160 < baseStart_623160 := by decide
  rcases family_descends (prefixWord ++ tailWord_623160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623207 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 2, 5]
def baseStart_623207 : Nat := 118140960795 + 623207 * 2 ^ 59
def prefixEnd_623207 : Nat := 4983230072969 + 3 ^ 40 * 623207 * 2
def baseEnd_623207 : Nat := 106668246082216144482143

theorem tailTrace_623207 : CollatzResearch.WordTrace tailWord_623207 prefixEnd_623207 106668246082216144482143 := by
  unfold tailWord_623207
  simp only [CollatzResearch.WordTrace]
  refine ⟨22730226653234949126963875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15153484435489966084642583 22730226653234949126963875)
  ·
    refine ⟨34095339979852423690445813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22730226653234949126963875 34095339979852423690445813)
    ·
      refine ⟨3196438123111164720979295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34095339979852423690445813 3196438123111164720979295)
      ·
        refine ⟨4794657184666747081468943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3196438123111164720979295 4794657184666747081468943)
        ·
          refine ⟨7191985777000120622203415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4794657184666747081468943 7191985777000120622203415)
          ·
            refine ⟨10787978665500180933305123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7191985777000120622203415 10787978665500180933305123)
            ·
              refine ⟨16181967998250271399957685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10787978665500180933305123 16181967998250271399957685)
              ·
                refine ⟨1517059499835962943746033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16181967998250271399957685 1517059499835962943746033)
                ·
                  refine ⟨1137794624876972207809525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1517059499835962943746033 1137794624876972207809525)
                  ·
                    refine ⟨106668246082216144482143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1137794624876972207809525 106668246082216144482143)
                    ·
                      rfl

theorem cell23_623207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_623207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623207 prefixEnd_623207 := by exact prefixLift 623207
  have htrace : WordTrace (prefixWord ++ tailWord_623207) baseStart_623207 baseEnd_623207 := by
    simpa [prefixWord, tailWord_623207, baseEnd_623207] using wordTrace_append hprefix tailTrace_623207
  have hstable : (prefixWord ++ tailWord_623207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623207).length < 2 ^ (prefixWord ++ tailWord_623207).sum := by decide
  have hdescent : baseEnd_623207 < baseStart_623207 := by decide
  rcases family_descends (prefixWord ++ tailWord_623207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623331 : List Nat := [1, 1, 1, 7, 1, 2, 1, 3, 1, 5]
def baseStart_623331 : Nat := 118140960795 + 623331 * 2 ^ 59
def prefixEnd_623331 : Nat := 4983230072969 + 3 ^ 40 * 623331 * 2
def baseEnd_623331 : Nat := 106689469949268649431953

theorem tailTrace_623331 : CollatzResearch.WordTrace tailWord_623331 prefixEnd_623331 106689469949268649431953 := by
  unfold tailWord_623331
  simp only [CollatzResearch.WordTrace]
  refine ⟨22734749304785718304477847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15156499536523812202985231 22734749304785718304477847)
  ·
    refine ⟨34102123957178577456716771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22734749304785718304477847 34102123957178577456716771)
    ·
      refine ⟨51153185935767866185075157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34102123957178577456716771 51153185935767866185075157)
      ·
        refine ⟨1198902795369559363712699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 51153185935767866185075157 1198902795369559363712699)
        ·
          refine ⟨1798354193054339045569049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1198902795369559363712699 1798354193054339045569049)
          ·
            refine ⟨1348765644790754284176787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1798354193054339045569049 1348765644790754284176787)
            ·
              refine ⟨2023148467186131426265181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1348765644790754284176787 2023148467186131426265181)
              ·
                refine ⟨758680675194799284849443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2023148467186131426265181 758680675194799284849443)
                ·
                  refine ⟨1138021012792198927274165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 758680675194799284849443 1138021012792198927274165)
                  ·
                    refine ⟨106689469949268649431953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1138021012792198927274165 106689469949268649431953)
                    ·
                      rfl

theorem cell23_623331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 5].length) (baseStart_623331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623331 prefixEnd_623331 := by exact prefixLift 623331
  have htrace : WordTrace (prefixWord ++ tailWord_623331) baseStart_623331 baseEnd_623331 := by
    simpa [prefixWord, tailWord_623331, baseEnd_623331] using wordTrace_append hprefix tailTrace_623331
  have hstable : (prefixWord ++ tailWord_623331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623331).length < 2 ^ (prefixWord ++ tailWord_623331).sum := by decide
  have hdescent : baseEnd_623331 < baseStart_623331 := by decide
  rcases family_descends (prefixWord ++ tailWord_623331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623344 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 4, 4]
def baseStart_623344 : Nat := 118140960795 + 623344 * 2 ^ 59
def prefixEnd_623344 : Nat := 4983230072969 + 3 ^ 40 * 623344 * 2
def baseEnd_623344 : Nat := 106691695032104799144433

theorem tailTrace_623344 : CollatzResearch.WordTrace tailWord_623344 prefixEnd_623344 106691695032104799144433 := by
  unfold tailWord_623344
  simp only [CollatzResearch.WordTrace]
  refine ⟨11367611726869310762350543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15156815635825747683134057 11367611726869310762350543)
  ·
    refine ⟨17051417590303966143525815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11367611726869310762350543 17051417590303966143525815)
    ·
      refine ⟨25577126385455949215288723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17051417590303966143525815 25577126385455949215288723)
      ·
        refine ⟨38365689578183923822933085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25577126385455949215288723 38365689578183923822933085)
        ·
          refine ⟨14387133591818971433599907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38365689578183923822933085 14387133591818971433599907)
          ·
            refine ⟨21580700387728457150399861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14387133591818971433599907 21580700387728457150399861)
            ·
              refine ⟨2023190661349542857849987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21580700387728457150399861 2023190661349542857849987)
              ·
                refine ⟨3034785992024314286774981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2023190661349542857849987 3034785992024314286774981)
                ·
                  refine ⟨569022373504558928770309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3034785992024314286774981 569022373504558928770309)
                  ·
                    refine ⟨106691695032104799144433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 569022373504558928770309 106691695032104799144433)
                    ·
                      rfl

theorem cell23_623344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 4, 4].length) (baseStart_623344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623344 prefixEnd_623344 := by exact prefixLift 623344
  have htrace : WordTrace (prefixWord ++ tailWord_623344) baseStart_623344 baseEnd_623344 := by
    simpa [prefixWord, tailWord_623344, baseEnd_623344] using wordTrace_append hprefix tailTrace_623344
  have hstable : (prefixWord ++ tailWord_623344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623344).length < 2 ^ (prefixWord ++ tailWord_623344).sum := by decide
  have hdescent : baseEnd_623344 < baseStart_623344 := by decide
  rcases family_descends (prefixWord ++ tailWord_623344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623347 : List Nat := [1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 6]
def baseStart_623347 : Nat := 118140960795 + 623347 * 2 ^ 59
def prefixEnd_623347 : Nat := 4983230072969 + 3 ^ 40 * 623347 * 2
def baseEnd_623347 : Nat := 320076625538277885695785

theorem tailTrace_623347 : CollatzResearch.WordTrace tailWord_623347 prefixEnd_623347 320076625538277885695785 := by
  unfold tailWord_623347
  simp only [CollatzResearch.WordTrace]
  refine ⟨22735332872727753037060295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15156888581818502024706863 22735332872727753037060295)
  ·
    refine ⟨34102999309091629555590443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22735332872727753037060295 34102999309091629555590443)
    ·
      refine ⟨51154498963637444333385665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34102999309091629555590443 51154498963637444333385665)
      ·
        refine ⟨38365874222728083250039249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51154498963637444333385665 38365874222728083250039249)
        ·
          refine ⟨28774405667046062437529437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38365874222728083250039249 28774405667046062437529437)
          ·
            refine ⟨10790402125142273414073539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28774405667046062437529437 10790402125142273414073539)
            ·
              refine ⟨16185603187713410121110309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10790402125142273414073539 16185603187713410121110309)
              ·
                refine ⟨3034800597696264397708183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16185603187713410121110309 3034800597696264397708183)
                ·
                  refine ⟨4552200896544396596562275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3034800597696264397708183 4552200896544396596562275)
                  ·
                    refine ⟨6828301344816594894843413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4552200896544396596562275 6828301344816594894843413)
                    ·
                      refine ⟨320076625538277885695785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6828301344816594894843413 320076625538277885695785)
                      ·
                        rfl

theorem cell23_623347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 6].length) (baseStart_623347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623347 prefixEnd_623347 := by exact prefixLift 623347
  have htrace : WordTrace (prefixWord ++ tailWord_623347) baseStart_623347 baseEnd_623347 := by
    simpa [prefixWord, tailWord_623347, baseEnd_623347] using wordTrace_append hprefix tailTrace_623347
  have hstable : (prefixWord ++ tailWord_623347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623347).length < 2 ^ (prefixWord ++ tailWord_623347).sum := by decide
  have hdescent : baseEnd_623347 < baseStart_623347 := by decide
  rcases family_descends (prefixWord ++ tailWord_623347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623354 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3]
def baseStart_623354 : Nat := 118140960795 + 623354 * 2 ^ 59
def prefixEnd_623354 : Nat := 4983230072969 + 3 ^ 40 * 623354 * 2
def baseEnd_623354 : Nat := 320080219902859358308253

theorem tailTrace_623354 : CollatzResearch.WordTrace tailWord_623354 prefixEnd_623354 320080219902859358308253 := by
  unfold tailWord_623354
  simp only [CollatzResearch.WordTrace]
  refine ⟨5683897045925598308141279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15157058789134928821710077 5683897045925598308141279)
  ·
    refine ⟨8525845568888397462211919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5683897045925598308141279 8525845568888397462211919)
    ·
      refine ⟨12788768353332596193317879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8525845568888397462211919 12788768353332596193317879)
      ·
        refine ⟨19183152529998894289976819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12788768353332596193317879 19183152529998894289976819)
        ·
          refine ⟨28774728794998341434965229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19183152529998894289976819 28774728794998341434965229)
          ·
            refine ⟨10790523298124378038111961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28774728794998341434965229 10790523298124378038111961)
            ·
              refine ⟨8092892473593283528583971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10790523298124378038111961 8092892473593283528583971)
              ·
                refine ⟨12139338710389925292875957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8092892473593283528583971 12139338710389925292875957)
                ·
                  refine ⟨1138063004099055496207121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12139338710389925292875957 1138063004099055496207121)
                  ·
                    refine ⟨853547253074291622155341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1138063004099055496207121 853547253074291622155341)
                    ·
                      refine ⟨320080219902859358308253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 853547253074291622155341 320080219902859358308253)
                      ·
                        rfl

theorem cell23_623354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_623354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623354 prefixEnd_623354 := by exact prefixLift 623354
  have htrace : WordTrace (prefixWord ++ tailWord_623354) baseStart_623354 baseEnd_623354 := by
    simpa [prefixWord, tailWord_623354, baseEnd_623354] using wordTrace_append hprefix tailTrace_623354
  have hstable : (prefixWord ++ tailWord_623354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623354).length < 2 ^ (prefixWord ++ tailWord_623354).sum := by decide
  have hdescent : baseEnd_623354 < baseStart_623354 := by decide
  rcases family_descends (prefixWord ++ tailWord_623354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623357 : List Nat := [1, 4, 1, 1, 1, 1, 4, 10]
def baseStart_623357 : Nat := 118140960795 + 623357 * 2 ^ 59
def prefixEnd_623357 : Nat := 4983230072969 + 3 ^ 40 * 623357 * 2
def baseEnd_623357 : Nat := 11854880012771216539657

theorem tailTrace_623357 : CollatzResearch.WordTrace tailWord_623357 prefixEnd_623357 11854880012771216539657 := by
  unfold tailWord_623357
  simp only [CollatzResearch.WordTrace]
  refine ⟨22735697602691524744924325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15157131735127683163282883 22735697602691524744924325)
  ·
    refine ⟨4262943300504660889673311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22735697602691524744924325 4262943300504660889673311)
    ·
      refine ⟨6394414950756991334509967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4262943300504660889673311 6394414950756991334509967)
      ·
        refine ⟨9591622426135487001764951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6394414950756991334509967 9591622426135487001764951)
        ·
          refine ⟨14387433639203230502647427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9591622426135487001764951 14387433639203230502647427)
          ·
            refine ⟨21581150458804845753971141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14387433639203230502647427 21581150458804845753971141)
            ·
              refine ⟨4046465711025908578869589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21581150458804845753971141 4046465711025908578869589)
              ·
                refine ⟨11854880012771216539657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4046465711025908578869589 11854880012771216539657)
                ·
                  rfl

theorem cell23_623357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 10].length) (baseStart_623357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623357 prefixEnd_623357 := by exact prefixLift 623357
  have htrace : WordTrace (prefixWord ++ tailWord_623357) baseStart_623357 baseEnd_623357 := by
    simpa [prefixWord, tailWord_623357, baseEnd_623357] using wordTrace_append hprefix tailTrace_623357
  have hstable : (prefixWord ++ tailWord_623357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623357).length < 2 ^ (prefixWord ++ tailWord_623357).sum := by decide
  have hdescent : baseEnd_623357 < baseStart_623357 := by decide
  rcases family_descends (prefixWord ++ tailWord_623357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623364 : List Nat := [2, 3, 2, 2, 1, 1, 3, 1, 1, 1, 6]
def baseStart_623364 : Nat := 118140960795 + 623364 * 2 ^ 59
def prefixEnd_623364 : Nat := 4983230072969 + 3 ^ 40 * 623364 * 2
def baseEnd_623364 : Nat := 320085354709404319183207

theorem tailTrace_623364 : CollatzResearch.WordTrace tailWord_623364 prefixEnd_623364 320085354709404319183207 := by
  unfold tailWord_623364
  simp only [CollatzResearch.WordTrace]
  refine ⟨11367976456833082470214573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15157301942444109960286097 11367976456833082470214573)
  ·
    refine ⟨4262991171312405926330465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11367976456833082470214573 4262991171312405926330465)
    ·
      refine ⟨3197243378484304444747849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4262991171312405926330465 3197243378484304444747849)
      ·
        refine ⟨2397932533863228333560887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3197243378484304444747849 2397932533863228333560887)
        ·
          refine ⟨3596898800794842500341331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2397932533863228333560887 3596898800794842500341331)
          ·
            refine ⟨5395348201192263750511997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3596898800794842500341331 5395348201192263750511997)
            ·
              refine ⟨2023255575447098906441999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5395348201192263750511997 2023255575447098906441999)
              ·
                refine ⟨3034883363170648359662999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2023255575447098906441999 3034883363170648359662999)
                ·
                  refine ⟨4552325044755972539494499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3034883363170648359662999 4552325044755972539494499)
                  ·
                    refine ⟨6828487567133958809241749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4552325044755972539494499 6828487567133958809241749)
                    ·
                      refine ⟨320085354709404319183207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6828487567133958809241749 320085354709404319183207)
                      ·
                        rfl

theorem cell23_623364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_623364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623364 prefixEnd_623364 := by exact prefixLift 623364
  have htrace : WordTrace (prefixWord ++ tailWord_623364) baseStart_623364 baseEnd_623364 := by
    simpa [prefixWord, tailWord_623364, baseEnd_623364] using wordTrace_append hprefix tailTrace_623364
  have hstable : (prefixWord ++ tailWord_623364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623364).length < 2 ^ (prefixWord ++ tailWord_623364).sum := by decide
  have hdescent : baseEnd_623364 < baseStart_623364 := by decide
  rcases family_descends (prefixWord ++ tailWord_623364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623368 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 3, 2, 2]
def baseStart_623368 : Nat := 118140960795 + 623368 * 2 ^ 59
def prefixEnd_623368 : Nat := 4983230072969 + 3 ^ 40 * 623368 * 2
def baseEnd_623368 : Nat := 320087408632022303533189

theorem tailTrace_623368 : CollatzResearch.WordTrace tailWord_623368 prefixEnd_623368 320087408632022303533189 := by
  unfold tailWord_623368
  simp only [CollatzResearch.WordTrace]
  refine ⟨11368049402825836811787379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15157399203767782415716505 11368049402825836811787379)
  ·
    refine ⟨17052074104238755217681069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11368049402825836811787379 17052074104238755217681069)
    ·
      refine ⟨6394527789089533206630401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17052074104238755217681069 6394527789089533206630401)
      ·
        refine ⟨4795895841817149904972801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6394527789089533206630401 4795895841817149904972801)
        ·
          refine ⟨3596921881362862428729601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4795895841817149904972801 3596921881362862428729601)
          ·
            refine ⟨2697691411022146821547201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3596921881362862428729601 2697691411022146821547201)
            ·
              refine ⟨2023268558266610116160401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2697691411022146821547201 2023268558266610116160401)
              ·
                refine ⟨1517451418699957587120301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2023268558266610116160401 1517451418699957587120301)
                ·
                  refine ⟨569044282012484095170113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1517451418699957587120301 569044282012484095170113)
                  ·
                    refine ⟨426783211509363071377585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 569044282012484095170113 426783211509363071377585)
                    ·
                      refine ⟨320087408632022303533189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 426783211509363071377585 320087408632022303533189)
                      ·
                        rfl

theorem cell23_623368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 3, 2, 2].length) (baseStart_623368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623368 prefixEnd_623368 := by exact prefixLift 623368
  have htrace : WordTrace (prefixWord ++ tailWord_623368) baseStart_623368 baseEnd_623368 := by
    simpa [prefixWord, tailWord_623368, baseEnd_623368] using wordTrace_append hprefix tailTrace_623368
  have hstable : (prefixWord ++ tailWord_623368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623368).length < 2 ^ (prefixWord ++ tailWord_623368).sum := by decide
  have hdescent : baseEnd_623368 < baseStart_623368 := by decide
  rcases family_descends (prefixWord ++ tailWord_623368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623384 : List Nat := [2, 1, 2, 3, 1, 1, 1, 3, 3, 3, 3]
def baseStart_623384 : Nat := 118140960795 + 623384 * 2 ^ 59
def prefixEnd_623384 : Nat := 4983230072969 + 3 ^ 40 * 623384 * 2
def baseEnd_623384 : Nat := 320095624322494240933115

theorem tailTrace_623384 : CollatzResearch.WordTrace tailWord_623384 prefixEnd_623384 320095624322494240933115 := by
  unfold tailWord_623384
  simp only [CollatzResearch.WordTrace]
  refine ⟨11368341186796854178078603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15157788249062472237438137 11368341186796854178078603)
  ·
    refine ⟨17052511780195281267117905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11368341186796854178078603 17052511780195281267117905)
    ·
      refine ⟨12789383835146460950338429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17052511780195281267117905 12789383835146460950338429)
      ·
        refine ⟨4796018938179922856376911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12789383835146460950338429 4796018938179922856376911)
        ·
          refine ⟨7194028407269884284565367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4796018938179922856376911 7194028407269884284565367)
          ·
            refine ⟨10791042610904826426848051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7194028407269884284565367 10791042610904826426848051)
            ·
              refine ⟨16186563916357239640272077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10791042610904826426848051 16186563916357239640272077)
              ·
                refine ⟨6069961468633964865102029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16186563916357239640272077 6069961468633964865102029)
                ·
                  refine ⟨2276235550737736824413261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6069961468633964865102029 2276235550737736824413261)
                  ·
                    refine ⟨853588331526651309154973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2276235550737736824413261 853588331526651309154973)
                    ·
                      refine ⟨320095624322494240933115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 853588331526651309154973 320095624322494240933115)
                      ·
                        rfl

theorem cell23_623384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_623384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623384 prefixEnd_623384 := by exact prefixLift 623384
  have htrace : WordTrace (prefixWord ++ tailWord_623384) baseStart_623384 baseEnd_623384 := by
    simpa [prefixWord, tailWord_623384, baseEnd_623384] using wordTrace_append hprefix tailTrace_623384
  have hstable : (prefixWord ++ tailWord_623384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623384).length < 2 ^ (prefixWord ++ tailWord_623384).sum := by decide
  have hdescent : baseEnd_623384 < baseStart_623384 := by decide
  rcases family_descends (prefixWord ++ tailWord_623384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623412 : List Nat := [2, 5, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_623412 : Nat := 118140960795 + 623412 * 2 ^ 59
def prefixEnd_623412 : Nat := 4983230072969 + 3 ^ 40 * 623412 * 2
def baseEnd_623412 : Nat := 106703333926940043794329

theorem tailTrace_623412 : CollatzResearch.WordTrace tailWord_623412 prefixEnd_623412 106703333926940043794329 := by
  unfold tailWord_623412
  simp only [CollatzResearch.WordTrace]
  refine ⟨11368851808746134569088245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15158469078328179425450993 11368851808746134569088245)
  ·
    refine ⟨1065829857069950115852023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11368851808746134569088245 1065829857069950115852023)
    ·
      refine ⟨1598744785604925173778035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1065829857069950115852023 1598744785604925173778035)
      ·
        refine ⟨2398117178407387760667053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1598744785604925173778035 2398117178407387760667053)
        ·
          refine ⟨899293941902770410250145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2398117178407387760667053 899293941902770410250145)
          ·
            refine ⟨674470456427077807687609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 899293941902770410250145 674470456427077807687609)
            ·
              refine ⟨505852842320308355765707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674470456427077807687609 505852842320308355765707)
              ·
                refine ⟨758779263480462533648561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505852842320308355765707 758779263480462533648561)
                ·
                  refine ⟨569084447610346900236421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 758779263480462533648561 569084447610346900236421)
                  ·
                    refine ⟨106703333926940043794329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 569084447610346900236421 106703333926940043794329)
                    ·
                      rfl

theorem cell23_623412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_623412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623412 prefixEnd_623412 := by exact prefixLift 623412
  have htrace : WordTrace (prefixWord ++ tailWord_623412) baseStart_623412 baseEnd_623412 := by
    simpa [prefixWord, tailWord_623412, baseEnd_623412] using wordTrace_append hprefix tailTrace_623412
  have hstable : (prefixWord ++ tailWord_623412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623412).length < 2 ^ (prefixWord ++ tailWord_623412).sum := by decide
  have hdescent : baseEnd_623412 < baseStart_623412 := by decide
  rcases family_descends (prefixWord ++ tailWord_623412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623422 : List Nat := [4, 2, 1, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_623422 : Nat := 118140960795 + 623422 * 2 ^ 59
def prefixEnd_623422 : Nat := 4983230072969 + 3 ^ 40 * 623422 * 2
def baseEnd_623422 : Nat := 320115136587365092257941

theorem tailTrace_623422 : CollatzResearch.WordTrace tailWord_623422 prefixEnd_623422 320115136587365092257941 := by
  unfold tailWord_623422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2842258543432005105755065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15158712231637360564027013 2842258543432005105755065)
  ·
    refine ⟨2131693907574003829316299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2842258543432005105755065 2131693907574003829316299)
    ·
      refine ⟨3197540861361005743974449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2131693907574003829316299 3197540861361005743974449)
      ·
        refine ⟨2398155646020754307980837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3197540861361005743974449 2398155646020754307980837)
        ·
          refine ⟨449654183628891432746407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2398155646020754307980837 449654183628891432746407)
          ·
            refine ⟨674481275443337149119611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 449654183628891432746407 674481275443337149119611)
            ·
              refine ⟨1011721913165005723679417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674481275443337149119611 1011721913165005723679417)
              ·
                refine ⟨758791434873754292759563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1011721913165005723679417 758791434873754292759563)
                ·
                  refine ⟨1138187152310631439139345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 758791434873754292759563 1138187152310631439139345)
                  ·
                    refine ⟨853640364232973579354509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1138187152310631439139345 853640364232973579354509)
                    ·
                      refine ⟨320115136587365092257941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 853640364232973579354509 320115136587365092257941)
                      ·
                        rfl

theorem cell23_623422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_623422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623422 prefixEnd_623422 := by exact prefixLift 623422
  have htrace : WordTrace (prefixWord ++ tailWord_623422) baseStart_623422 baseEnd_623422 := by
    simpa [prefixWord, tailWord_623422, baseEnd_623422] using wordTrace_append hprefix tailTrace_623422
  have hstable : (prefixWord ++ tailWord_623422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623422).length < 2 ^ (prefixWord ++ tailWord_623422).sum := by decide
  have hdescent : baseEnd_623422 < baseStart_623422 := by decide
  rcases family_descends (prefixWord ++ tailWord_623422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623445 : List Nat := [1, 3, 2, 2, 2, 1, 5, 1, 1, 3, 2]
def baseStart_623445 : Nat := 118140960795 + 623445 * 2 ^ 59
def prefixEnd_623445 : Nat := 4983230072969 + 3 ^ 40 * 623445 * 2
def baseEnd_623445 : Nat := 320126946642418502270335

theorem tailTrace_623445 : CollatzResearch.WordTrace tailWord_623445 prefixEnd_623445 320126946642418502270335 := by
  unfold tailWord_623445
  simp only [CollatzResearch.WordTrace]
  refine ⟨22738907226372715774127789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15159271484248477182751859 22738907226372715774127789)
  ·
    refine ⟨8527090209889768415297921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22738907226372715774127789 8527090209889768415297921)
    ·
      refine ⟨6395317657417326311473441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8527090209889768415297921 6395317657417326311473441)
      ·
        refine ⟨4796488243062994733605081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6395317657417326311473441 4796488243062994733605081)
        ·
          refine ⟨3597366182297246050203811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4796488243062994733605081 3597366182297246050203811)
          ·
            refine ⟨5396049273445869075305717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3597366182297246050203811 5396049273445869075305717)
            ·
              refine ⟨505879619385550225809911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5396049273445869075305717 505879619385550225809911)
              ·
                refine ⟨758819429078325338714867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 505879619385550225809911 758819429078325338714867)
                ·
                  refine ⟨1138229143617488008072301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 758819429078325338714867 1138229143617488008072301)
                  ·
                    refine ⟨426835928856558003027113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1138229143617488008072301 426835928856558003027113)
                    ·
                      refine ⟨320126946642418502270335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 426835928856558003027113 320126946642418502270335)
                      ·
                        rfl

theorem cell23_623445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_623445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623445 prefixEnd_623445 := by exact prefixLift 623445
  have htrace : WordTrace (prefixWord ++ tailWord_623445) baseStart_623445 baseEnd_623445 := by
    simpa [prefixWord, tailWord_623445, baseEnd_623445] using wordTrace_append hprefix tailTrace_623445
  have hstable : (prefixWord ++ tailWord_623445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623445).length < 2 ^ (prefixWord ++ tailWord_623445).sum := by decide
  have hdescent : baseEnd_623445 < baseStart_623445 := by decide
  rcases family_descends (prefixWord ++ tailWord_623445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623498 : List Nat := [3, 1, 2, 4, 1, 1, 1, 5, 5]
def baseStart_623498 : Nat := 118140960795 + 623498 * 2 ^ 59
def prefixEnd_623498 : Nat := 4983230072969 + 3 ^ 40 * 623498 * 2
def baseEnd_623498 : Nat := 35572684568567421656399

theorem tailTrace_623498 : CollatzResearch.WordTrace tailWord_623498 prefixEnd_623498 35572684568567421656399 := by
  unfold tailWord_623498
  simp only [CollatzResearch.WordTrace]
  refine ⟨5685210073795176456451787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15160560196787137217204765 5685210073795176456451787)
  ·
    refine ⟨8527815110692764684677681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5685210073795176456451787 8527815110692764684677681)
    ·
      refine ⟨6395861333019573513508261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8527815110692764684677681 6395861333019573513508261)
      ·
        refine ⟨1199223999941170033782799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6395861333019573513508261 1199223999941170033782799)
        ·
          refine ⟨1798835999911755050674199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199223999941170033782799 1798835999911755050674199)
          ·
            refine ⟨2698253999867632576011299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1798835999911755050674199 2698253999867632576011299)
            ·
              refine ⟨4047380999801448864016949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2698253999867632576011299 4047380999801448864016949)
              ·
                refine ⟨379441968731385831001589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4047380999801448864016949 379441968731385831001589)
                ·
                  refine ⟨35572684568567421656399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 379441968731385831001589 35572684568567421656399)
                  ·
                    rfl

theorem cell23_623498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 5].length) (baseStart_623498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623498 prefixEnd_623498 := by exact prefixLift 623498
  have htrace : WordTrace (prefixWord ++ tailWord_623498) baseStart_623498 baseEnd_623498 := by
    simpa [prefixWord, tailWord_623498, baseEnd_623498] using wordTrace_append hprefix tailTrace_623498
  have hstable : (prefixWord ++ tailWord_623498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623498).length < 2 ^ (prefixWord ++ tailWord_623498).sum := by decide
  have hdescent : baseEnd_623498 < baseStart_623498 := by decide
  rcases family_descends (prefixWord ++ tailWord_623498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623584 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 1, 11]
def baseStart_623584 : Nat := 118140960795 + 623584 * 2 ^ 59
def prefixEnd_623584 : Nat := 4983230072969 + 3 ^ 40 * 623584 * 2
def baseEnd_623584 : Nat := 106732773484464486144065

theorem tailTrace_623584 : CollatzResearch.WordTrace tailWord_623584 prefixEnd_623584 106732773484464486144065 := by
  unfold tailWord_623584
  simp only [CollatzResearch.WordTrace]
  refine ⟨11371988486434571256718903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15162651315246095008958537 11371988486434571256718903)
  ·
    refine ⟨17057982729651856885078355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11371988486434571256718903 17057982729651856885078355)
    ·
      refine ⟨25586974094477785327617533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17057982729651856885078355 25586974094477785327617533)
      ·
        refine ⟨9595115285429169497856575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25586974094477785327617533 9595115285429169497856575)
        ·
          refine ⟨14392672928143754246784863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9595115285429169497856575 14392672928143754246784863)
          ·
            refine ⟨21589009392215631370177295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14392672928143754246784863 21589009392215631370177295)
            ·
              refine ⟨32383514088323447055265943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21589009392215631370177295 32383514088323447055265943)
              ·
                refine ⟨48575271132485170582898915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32383514088323447055265943 48575271132485170582898915)
                ·
                  refine ⟨72862906698727755874348373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48575271132485170582898915 72862906698727755874348373)
                  ·
                    refine ⟨106732773484464486144065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 72862906698727755874348373 106732773484464486144065)
                    ·
                      rfl

theorem cell23_623584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 11].length) (baseStart_623584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623584 prefixEnd_623584 := by exact prefixLift 623584
  have htrace : WordTrace (prefixWord ++ tailWord_623584) baseStart_623584 baseEnd_623584 := by
    simpa [prefixWord, tailWord_623584, baseEnd_623584] using wordTrace_append hprefix tailTrace_623584
  have hstable : (prefixWord ++ tailWord_623584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623584).length < 2 ^ (prefixWord ++ tailWord_623584).sum := by decide
  have hdescent : baseEnd_623584 < baseStart_623584 := by decide
  rcases family_descends (prefixWord ++ tailWord_623584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623602 : List Nat := [3, 2, 1, 5, 1, 1, 2, 1, 2, 2, 3]
def baseStart_623602 : Nat := 118140960795 + 623602 * 2 ^ 59
def prefixEnd_623602 : Nat := 4983230072969 + 3 ^ 40 * 623602 * 2
def baseEnd_623602 : Nat := 320207563105174388007113

theorem tailTrace_623602 : CollatzResearch.WordTrace tailWord_623602 prefixEnd_623602 320207563105174388007113 := by
  unfold tailWord_623602
  simp only [CollatzResearch.WordTrace]
  refine ⟨5686158371700982896898265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15163088991202621058395373 5686158371700982896898265)
  ·
    refine ⟨4264618778775737172673699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5686158371700982896898265 4264618778775737172673699)
    ·
      refine ⟨6396928168163605759010549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4264618778775737172673699 6396928168163605759010549)
      ·
        refine ⟨599712015765338039907239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6396928168163605759010549 599712015765338039907239)
        ·
          refine ⟨899568023648007059860859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 599712015765338039907239 899568023648007059860859)
          ·
            refine ⟨1349352035472010589791289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899568023648007059860859 1349352035472010589791289)
            ·
              refine ⟨1012014026604007942343467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1349352035472010589791289 1012014026604007942343467)
              ·
                refine ⟨1518021039906011913515201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012014026604007942343467 1518021039906011913515201)
                ·
                  refine ⟨1138515779929508935136401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1518021039906011913515201 1138515779929508935136401)
                  ·
                    refine ⟨853886834947131701352301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1138515779929508935136401 853886834947131701352301)
                    ·
                      refine ⟨320207563105174388007113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 853886834947131701352301 320207563105174388007113)
                      ·
                        rfl

theorem cell23_623602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_623602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623602 prefixEnd_623602 := by exact prefixLift 623602
  have htrace : WordTrace (prefixWord ++ tailWord_623602) baseStart_623602 baseEnd_623602 := by
    simpa [prefixWord, tailWord_623602, baseEnd_623602] using wordTrace_append hprefix tailTrace_623602
  have hstable : (prefixWord ++ tailWord_623602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623602).length < 2 ^ (prefixWord ++ tailWord_623602).sum := by decide
  have hdescent : baseEnd_623602 < baseStart_623602 := by decide
  rcases family_descends (prefixWord ++ tailWord_623602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623641 : List Nat := [1, 2, 1, 2, 1, 1, 4, 4, 1, 1, 5]
def baseStart_623641 : Nat := 118140960795 + 623641 * 2 ^ 59
def prefixEnd_623641 : Nat := 4983230072969 + 3 ^ 40 * 623641 * 2
def baseEnd_623641 : Nat := 320227588850699735419433

theorem tailTrace_623641 : CollatzResearch.WordTrace tailWord_623641 prefixEnd_623641 320227588850699735419433 := by
  unfold tailWord_623641
  simp only [CollatzResearch.WordTrace]
  refine ⟨22746055933662641248262777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15164037289108427498841851 22746055933662641248262777)
  ·
    refine ⟨17059541950246980936197083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22746055933662641248262777 17059541950246980936197083)
    ·
      refine ⟨25589312925370471404295625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17059541950246980936197083 25589312925370471404295625)
      ·
        refine ⟨19191984694027853553221719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25589312925370471404295625 19191984694027853553221719)
        ·
          refine ⟨28787977041041780329832579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19191984694027853553221719 28787977041041780329832579)
          ·
            refine ⟨43181965561562670494748869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28787977041041780329832579 43181965561562670494748869)
            ·
              refine ⟨8096618542793000717765413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43181965561562670494748869 8096618542793000717765413)
              ·
                refine ⟨1518115976773687634581015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8096618542793000717765413 1518115976773687634581015)
                ·
                  refine ⟨2277173965160531451871523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518115976773687634581015 2277173965160531451871523)
                  ·
                    refine ⟨3415760947740797177807285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2277173965160531451871523 3415760947740797177807285)
                    ·
                      refine ⟨320227588850699735419433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3415760947740797177807285 320227588850699735419433)
                      ·
                        rfl

theorem cell23_623641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_623641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623641 prefixEnd_623641 := by exact prefixLift 623641
  have htrace : WordTrace (prefixWord ++ tailWord_623641) baseStart_623641 baseEnd_623641 := by
    simpa [prefixWord, tailWord_623641, baseEnd_623641] using wordTrace_append hprefix tailTrace_623641
  have hstable : (prefixWord ++ tailWord_623641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623641).length < 2 ^ (prefixWord ++ tailWord_623641).sum := by decide
  have hdescent : baseEnd_623641 < baseStart_623641 := by decide
  rcases family_descends (prefixWord ++ tailWord_623641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623655 : List Nat := [1, 1, 7, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_623655 : Nat := 118140960795 + 623655 * 2 ^ 59
def prefixEnd_623655 : Nat := 4983230072969 + 3 ^ 40 * 623655 * 2
def baseEnd_623655 : Nat := 320234777579862680644369

theorem tailTrace_623655 : CollatzResearch.WordTrace tailWord_623655 prefixEnd_623655 320234777579862680644369 := by
  unfold tailWord_623655
  simp only [CollatzResearch.WordTrace]
  refine ⟨22746566555611921639272419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15164377703741281092848279 22746566555611921639272419)
  ·
    refine ⟨34119849833417882458908629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22746566555611921639272419 34119849833417882458908629)
    ·
      refine ⟨799683980470731620130671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 34119849833417882458908629 799683980470731620130671)
      ·
        refine ⟨1199525970706097430196007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799683980470731620130671 1199525970706097430196007)
        ·
          refine ⟨1799288956059146145294011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199525970706097430196007 1799288956059146145294011)
          ·
            refine ⟨2698933434088719217941017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1799288956059146145294011 2698933434088719217941017)
            ·
              refine ⟨2024200075566539413455763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2698933434088719217941017 2024200075566539413455763)
              ·
                refine ⟨3036300113349809120183645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2024200075566539413455763 3036300113349809120183645)
                ·
                  refine ⟨1138612542506178420068867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3036300113349809120183645 1138612542506178420068867)
                  ·
                    refine ⟨1707918813759267630103301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1138612542506178420068867 1707918813759267630103301)
                    ·
                      refine ⟨320234777579862680644369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1707918813759267630103301 320234777579862680644369)
                      ·
                        rfl

theorem cell23_623655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_623655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623655 prefixEnd_623655 := by exact prefixLift 623655
  have htrace : WordTrace (prefixWord ++ tailWord_623655) baseStart_623655 baseEnd_623655 := by
    simpa [prefixWord, tailWord_623655, baseEnd_623655] using wordTrace_append hprefix tailTrace_623655
  have hstable : (prefixWord ++ tailWord_623655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623655).length < 2 ^ (prefixWord ++ tailWord_623655).sum := by decide
  have hdescent : baseEnd_623655 < baseStart_623655 := by decide
  rcases family_descends (prefixWord ++ tailWord_623655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623672 : List Nat := [2, 1, 2, 1, 5, 3, 2, 1, 1, 1, 4]
def baseStart_623672 : Nat := 118140960795 + 623672 * 2 ^ 59
def prefixEnd_623672 : Nat := 4983230072969 + 3 ^ 40 * 623672 * 2
def baseEnd_623672 : Nat := 320243506750989114131791

theorem tailTrace_623672 : CollatzResearch.WordTrace tailWord_623672 prefixEnd_623672 320243506750989114131791 := by
  unfold tailWord_623672
  simp only [CollatzResearch.WordTrace]
  refine ⟨11373593298275166771320635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15164791064366889028427513 11373593298275166771320635)
  ·
    refine ⟨17060389947412750156980953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11373593298275166771320635 17060389947412750156980953)
    ·
      refine ⟨12795292460559562617735715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17060389947412750156980953 12795292460559562617735715)
      ·
        refine ⟨19192938690839343926603573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12795292460559562617735715 19192938690839343926603573)
        ·
          refine ⟨1799338002266188493119085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19192938690839343926603573 1799338002266188493119085)
          ·
            refine ⟨674751750849820684919657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1799338002266188493119085 674751750849820684919657)
            ·
              refine ⟨506063813137365513689743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 674751750849820684919657 506063813137365513689743)
              ·
                refine ⟨759095719706048270534615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506063813137365513689743 759095719706048270534615)
                ·
                  refine ⟨1138643579559072405801923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759095719706048270534615 1138643579559072405801923)
                  ·
                    refine ⟨1707965369338608608702885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1138643579559072405801923 1707965369338608608702885)
                    ·
                      refine ⟨320243506750989114131791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1707965369338608608702885 320243506750989114131791)
                      ·
                        rfl

theorem cell23_623672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 1, 1, 4].length) (baseStart_623672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623672 prefixEnd_623672 := by exact prefixLift 623672
  have htrace : WordTrace (prefixWord ++ tailWord_623672) baseStart_623672 baseEnd_623672 := by
    simpa [prefixWord, tailWord_623672, baseEnd_623672] using wordTrace_append hprefix tailTrace_623672
  have hstable : (prefixWord ++ tailWord_623672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623672).length < 2 ^ (prefixWord ++ tailWord_623672).sum := by decide
  have hdescent : baseEnd_623672 < baseStart_623672 := by decide
  rcases family_descends (prefixWord ++ tailWord_623672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623678 : List Nat := [4, 2, 1, 3, 1, 2, 10]
def baseStart_623678 : Nat := 118140960795 + 623678 * 2 ^ 59
def prefixEnd_623678 : Nat := 4983230072969 + 3 ^ 40 * 623678 * 2
def baseEnd_623678 : Nat := 3953661575739704822923

theorem tailTrace_623678 : CollatzResearch.WordTrace tailWord_623678 prefixEnd_623678 3953661575739704822923 := by
  unfold tailWord_623678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2843425679316074570919961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15164936956352397711573125 2843425679316074570919961)
  ·
    refine ⟨2132569259487055928189971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2843425679316074570919961 2132569259487055928189971)
    ·
      refine ⟨3198853889230583892284957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2132569259487055928189971 3198853889230583892284957)
      ·
        refine ⟨1199570208461468959606859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3198853889230583892284957 1199570208461468959606859)
        ·
          refine ⟨1799355312692203439410289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1199570208461468959606859 1799355312692203439410289)
          ·
            refine ⟨1349516484519152579557717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1799355312692203439410289 1349516484519152579557717)
            ·
              refine ⟨3953661575739704822923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1349516484519152579557717 3953661575739704822923)
              ·
                rfl

theorem cell23_623678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 10].length) (baseStart_623678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623678 prefixEnd_623678 := by exact prefixLift 623678
  have htrace : WordTrace (prefixWord ++ tailWord_623678) baseStart_623678 baseEnd_623678 := by
    simpa [prefixWord, tailWord_623678, baseEnd_623678] using wordTrace_append hprefix tailTrace_623678
  have hstable : (prefixWord ++ tailWord_623678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623678).length < 2 ^ (prefixWord ++ tailWord_623678).sum := by decide
  have hdescent : baseEnd_623678 < baseStart_623678 := by decide
  rcases family_descends (prefixWord ++ tailWord_623678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623702 : List Nat := [5, 2, 2, 1, 2, 1, 1, 1, 1, 1, 6]
def baseStart_623702 : Nat := 118140960795 + 623702 * 2 ^ 59
def prefixEnd_623702 : Nat := 4983230072969 + 3 ^ 40 * 623702 * 2
def baseEnd_623702 : Nat := 320258911170623996756653

theorem tailTrace_623702 : CollatzResearch.WordTrace tailWord_623702 prefixEnd_623702 320258911170623996756653 := by
  unfold tailWord_623702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1421767549152603041639585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15165520524294432444155573 1421767549152603041639585)
  ·
    refine ⟨1066325661864452281229689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1421767549152603041639585 1066325661864452281229689)
    ·
      refine ⟨799744246398339210922267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1066325661864452281229689 799744246398339210922267)
      ·
        refine ⟨1199616369597508816383401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799744246398339210922267 1199616369597508816383401)
        ·
          refine ⟨899712277198131612287551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1199616369597508816383401 899712277198131612287551)
          ·
            refine ⟨1349568415797197418431327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899712277198131612287551 1349568415797197418431327)
            ·
              refine ⟨2024352623695796127646991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349568415797197418431327 2024352623695796127646991)
              ·
                refine ⟨3036528935543694191470487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2024352623695796127646991 3036528935543694191470487)
                ·
                  refine ⟨4554793403315541287205731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3036528935543694191470487 4554793403315541287205731)
                  ·
                    refine ⟨6832190104973311930808597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4554793403315541287205731 6832190104973311930808597)
                    ·
                      refine ⟨320258911170623996756653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6832190104973311930808597 320258911170623996756653)
                      ·
                        rfl

theorem cell23_623702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_623702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623702 prefixEnd_623702 := by exact prefixLift 623702
  have htrace : WordTrace (prefixWord ++ tailWord_623702) baseStart_623702 baseEnd_623702 := by
    simpa [prefixWord, tailWord_623702, baseEnd_623702] using wordTrace_append hprefix tailTrace_623702
  have hstable : (prefixWord ++ tailWord_623702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623702).length < 2 ^ (prefixWord ++ tailWord_623702).sum := by decide
  have hdescent : baseEnd_623702 < baseStart_623702 := by decide
  rcases family_descends (prefixWord ++ tailWord_623702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623709 : List Nat := [1, 4, 4, 1, 2, 1, 2, 2, 1, 2, 3]
def baseStart_623709 : Nat := 118140960795 + 623709 * 2 ^ 59
def prefixEnd_623709 : Nat := 4983230072969 + 3 ^ 40 * 623709 * 2
def baseEnd_623709 : Nat := 320262505535205469369121

theorem tailTrace_623709 : CollatzResearch.WordTrace tailWord_623709 prefixEnd_623709 320262505535205469369121 := by
  unfold tailWord_623709
  simp only [CollatzResearch.WordTrace]
  refine ⟨22748536097416288861738181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15165690731610859241158787 22748536097416288861738181)
  ·
    refine ⟨4265350518265554161575909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22748536097416288861738181 4265350518265554161575909)
    ·
      refine ⟨799753222174791405295483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4265350518265554161575909 799753222174791405295483)
      ·
        refine ⟨1199629833262187107943225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 799753222174791405295483 1199629833262187107943225)
        ·
          refine ⟨899722374946640330957419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1199629833262187107943225 899722374946640330957419)
          ·
            refine ⟨1349583562419960496436129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899722374946640330957419 1349583562419960496436129)
            ·
              refine ⟨1012187671814970372327097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1349583562419960496436129 1012187671814970372327097)
              ·
                refine ⟨759140753861227779245323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1012187671814970372327097 759140753861227779245323)
                ·
                  refine ⟨1138711130791841668867985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759140753861227779245323 1138711130791841668867985)
                  ·
                    refine ⟨854033348093881251650989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1138711130791841668867985 854033348093881251650989)
                    ·
                      refine ⟨320262505535205469369121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 854033348093881251650989 320262505535205469369121)
                      ·
                        rfl

theorem cell23_623709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_623709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623709 prefixEnd_623709 := by exact prefixLift 623709
  have htrace : WordTrace (prefixWord ++ tailWord_623709) baseStart_623709 baseEnd_623709 := by
    simpa [prefixWord, tailWord_623709, baseEnd_623709] using wordTrace_append hprefix tailTrace_623709
  have hstable : (prefixWord ++ tailWord_623709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623709).length < 2 ^ (prefixWord ++ tailWord_623709).sum := by decide
  have hdescent : baseEnd_623709 < baseStart_623709 := by decide
  rcases family_descends (prefixWord ++ tailWord_623709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623805 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 2, 5, 2]
def baseStart_623805 : Nat := 118140960795 + 623805 * 2 ^ 59
def prefixEnd_623805 : Nat := 4983230072969 + 3 ^ 40 * 623805 * 2
def baseEnd_623805 : Nat := 320311799678037093768679

theorem tailTrace_623805 : CollatzResearch.WordTrace tailWord_623805 prefixEnd_623805 320311799678037093768679 := by
  unfold tailWord_623805
  simp only [CollatzResearch.WordTrace]
  refine ⟨22752037505068497257232869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15168025003378998171488579 22752037505068497257232869)
  ·
    refine ⟨4266007032200343235731163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22752037505068497257232869 4266007032200343235731163)
    ·
      refine ⟨6399010548300514853596745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4266007032200343235731163 6399010548300514853596745)
      ·
        refine ⟨4799257911225386140197559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6399010548300514853596745 4799257911225386140197559)
        ·
          refine ⟨7198886866838079210296339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4799257911225386140197559 7198886866838079210296339)
          ·
            refine ⟨10798330300257118815444509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7198886866838079210296339 10798330300257118815444509)
            ·
              refine ⟨4049373862596419555791691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10798330300257118815444509 4049373862596419555791691)
              ·
                refine ⟨6074060793894629333687537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4049373862596419555791691 6074060793894629333687537)
                ·
                  refine ⟨4555545595420972000265653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6074060793894629333687537 4555545595420972000265653)
                  ·
                    refine ⟨427082399570716125024905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4555545595420972000265653 427082399570716125024905)
                    ·
                      refine ⟨320311799678037093768679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 427082399570716125024905 320311799678037093768679)
                      ·
                        rfl

theorem cell23_623805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 2, 5, 2].length) (baseStart_623805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623805 prefixEnd_623805 := by exact prefixLift 623805
  have htrace : WordTrace (prefixWord ++ tailWord_623805) baseStart_623805 baseEnd_623805 := by
    simpa [prefixWord, tailWord_623805, baseEnd_623805] using wordTrace_append hprefix tailTrace_623805
  have hstable : (prefixWord ++ tailWord_623805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623805).length < 2 ^ (prefixWord ++ tailWord_623805).sum := by decide
  have hdescent : baseEnd_623805 < baseStart_623805 := by decide
  rcases family_descends (prefixWord ++ tailWord_623805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623812 : List Nat := [2, 3, 3, 1, 3, 1, 1, 1, 2, 3, 3]
def baseStart_623812 : Nat := 118140960795 + 623812 * 2 ^ 59
def prefixEnd_623812 : Nat := 4983230072969 + 3 ^ 40 * 623812 * 2
def baseEnd_623812 : Nat := 320315394042618566381147

theorem tailTrace_623812 : CollatzResearch.WordTrace tailWord_623812 prefixEnd_623812 320315394042618566381147 := by
  unfold tailWord_623812
  simp only [CollatzResearch.WordTrace]
  refine ⟨11376146408021568726368845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15168195210695424968491793 11376146408021568726368845)
  ·
    refine ⟨4266054903008088272388317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11376146408021568726368845 4266054903008088272388317)
    ·
      refine ⟨1599770588628033102145619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4266054903008088272388317 1599770588628033102145619)
      ·
        refine ⟨2399655882942049653218429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1599770588628033102145619 2399655882942049653218429)
        ·
          refine ⟨899870956103268619956911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2399655882942049653218429 899870956103268619956911)
          ·
            refine ⟨1349806434154902929935367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 899870956103268619956911 1349806434154902929935367)
            ·
              refine ⟨2024709651232354394903051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1349806434154902929935367 2024709651232354394903051)
              ·
                refine ⟨3037064476848531592354577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2024709651232354394903051 3037064476848531592354577)
                ·
                  refine ⟨2277798357636398694265933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3037064476848531592354577 2277798357636398694265933)
                  ·
                    refine ⟨854174384113649510349725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2277798357636398694265933 854174384113649510349725)
                    ·
                      refine ⟨320315394042618566381147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 854174384113649510349725 320315394042618566381147)
                      ·
                        rfl

theorem cell23_623812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_623812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623812 prefixEnd_623812 := by exact prefixLift 623812
  have htrace : WordTrace (prefixWord ++ tailWord_623812) baseStart_623812 baseEnd_623812 := by
    simpa [prefixWord, tailWord_623812, baseEnd_623812] using wordTrace_append hprefix tailTrace_623812
  have hstable : (prefixWord ++ tailWord_623812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623812).length < 2 ^ (prefixWord ++ tailWord_623812).sum := by decide
  have hdescent : baseEnd_623812 < baseStart_623812 := by decide
  rcases family_descends (prefixWord ++ tailWord_623812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623832 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 2, 5]
def baseStart_623832 : Nat := 118140960795 + 623832 * 2 ^ 59
def prefixEnd_623832 : Nat := 4983230072969 + 3 ^ 40 * 623832 * 2
def baseEnd_623832 : Nat := 106775221218569496043685

theorem tailTrace_623832 : CollatzResearch.WordTrace tailWord_623832 prefixEnd_623832 106775221218569496043685 := by
  unfold tailWord_623832
  simp only [CollatzResearch.WordTrace]
  refine ⟨11376511137985340434232875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15168681517313787245643833 11376511137985340434232875)
  ·
    refine ⟨17064766706978010651349313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11376511137985340434232875 17064766706978010651349313)
    ·
      refine ⟨12798575030233507988511985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17064766706978010651349313 12798575030233507988511985)
      ·
        refine ⟨9598931272675130991383989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12798575030233507988511985 9598931272675130991383989)
        ·
          refine ⟨899899806813293530442249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9598931272675130991383989 899899806813293530442249)
          ·
            refine ⟨674924855109970147831687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 899899806813293530442249 674924855109970147831687)
            ·
              refine ⟨1012387282664955221747531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 674924855109970147831687 1012387282664955221747531)
              ·
                refine ⟨1518580923997432832621297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012387282664955221747531 1518580923997432832621297)
                ·
                  refine ⟨1138935692998074624465973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1518580923997432832621297 1138935692998074624465973)
                  ·
                    refine ⟨106775221218569496043685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1138935692998074624465973 106775221218569496043685)
                    ·
                      rfl

theorem cell23_623832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 2, 5].length) (baseStart_623832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623832 prefixEnd_623832 := by exact prefixLift 623832
  have htrace : WordTrace (prefixWord ++ tailWord_623832) baseStart_623832 baseEnd_623832 := by
    simpa [prefixWord, tailWord_623832, baseEnd_623832] using wordTrace_append hprefix tailTrace_623832
  have hstable : (prefixWord ++ tailWord_623832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623832).length < 2 ^ (prefixWord ++ tailWord_623832).sum := by decide
  have hdescent : baseEnd_623832 < baseStart_623832 := by decide
  rcases family_descends (prefixWord ++ tailWord_623832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623848 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 1, 3, 6]
def baseStart_623848 : Nat := 118140960795 + 623848 * 2 ^ 59
def prefixEnd_623848 : Nat := 4983230072969 + 3 ^ 40 * 623848 * 2
def baseEnd_623848 : Nat := 320333879346180425530981

theorem tailTrace_623848 : CollatzResearch.WordTrace tailWord_623848 prefixEnd_623848 320333879346180425530981 := by
  unfold tailWord_623848
  simp only [CollatzResearch.WordTrace]
  refine ⟨11376802921956357800524099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15169070562608477067365465 11376802921956357800524099)
  ·
    refine ⟨17065204382934536700786149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11376802921956357800524099 17065204382934536700786149)
    ·
      refine ⟨3199725821800225631397403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17065204382934536700786149 3199725821800225631397403)
      ·
        refine ⟨4799588732700338447096105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3199725821800225631397403 4799588732700338447096105)
        ·
          refine ⟨3599691549525253835322079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4799588732700338447096105 3599691549525253835322079)
          ·
            refine ⟨5399537324287880752983119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3599691549525253835322079 5399537324287880752983119)
            ·
              refine ⟨8099305986431821129474679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5399537324287880752983119 8099305986431821129474679)
              ·
                refine ⟨12148958979647731694212019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8099305986431821129474679 12148958979647731694212019)
                ·
                  refine ⟨18223438469471597541318029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12148958979647731694212019 18223438469471597541318029)
                  ·
                    refine ⟨6833789426051849077994261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18223438469471597541318029 6833789426051849077994261)
                    ·
                      refine ⟨320333879346180425530981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6833789426051849077994261 320333879346180425530981)
                      ·
                        rfl

theorem cell23_623848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_623848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623848 prefixEnd_623848 := by exact prefixLift 623848
  have htrace : WordTrace (prefixWord ++ tailWord_623848) baseStart_623848 baseEnd_623848 := by
    simpa [prefixWord, tailWord_623848, baseEnd_623848] using wordTrace_append hprefix tailTrace_623848
  have hstable : (prefixWord ++ tailWord_623848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623848).length < 2 ^ (prefixWord ++ tailWord_623848).sum := by decide
  have hdescent : baseEnd_623848 < baseStart_623848 := by decide
  rcases family_descends (prefixWord ++ tailWord_623848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623888 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 9, 5]
def baseStart_623888 : Nat := 118140960795 + 623888 * 2 ^ 59
def prefixEnd_623888 : Nat := 4983230072969 + 3 ^ 40 * 623888 * 2
def baseEnd_623888 : Nat := 106784806190786756343599

theorem tailTrace_623888 : CollatzResearch.WordTrace tailWord_623888 prefixEnd_623888 106784806190786756343599 := by
  unfold tailWord_623888
  simp only [CollatzResearch.WordTrace]
  refine ⟨11377532381883901216252159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15170043175845201621669545 11377532381883901216252159)
  ·
    refine ⟨17066298572825851824378239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11377532381883901216252159 17066298572825851824378239)
    ·
      refine ⟨25599447859238777736567359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17066298572825851824378239 25599447859238777736567359)
      ·
        refine ⟨38399171788858166604851039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25599447859238777736567359 38399171788858166604851039)
        ·
          refine ⟨57598757683287249907276559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38399171788858166604851039 57598757683287249907276559)
          ·
            refine ⟨86398136524930874860914839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57598757683287249907276559 86398136524930874860914839)
            ·
              refine ⟨129597204787396312291372259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86398136524930874860914839 129597204787396312291372259)
              ·
                refine ⟨194395807181094468437058389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129597204787396312291372259 194395807181094468437058389)
                ·
                  refine ⟨1139037932701725400998389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 194395807181094468437058389 1139037932701725400998389)
                  ·
                    refine ⟨106784806190786756343599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1139037932701725400998389 106784806190786756343599)
                    ·
                      rfl

theorem cell23_623888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9, 5].length) (baseStart_623888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623888 prefixEnd_623888 := by exact prefixLift 623888
  have htrace : WordTrace (prefixWord ++ tailWord_623888) baseStart_623888 baseEnd_623888 := by
    simpa [prefixWord, tailWord_623888, baseEnd_623888] using wordTrace_append hprefix tailTrace_623888
  have hstable : (prefixWord ++ tailWord_623888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623888).length < 2 ^ (prefixWord ++ tailWord_623888).sum := by decide
  have hdescent : baseEnd_623888 < baseStart_623888 := by decide
  rcases family_descends (prefixWord ++ tailWord_623888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623955 : List Nat := [1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 4]
def baseStart_623955 : Nat := 118140960795 + 623955 * 2 ^ 59
def prefixEnd_623955 : Nat := 4983230072969 + 3 ^ 40 * 623955 * 2
def baseEnd_623955 : Nat := 320388821776211506892989

theorem tailTrace_623955 : CollatzResearch.WordTrace tailWord_623955 prefixEnd_623955 320388821776211506892989 := by
  unfold tailWord_623955
  simp only [CollatzResearch.WordTrace]
  refine ⟨22757508454525072875193319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15171672303016715250128879 22757508454525072875193319)
  ·
    refine ⟨34136262681787609312789979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22757508454525072875193319 34136262681787609312789979)
    ·
      refine ⟨51204394022681413969184969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34136262681787609312789979 51204394022681413969184969)
      ·
        refine ⟨38403295517011060476888727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51204394022681413969184969 38403295517011060476888727)
        ·
          refine ⟨57604943275516590715333091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38403295517011060476888727 57604943275516590715333091)
          ·
            refine ⟨86407414913274886072999637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57604943275516590715333091 86407414913274886072999637)
            ·
              refine ⟨2025173787029880142335929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 86407414913274886072999637 2025173787029880142335929)
              ·
                refine ⟨1518880340272410106751947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2025173787029880142335929 1518880340272410106751947)
                ·
                  refine ⟨2278320510408615160127921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518880340272410106751947 2278320510408615160127921)
                  ·
                    refine ⟨1708740382806461370095941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2278320510408615160127921 1708740382806461370095941)
                    ·
                      refine ⟨320388821776211506892989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1708740382806461370095941 320388821776211506892989)
                      ·
                        rfl

theorem cell23_623955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 2, 4].length) (baseStart_623955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623955 prefixEnd_623955 := by exact prefixLift 623955
  have htrace : WordTrace (prefixWord ++ tailWord_623955) baseStart_623955 baseEnd_623955 := by
    simpa [prefixWord, tailWord_623955, baseEnd_623955] using wordTrace_append hprefix tailTrace_623955
  have hstable : (prefixWord ++ tailWord_623955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623955).length < 2 ^ (prefixWord ++ tailWord_623955).sum := by decide
  have hdescent : baseEnd_623955 < baseStart_623955 := by decide
  rcases family_descends (prefixWord ++ tailWord_623955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623959 : List Nat := [1, 1, 3, 2, 3, 3, 3, 1, 1, 1, 4]
def baseStart_623959 : Nat := 118140960795 + 623959 * 2 ^ 59
def prefixEnd_623959 : Nat := 4983230072969 + 3 ^ 40 * 623959 * 2
def baseEnd_623959 : Nat := 320390875698829491242971

theorem tailTrace_623959 : CollatzResearch.WordTrace tailWord_623959 prefixEnd_623959 320390875698829491242971 := by
  unfold tailWord_623959
  simp only [CollatzResearch.WordTrace]
  refine ⟨22757654346510581558338931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15171769564340387705559287 22757654346510581558338931)
  ·
    refine ⟨34136481519765872337508397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22757654346510581558338931 34136481519765872337508397)
    ·
      refine ⟨12801180569912202126565649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34136481519765872337508397 12801180569912202126565649)
      ·
        refine ⟨9600885427434151594924237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12801180569912202126565649 9600885427434151594924237)
        ·
          refine ⟨3600332035287806848096589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9600885427434151594924237 3600332035287806848096589)
          ·
            refine ⟨1350124513232927568036221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3600332035287806848096589 1350124513232927568036221)
            ·
              refine ⟨506296692462347838013583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1350124513232927568036221 506296692462347838013583)
              ·
                refine ⟨759445038693521757020375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 506296692462347838013583 759445038693521757020375)
                ·
                  refine ⟨1139167558040282635530563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759445038693521757020375 1139167558040282635530563)
                  ·
                    refine ⟨1708751337060423953295845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1139167558040282635530563 1708751337060423953295845)
                    ·
                      refine ⟨320390875698829491242971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1708751337060423953295845 320390875698829491242971)
                      ·
                        rfl

theorem cell23_623959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 3, 1, 1, 1, 4].length) (baseStart_623959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623959 prefixEnd_623959 := by exact prefixLift 623959
  have htrace : WordTrace (prefixWord ++ tailWord_623959) baseStart_623959 baseEnd_623959 := by
    simpa [prefixWord, tailWord_623959, baseEnd_623959] using wordTrace_append hprefix tailTrace_623959
  have hstable : (prefixWord ++ tailWord_623959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623959).length < 2 ^ (prefixWord ++ tailWord_623959).sum := by decide
  have hdescent : baseEnd_623959 < baseStart_623959 := by decide
  rcases family_descends (prefixWord ++ tailWord_623959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623962 : List Nat := [3, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3]
def baseStart_623962 : Nat := 118140960795 + 623962 * 2 ^ 59
def prefixEnd_623962 : Nat := 4983230072969 + 3 ^ 40 * 623962 * 2
def baseEnd_623962 : Nat := 320392416140792979505457

theorem tailTrace_623962 : CollatzResearch.WordTrace tailWord_623962 prefixEnd_623962 320392416140792979505457 := by
  unfold tailWord_623962
  simp only [CollatzResearch.WordTrace]
  refine ⟨5689440941374928267674535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15171842510333142047132093 5689440941374928267674535)
  ·
    refine ⟨8534161412062392401511803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5689440941374928267674535 8534161412062392401511803)
    ·
      refine ⟨12801242118093588602267705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8534161412062392401511803 12801242118093588602267705)
      ·
        refine ⟨9600931588570191451700779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12801242118093588602267705 9600931588570191451700779)
        ·
          refine ⟨14401397382855287177551169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9600931588570191451700779 14401397382855287177551169)
          ·
            refine ⟨10801048037141465383163377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14401397382855287177551169 10801048037141465383163377)
            ·
              refine ⟨8100786027856099037372533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10801048037141465383163377 8100786027856099037372533)
              ·
                refine ⟨759448690111509284753675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8100786027856099037372533 759448690111509284753675)
                ·
                  refine ⟨1139173035167263927130513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759448690111509284753675 1139173035167263927130513)
                  ·
                    refine ⟨854379776375447945347885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1139173035167263927130513 854379776375447945347885)
                    ·
                      refine ⟨320392416140792979505457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 854379776375447945347885 320392416140792979505457)
                      ·
                        rfl

theorem cell23_623962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_623962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623962 prefixEnd_623962 := by exact prefixLift 623962
  have htrace : WordTrace (prefixWord ++ tailWord_623962) baseStart_623962 baseEnd_623962 := by
    simpa [prefixWord, tailWord_623962, baseEnd_623962] using wordTrace_append hprefix tailTrace_623962
  have hstable : (prefixWord ++ tailWord_623962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623962).length < 2 ^ (prefixWord ++ tailWord_623962).sum := by decide
  have hdescent : baseEnd_623962 < baseStart_623962 := by decide
  rcases family_descends (prefixWord ++ tailWord_623962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_623989 : List Nat := [1, 3, 4, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_623989 : Nat := 118140960795 + 623989 * 2 ^ 59
def prefixEnd_623989 : Nat := 4983230072969 + 3 ^ 40 * 623989 * 2
def baseEnd_623989 : Nat := 320406280118464373867833

theorem tailTrace_623989 : CollatzResearch.WordTrace tailWord_623989 prefixEnd_623989 320406280118464373867833 := by
  unfold tailWord_623989
  simp only [CollatzResearch.WordTrace]
  refine ⟨22758748536401896681931021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15172499024267931121287347 22758748536401896681931021)
  ·
    refine ⟨8534530701150711255724133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22758748536401896681931021 8534530701150711255724133)
    ·
      refine ⟨1600224506465758360448275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8534530701150711255724133 1600224506465758360448275)
      ·
        refine ⟨2400336759698637540672413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1600224506465758360448275 2400336759698637540672413)
        ·
          refine ⟨900126284886989077752155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2400336759698637540672413 900126284886989077752155)
          ·
            refine ⟨1350189427330483616628233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900126284886989077752155 1350189427330483616628233)
            ·
              refine ⟨1012642070497862712471175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1350189427330483616628233 1012642070497862712471175)
              ·
                refine ⟨1518963105746794068706763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012642070497862712471175 1518963105746794068706763)
                ·
                  refine ⟨2278444658620191103060145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1518963105746794068706763 2278444658620191103060145)
                  ·
                    refine ⟨1708833493965143327295109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2278444658620191103060145 1708833493965143327295109)
                    ·
                      refine ⟨320406280118464373867833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1708833493965143327295109 320406280118464373867833)
                      ·
                        rfl

theorem cell23_623989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_623989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_623989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_623989 prefixEnd_623989 := by exact prefixLift 623989
  have htrace : WordTrace (prefixWord ++ tailWord_623989) baseStart_623989 baseEnd_623989 := by
    simpa [prefixWord, tailWord_623989, baseEnd_623989] using wordTrace_append hprefix tailTrace_623989
  have hstable : (prefixWord ++ tailWord_623989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_623989).length < 2 ^ (prefixWord ++ tailWord_623989).sum := by decide
  have hdescent : baseEnd_623989 < baseStart_623989 := by decide
  rcases family_descends (prefixWord ++ tailWord_623989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624025 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 2, 6]
def baseStart_624025 : Nat := 118140960795 + 624025 * 2 ^ 59
def prefixEnd_624025 : Nat := 4983230072969 + 3 ^ 40 * 624025 * 2
def baseEnd_624025 : Nat := 106808255140675411005889

theorem tailTrace_624025 : CollatzResearch.WordTrace tailWord_624025 prefixEnd_624025 106808255140675411005889 := by
  unfold tailWord_624025
  simp only [CollatzResearch.WordTrace]
  refine ⟨22760061564271474830241529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15173374376180983220161019 22760061564271474830241529)
  ·
    refine ⟨17070046173203606122681147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22760061564271474830241529 17070046173203606122681147)
    ·
      refine ⟨25605069259805409184021721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17070046173203606122681147 25605069259805409184021721)
      ·
        refine ⟨19203801944854056888016291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25605069259805409184021721 19203801944854056888016291)
        ·
          refine ⟨28805702917281085332024437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19203801944854056888016291 28805702917281085332024437)
          ·
            refine ⟨2700534648495101749877291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28805702917281085332024437 2700534648495101749877291)
            ·
              refine ⟨4050801972742652624815937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2700534648495101749877291 4050801972742652624815937)
              ·
                refine ⟨3038101479556989468611953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4050801972742652624815937 3038101479556989468611953)
                ·
                  refine ⟨2278576109667742101458965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3038101479556989468611953 2278576109667742101458965)
                  ·
                    refine ⟨106808255140675411005889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2278576109667742101458965 106808255140675411005889)
                    ·
                      rfl

theorem cell23_624025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 6].length) (baseStart_624025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624025 prefixEnd_624025 := by exact prefixLift 624025
  have htrace : WordTrace (prefixWord ++ tailWord_624025) baseStart_624025 baseEnd_624025 := by
    simpa [prefixWord, tailWord_624025, baseEnd_624025] using wordTrace_append hprefix tailTrace_624025
  have hstable : (prefixWord ++ tailWord_624025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624025).length < 2 ^ (prefixWord ++ tailWord_624025).sum := by decide
  have hdescent : baseEnd_624025 < baseStart_624025 := by decide
  rcases family_descends (prefixWord ++ tailWord_624025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624055 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 7]
def baseStart_624055 : Nat := 118140960795 + 624055 * 2 ^ 59
def prefixEnd_624055 : Nat := 4983230072969 + 3 ^ 40 * 624055 * 2
def baseEnd_624055 : Nat := 35604463315740123960281

theorem tailTrace_624055 : CollatzResearch.WordTrace tailWord_624055 prefixEnd_624055 35604463315740123960281 := by
  unfold tailWord_624055
  simp only [CollatzResearch.WordTrace]
  refine ⟨22761155754162789953833619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15174103836108526635889079 22761155754162789953833619)
  ·
    refine ⟨34141733631244184930750429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22761155754162789953833619 34141733631244184930750429)
    ·
      refine ⟨12803150111716569349031411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34141733631244184930750429 12803150111716569349031411)
      ·
        refine ⟨19204725167574854023547117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12803150111716569349031411 19204725167574854023547117)
        ·
          refine ⟨7201771937840570258830169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19204725167574854023547117 7201771937840570258830169)
          ·
            refine ⟨5401328953380427694122627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7201771937840570258830169 5401328953380427694122627)
            ·
              refine ⟨8101993430070641541183941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5401328953380427694122627 8101993430070641541183941)
              ·
                refine ⟨1519123768138245288971989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8101993430070641541183941 1519123768138245288971989)
                ·
                  refine ⟨35604463315740123960281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1519123768138245288971989 35604463315740123960281)
                  ·
                    rfl

theorem cell23_624055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 7].length) (baseStart_624055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624055 prefixEnd_624055 := by exact prefixLift 624055
  have htrace : WordTrace (prefixWord ++ tailWord_624055) baseStart_624055 baseEnd_624055 := by
    simpa [prefixWord, tailWord_624055, baseEnd_624055] using wordTrace_append hprefix tailTrace_624055
  have hstable : (prefixWord ++ tailWord_624055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624055).length < 2 ^ (prefixWord ++ tailWord_624055).sum := by decide
  have hdescent : baseEnd_624055 < baseStart_624055 := by decide
  rcases family_descends (prefixWord ++ tailWord_624055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624134 : List Nat := [6, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2]
def baseStart_624134 : Nat := 118140960795 + 624134 * 2 ^ 59
def prefixEnd_624134 : Nat := 4983230072969 + 3 ^ 40 * 624134 * 2
def baseEnd_624134 : Nat := 320480734813366306554667

theorem tailTrace_624134 : CollatzResearch.WordTrace tailWord_624134 prefixEnd_624134 320480734813366306554667 := by
  unfold tailWord_624134
  simp only [CollatzResearch.WordTrace]
  refine ⟨711376160027393326436233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15176024747251057630639637 711376160027393326436233)
  ·
    refine ⟨533532120020544994827175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 711376160027393326436233 533532120020544994827175)
    ·
      refine ⟨800298180030817492240763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 533532120020544994827175 800298180030817492240763)
      ·
        refine ⟨1200447270046226238361145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800298180030817492240763 1200447270046226238361145)
        ·
          refine ⟨900335452534669678770859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1200447270046226238361145 900335452534669678770859)
          ·
            refine ⟨1350503178802004518156289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900335452534669678770859 1350503178802004518156289)
            ·
              refine ⟨1012877384101503388617217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1350503178802004518156289 1012877384101503388617217)
              ·
                refine ⟨759658038076127541462913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1012877384101503388617217 759658038076127541462913)
                ·
                  refine ⟨569743528557095656097185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 759658038076127541462913 569743528557095656097185)
                  ·
                    refine ⟨427307646417821742072889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 569743528557095656097185 427307646417821742072889)
                    ·
                      refine ⟨320480734813366306554667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 427307646417821742072889 320480734813366306554667)
                      ·
                        rfl

theorem cell23_624134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_624134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624134 prefixEnd_624134 := by exact prefixLift 624134
  have htrace : WordTrace (prefixWord ++ tailWord_624134) baseStart_624134 baseEnd_624134 := by
    simpa [prefixWord, tailWord_624134, baseEnd_624134] using wordTrace_append hprefix tailTrace_624134
  have hstable : (prefixWord ++ tailWord_624134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624134).length < 2 ^ (prefixWord ++ tailWord_624134).sum := by decide
  have hdescent : baseEnd_624134 < baseStart_624134 := by decide
  rcases family_descends (prefixWord ++ tailWord_624134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624240 : List Nat := [2, 1, 1, 1, 6, 3, 1, 3, 1, 1, 3]
def baseStart_624240 : Nat := 118140960795 + 624240 * 2 ^ 59
def prefixEnd_624240 : Nat := 4983230072969 + 3 ^ 40 * 624240 * 2
def baseEnd_624240 : Nat := 320535163762742891829179

theorem tailTrace_624240 : CollatzResearch.WordTrace tailWord_624240 prefixEnd_624240 320535163762742891829179 := by
  unfold tailWord_624240
  simp only [CollatzResearch.WordTrace]
  refine ⟨11383951629246283274659087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15178602172328377699545449 11383951629246283274659087)
  ·
    refine ⟨17075927443869424911988631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11383951629246283274659087 17075927443869424911988631)
    ·
      refine ⟨25613891165804137367982947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17075927443869424911988631 25613891165804137367982947)
      ·
        refine ⟨38420836748706206051974421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25613891165804137367982947 38420836748706206051974421)
        ·
          refine ⟨1800976722595603408686301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 38420836748706206051974421 1800976722595603408686301)
          ·
            refine ⟨675366270973351278257363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1800976722595603408686301 675366270973351278257363)
            ·
              refine ⟨1013049406460026917386045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675366270973351278257363 1013049406460026917386045)
              ·
                refine ⟨379893527422510094019767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1013049406460026917386045 379893527422510094019767)
                ·
                  refine ⟨569840291133765141029651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 379893527422510094019767 569840291133765141029651)
                  ·
                    refine ⟨854760436700647711544477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 569840291133765141029651 854760436700647711544477)
                    ·
                      refine ⟨320535163762742891829179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 854760436700647711544477 320535163762742891829179)
                      ·
                        rfl

theorem cell23_624240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 3, 1, 1, 3].length) (baseStart_624240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624240 prefixEnd_624240 := by exact prefixLift 624240
  have htrace : WordTrace (prefixWord ++ tailWord_624240) baseStart_624240 baseEnd_624240 := by
    simpa [prefixWord, tailWord_624240, baseEnd_624240] using wordTrace_append hprefix tailTrace_624240
  have hstable : (prefixWord ++ tailWord_624240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624240).length < 2 ^ (prefixWord ++ tailWord_624240).sum := by decide
  have hdescent : baseEnd_624240 < baseStart_624240 := by decide
  rcases family_descends (prefixWord ++ tailWord_624240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624249 : List Nat := [1, 2, 1, 3, 3, 1, 4, 1, 1, 1, 5]
def baseStart_624249 : Nat := 118140960795 + 624249 * 2 ^ 59
def prefixEnd_624249 : Nat := 4983230072969 + 3 ^ 40 * 624249 * 2
def baseEnd_624249 : Nat := 320539785088633356616637

theorem tailTrace_624249 : CollatzResearch.WordTrace tailWord_624249 prefixEnd_624249 320539785088633356616637 := by
  unfold tailWord_624249
  simp only [CollatzResearch.WordTrace]
  refine ⟨22768231515459961086395801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15178821010306640724263867 22768231515459961086395801)
  ·
    refine ⟨17076173636594970814796851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22768231515459961086395801 17076173636594970814796851)
    ·
      refine ⟨25614260454892456222195277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17076173636594970814796851 25614260454892456222195277)
      ·
        refine ⟨9605347670584671083323229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25614260454892456222195277 9605347670584671083323229)
        ·
          refine ⟨3602005376469251656246211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9605347670584671083323229 3602005376469251656246211)
          ·
            refine ⟨5403008064703877484369317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3602005376469251656246211 5403008064703877484369317)
            ·
              refine ⟨1013064012131977028319247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5403008064703877484369317 1013064012131977028319247)
              ·
                refine ⟨1519596018197965542478871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013064012131977028319247 1519596018197965542478871)
                ·
                  refine ⟨2279394027296948313718307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519596018197965542478871 2279394027296948313718307)
                  ·
                    refine ⟨3419091040945422470577461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2279394027296948313718307 3419091040945422470577461)
                    ·
                      refine ⟨320539785088633356616637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3419091040945422470577461 320539785088633356616637)
                      ·
                        rfl

theorem cell23_624249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_624249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624249 prefixEnd_624249 := by exact prefixLift 624249
  have htrace : WordTrace (prefixWord ++ tailWord_624249) baseStart_624249 baseEnd_624249 := by
    simpa [prefixWord, tailWord_624249, baseEnd_624249] using wordTrace_append hprefix tailTrace_624249
  have hstable : (prefixWord ++ tailWord_624249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624249).length < 2 ^ (prefixWord ++ tailWord_624249).sum := by decide
  have hdescent : baseEnd_624249 < baseStart_624249 := by decide
  rcases family_descends (prefixWord ++ tailWord_624249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624263 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 3, 2, 2]
def baseStart_624263 : Nat := 118140960795 + 624263 * 2 ^ 59
def prefixEnd_624263 : Nat := 4983230072969 + 3 ^ 40 * 624263 * 2
def baseEnd_624263 : Nat := 320546973817796301841573

theorem tailTrace_624263 : CollatzResearch.WordTrace tailWord_624263 prefixEnd_624263 320546973817796301841573 := by
  unfold tailWord_624263
  simp only [CollatzResearch.WordTrace]
  refine ⟨22768742137409241477405443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15179161424939494318270295 22768742137409241477405443)
  ·
    refine ⟨34153113206113862216108165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22768742137409241477405443 34153113206113862216108165)
    ·
      refine ⟨6403708726146349165520281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34153113206113862216108165 6403708726146349165520281)
      ·
        refine ⟨4802781544609761874140211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6403708726146349165520281 4802781544609761874140211)
        ·
          refine ⟨7204172316914642811210317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4802781544609761874140211 7204172316914642811210317)
          ·
            refine ⟨2701564618842991054203869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7204172316914642811210317 2701564618842991054203869)
            ·
              refine ⟨1013086732066121645326451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2701564618842991054203869 1013086732066121645326451)
              ·
                refine ⟨1519630098099182467989677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013086732066121645326451 1519630098099182467989677)
                ·
                  refine ⟨569861286787193425496129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1519630098099182467989677 569861286787193425496129)
                  ·
                    refine ⟨427395965090395069122097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 569861286787193425496129 427395965090395069122097)
                    ·
                      refine ⟨320546973817796301841573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 427395965090395069122097 320546973817796301841573)
                      ·
                        rfl

theorem cell23_624263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_624263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624263 prefixEnd_624263 := by exact prefixLift 624263
  have htrace : WordTrace (prefixWord ++ tailWord_624263) baseStart_624263 baseEnd_624263 := by
    simpa [prefixWord, tailWord_624263, baseEnd_624263] using wordTrace_append hprefix tailTrace_624263
  have hstable : (prefixWord ++ tailWord_624263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624263).length < 2 ^ (prefixWord ++ tailWord_624263).sum := by decide
  have hdescent : baseEnd_624263 < baseStart_624263 := by decide
  rcases family_descends (prefixWord ++ tailWord_624263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624312 : List Nat := [2, 1, 2, 1, 2, 1, 1, 2, 3, 8]
def baseStart_624312 : Nat := 118140960795 + 624312 * 2 ^ 59
def prefixEnd_624312 : Nat := 4983230072969 + 3 ^ 40 * 624312 * 2
def baseEnd_624312 : Nat := 106857378123288870042949

theorem tailTrace_624312 : CollatzResearch.WordTrace tailWord_624312 prefixEnd_624312 106857378123288870042949 := by
  unfold tailWord_624312
  simp only [CollatzResearch.WordTrace]
  refine ⟨11385264657115861422969595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15180352876154481897292793 11385264657115861422969595)
  ·
    refine ⟨17077896985673792134454393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11385264657115861422969595 17077896985673792134454393)
    ·
      refine ⟨12808422739255344100840795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17077896985673792134454393 12808422739255344100840795)
      ·
        refine ⟨19212634108883016151261193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12808422739255344100840795 19212634108883016151261193)
        ·
          refine ⟨14409475581662262113445895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19212634108883016151261193 14409475581662262113445895)
          ·
            refine ⟨21614213372493393170168843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14409475581662262113445895 21614213372493393170168843)
            ·
              refine ⟨32421320058740089755253265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21614213372493393170168843 32421320058740089755253265)
              ·
                refine ⟨24315990044055067316439949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32421320058740089755253265 24315990044055067316439949)
                ·
                  refine ⟨9118496266520650243664981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24315990044055067316439949 9118496266520650243664981)
                  ·
                    refine ⟨106857378123288870042949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9118496266520650243664981 106857378123288870042949)
                    ·
                      rfl

theorem cell23_624312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 2, 3, 8].length) (baseStart_624312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624312 prefixEnd_624312 := by exact prefixLift 624312
  have htrace : WordTrace (prefixWord ++ tailWord_624312) baseStart_624312 baseEnd_624312 := by
    simpa [prefixWord, tailWord_624312, baseEnd_624312] using wordTrace_append hprefix tailTrace_624312
  have hstable : (prefixWord ++ tailWord_624312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624312).length < 2 ^ (prefixWord ++ tailWord_624312).sum := by decide
  have hdescent : baseEnd_624312 < baseStart_624312 := by decide
  rcases family_descends (prefixWord ++ tailWord_624312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624396 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 2, 5, 2]
def baseStart_624396 : Nat := 118140960795 + 624396 * 2 ^ 59
def prefixEnd_624396 : Nat := 4983230072969 + 3 ^ 40 * 624396 * 2
def baseEnd_624396 : Nat := 320615266744844281478461

theorem tailTrace_624396 : CollatzResearch.WordTrace tailWord_624396 prefixEnd_624396 320615266744844281478461 := by
  unfold tailWord_624396
  simp only [CollatzResearch.WordTrace]
  refine ⟨11386796522963702595998521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15182395363951603461331361 11386796522963702595998521)
  ·
    refine ⟨8540097392222776946998891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11386796522963702595998521 8540097392222776946998891)
    ·
      refine ⟨12810146088334165420498337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8540097392222776946998891 12810146088334165420498337)
      ·
        refine ⟨9607609566250624065373753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12810146088334165420498337 9607609566250624065373753)
        ·
          refine ⟨7205707174687968049030315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9607609566250624065373753 7205707174687968049030315)
          ·
            refine ⟨10808560762031952073545473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7205707174687968049030315 10808560762031952073545473)
            ·
              refine ⟨8106420571523964055159105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10808560762031952073545473 8106420571523964055159105)
              ·
                refine ⟨6079815428642973041369329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8106420571523964055159105 6079815428642973041369329)
                ·
                  refine ⟨4559861571482229781026997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6079815428642973041369329 4559861571482229781026997)
                  ·
                    refine ⟨427487022326459041971281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4559861571482229781026997 427487022326459041971281)
                    ·
                      refine ⟨320615266744844281478461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 427487022326459041971281 320615266744844281478461)
                      ·
                        rfl

theorem cell23_624396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 2, 5, 2].length) (baseStart_624396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624396 prefixEnd_624396 := by exact prefixLift 624396
  have htrace : WordTrace (prefixWord ++ tailWord_624396) baseStart_624396 baseEnd_624396 := by
    simpa [prefixWord, tailWord_624396, baseEnd_624396] using wordTrace_append hprefix tailTrace_624396
  have hstable : (prefixWord ++ tailWord_624396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624396).length < 2 ^ (prefixWord ++ tailWord_624396).sum := by decide
  have hdescent : baseEnd_624396 < baseStart_624396 := by decide
  rcases family_descends (prefixWord ++ tailWord_624396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624439 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 4]
def baseStart_624439 : Nat := 118140960795 + 624439 * 2 ^ 59
def prefixEnd_624439 : Nat := 4983230072969 + 3 ^ 40 * 624439 * 2
def baseEnd_624439 : Nat := 320637346412987613240763

theorem tailTrace_624439 : CollatzResearch.WordTrace tailWord_624439 prefixEnd_624439 320637346412987613240763 := by
  unfold tailWord_624439
  simp only [CollatzResearch.WordTrace]
  refine ⟨22775161384771623535812371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15183440923181082357208247 22775161384771623535812371)
  ·
    refine ⟨34162742077157435303718557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22775161384771623535812371 34162742077157435303718557)
    ·
      refine ⟨12811028278934038238894459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34162742077157435303718557 12811028278934038238894459)
      ·
        refine ⟨19216542418401057358341689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12811028278934038238894459 19216542418401057358341689)
        ·
          refine ⟨14412406813800793018756267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19216542418401057358341689 14412406813800793018756267)
          ·
            refine ⟨21618610220701189528134401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14412406813800793018756267 21618610220701189528134401)
            ·
              refine ⟨16213957665525892146100801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21618610220701189528134401 16213957665525892146100801)
              ·
                refine ⟨12160468249144419109575601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16213957665525892146100801 12160468249144419109575601)
                ·
                  refine ⟨9120351186858314332181701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12160468249144419109575601 9120351186858314332181701)
                  ·
                    refine ⟨1710065847535933937284069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9120351186858314332181701 1710065847535933937284069)
                    ·
                      refine ⟨320637346412987613240763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1710065847535933937284069 320637346412987613240763)
                      ·
                        rfl

theorem cell23_624439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 2, 4, 4].length) (baseStart_624439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624439 prefixEnd_624439 := by exact prefixLift 624439
  have htrace : WordTrace (prefixWord ++ tailWord_624439) baseStart_624439 baseEnd_624439 := by
    simpa [prefixWord, tailWord_624439, baseEnd_624439] using wordTrace_append hprefix tailTrace_624439
  have hstable : (prefixWord ++ tailWord_624439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624439).length < 2 ^ (prefixWord ++ tailWord_624439).sum := by decide
  have hdescent : baseEnd_624439 < baseStart_624439 := by decide
  rcases family_descends (prefixWord ++ tailWord_624439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624483 : List Nat := [1, 1, 1, 5, 4, 1, 2, 2, 6]
def baseStart_624483 : Nat := 118140960795 + 624483 * 2 ^ 59
def prefixEnd_624483 : Nat := 4983230072969 + 3 ^ 40 * 624483 * 2
def baseEnd_624483 : Nat := 35628882173531715676729

theorem tailTrace_624483 : CollatzResearch.WordTrace tailWord_624483 prefixEnd_624483 35628882173531715676729 := by
  unfold tailWord_624483
  simp only [CollatzResearch.WordTrace]
  refine ⟨22776766196612219050414103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15184510797741479366942735 22776766196612219050414103)
  ·
    refine ⟨34165149294918328575621155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22776766196612219050414103 34165149294918328575621155)
    ·
      refine ⟨51247723942377492863431733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34165149294918328575621155 51247723942377492863431733)
      ·
        refine ⟨4804474119597889955946725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51247723942377492863431733 4804474119597889955946725)
        ·
          refine ⟨900838897424604366740011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4804474119597889955946725 900838897424604366740011)
          ·
            refine ⟨1351258346136906550110017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900838897424604366740011 1351258346136906550110017)
            ·
              refine ⟨1013443759602679912582513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351258346136906550110017 1013443759602679912582513)
              ·
                refine ⟨760082819702009934436885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013443759602679912582513 760082819702009934436885)
                ·
                  refine ⟨35628882173531715676729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 760082819702009934436885 35628882173531715676729)
                  ·
                    rfl

theorem cell23_624483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 6].length) (baseStart_624483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624483 prefixEnd_624483 := by exact prefixLift 624483
  have htrace : WordTrace (prefixWord ++ tailWord_624483) baseStart_624483 baseEnd_624483 := by
    simpa [prefixWord, tailWord_624483, baseEnd_624483] using wordTrace_append hprefix tailTrace_624483
  have hstable : (prefixWord ++ tailWord_624483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624483).length < 2 ^ (prefixWord ++ tailWord_624483).sum := by decide
  have hdescent : baseEnd_624483 < baseStart_624483 := by decide
  rcases family_descends (prefixWord ++ tailWord_624483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624489 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 2, 4, 5]
def baseStart_624489 : Nat := 118140960795 + 624489 * 2 ^ 59
def prefixEnd_624489 : Nat := 4983230072969 + 3 ^ 40 * 624489 * 2
def baseEnd_624489 : Nat := 320663020445712417615533

theorem tailTrace_624489 : CollatzResearch.WordTrace tailWord_624489 prefixEnd_624489 320663020445712417615533 := by
  unfold tailWord_624489
  simp only [CollatzResearch.WordTrace]
  refine ⟨22776985034590482075132521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15184656689726988050088347 22776985034590482075132521)
  ·
    refine ⟨17082738775942861556349391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22776985034590482075132521 17082738775942861556349391)
    ·
      refine ⟨25624108163914292334524087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17082738775942861556349391 25624108163914292334524087)
      ·
        refine ⟨38436162245871438501786131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25624108163914292334524087 38436162245871438501786131)
        ·
          refine ⟨57654243368807157752679197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38436162245871438501786131 57654243368807157752679197)
          ·
            refine ⟨21620341263302684157254699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57654243368807157752679197 21620341263302684157254699)
            ·
              refine ⟨32430511894954026235882049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21620341263302684157254699 32430511894954026235882049)
              ·
                refine ⟨24322883921215519676911537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32430511894954026235882049 24322883921215519676911537)
                ·
                  refine ⟨18242162940911639757683653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24322883921215519676911537 18242162940911639757683653)
                  ·
                    refine ⟨3420405551420932454565685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18242162940911639757683653 3420405551420932454565685)
                    ·
                      refine ⟨320663020445712417615533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3420405551420932454565685 320663020445712417615533)
                      ·
                        rfl

theorem cell23_624489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 4, 5].length) (baseStart_624489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624489 prefixEnd_624489 := by exact prefixLift 624489
  have htrace : WordTrace (prefixWord ++ tailWord_624489) baseStart_624489 baseEnd_624489 := by
    simpa [prefixWord, tailWord_624489, baseEnd_624489] using wordTrace_append hprefix tailTrace_624489
  have hstable : (prefixWord ++ tailWord_624489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624489).length < 2 ^ (prefixWord ++ tailWord_624489).sum := by decide
  have hdescent : baseEnd_624489 < baseStart_624489 := by decide
  rcases family_descends (prefixWord ++ tailWord_624489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624520 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 1, 5, 2]
def baseStart_624520 : Nat := 118140960795 + 624520 * 2 ^ 59
def prefixEnd_624520 : Nat := 4983230072969 + 3 ^ 40 * 624520 * 2
def baseEnd_624520 : Nat := 320678938346001796327891

theorem tailTrace_624520 : CollatzResearch.WordTrace tailWord_624520 prefixEnd_624520 320678938346001796327891 := by
  unfold tailWord_624520
  simp only [CollatzResearch.WordTrace]
  refine ⟨11389057848739087184755507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15185410464985449579674009 11389057848739087184755507)
  ·
    refine ⟨17083586773108630777133261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11389057848739087184755507 17083586773108630777133261)
    ·
      refine ⟨6406345039915736541424973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17083586773108630777133261 6406345039915736541424973)
      ·
        refine ⟨2402379389968401203034365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6406345039915736541424973 2402379389968401203034365)
        ·
          refine ⟨900892271238150451137887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2402379389968401203034365 900892271238150451137887)
          ·
            refine ⟨1351338406857225676706831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900892271238150451137887 1351338406857225676706831)
            ·
              refine ⟨2027007610285838515060247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351338406857225676706831 2027007610285838515060247)
              ·
                refine ⟨3040511415428757772590371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2027007610285838515060247 3040511415428757772590371)
                ·
                  refine ⟨4560767123143136658885557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040511415428757772590371 4560767123143136658885557)
                  ·
                    refine ⟨427571917794669061770521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4560767123143136658885557 427571917794669061770521)
                    ·
                      refine ⟨320678938346001796327891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 427571917794669061770521 320678938346001796327891)
                      ·
                        rfl

theorem cell23_624520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_624520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624520 prefixEnd_624520 := by exact prefixLift 624520
  have htrace : WordTrace (prefixWord ++ tailWord_624520) baseStart_624520 baseEnd_624520 := by
    simpa [prefixWord, tailWord_624520, baseEnd_624520] using wordTrace_append hprefix tailTrace_624520
  have hstable : (prefixWord ++ tailWord_624520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624520).length < 2 ^ (prefixWord ++ tailWord_624520).sum := by decide
  have hdescent : baseEnd_624520 < baseStart_624520 := by decide
  rcases family_descends (prefixWord ++ tailWord_624520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624530 : List Nat := [3, 2, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_624530 : Nat := 118140960795 + 624530 * 2 ^ 59
def prefixEnd_624530 : Nat := 4983230072969 + 3 ^ 40 * 624530 * 2
def baseEnd_624530 : Nat := 106894691050848919067615

theorem tailTrace_624530 : CollatzResearch.WordTrace tailWord_624530 prefixEnd_624530 106894691050848919067615 := by
  unfold tailWord_624530
  simp only [CollatzResearch.WordTrace]
  refine ⟨5694620106860486519343761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15185653618294630718250029 5694620106860486519343761)
  ·
    refine ⟨4270965080145364889507821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5694620106860486519343761 4270965080145364889507821)
    ·
      refine ⟨1601611905054511833565433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4270965080145364889507821 1601611905054511833565433)
      ·
        refine ⟨1201208928790883875174075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1601611905054511833565433 1201208928790883875174075)
        ·
          refine ⟨1801813393186325812761113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1201208928790883875174075 1801813393186325812761113)
          ·
            refine ⟨1351360044889744359570835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1801813393186325812761113 1351360044889744359570835)
            ·
              refine ⟨2027040067334616539356253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351360044889744359570835 2027040067334616539356253)
              ·
                refine ⟨760140025250481202258595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2027040067334616539356253 760140025250481202258595)
                ·
                  refine ⟨1140210037875721803387893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760140025250481202258595 1140210037875721803387893)
                  ·
                    refine ⟨106894691050848919067615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1140210037875721803387893 106894691050848919067615)
                    ·
                      rfl

theorem cell23_624530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_624530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624530 prefixEnd_624530 := by exact prefixLift 624530
  have htrace : WordTrace (prefixWord ++ tailWord_624530) baseStart_624530 baseEnd_624530 := by
    simpa [prefixWord, tailWord_624530, baseEnd_624530] using wordTrace_append hprefix tailTrace_624530
  have hstable : (prefixWord ++ tailWord_624530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624530).length < 2 ^ (prefixWord ++ tailWord_624530).sum := by decide
  have hdescent : baseEnd_624530 < baseStart_624530 := by decide
  rcases family_descends (prefixWord ++ tailWord_624530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624533 : List Nat := [1, 3, 2, 1, 1, 3, 3, 3, 1, 1, 4]
def baseStart_624533 : Nat := 118140960795 + 624533 * 2 ^ 59
def prefixEnd_624533 : Nat := 4983230072969 + 3 ^ 40 * 624533 * 2
def baseEnd_624533 : Nat := 320685613594510245465331

theorem tailTrace_624533 : CollatzResearch.WordTrace tailWord_624533 prefixEnd_624533 320685613594510245465331 := by
  unfold tailWord_624533
  simp only [CollatzResearch.WordTrace]
  refine ⟨22778589846431077589734253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15185726564287385059822835 22778589846431077589734253)
  ·
    refine ⟨8541971192411654096150345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22778589846431077589734253 8541971192411654096150345)
    ·
      refine ⟨6406478394308740572112759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8541971192411654096150345 6406478394308740572112759)
      ·
        refine ⟨9609717591463110858169139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6406478394308740572112759 9609717591463110858169139)
        ·
          refine ⟨14414576387194666287253709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9609717591463110858169139 14414576387194666287253709)
          ·
            refine ⟨5405466145197999857720141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14414576387194666287253709 5405466145197999857720141)
            ·
              refine ⟨2027049804449249946645053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5405466145197999857720141 2027049804449249946645053)
              ·
                refine ⟨760143676668468729991895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2027049804449249946645053 760143676668468729991895)
                ·
                  refine ⟨1140215515002703094987843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760143676668468729991895 1140215515002703094987843)
                  ·
                    refine ⟨1710323272504054642481765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1140215515002703094987843 1710323272504054642481765)
                    ·
                      refine ⟨320685613594510245465331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1710323272504054642481765 320685613594510245465331)
                      ·
                        rfl

theorem cell23_624533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_624533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624533 prefixEnd_624533 := by exact prefixLift 624533
  have htrace : WordTrace (prefixWord ++ tailWord_624533) baseStart_624533 baseEnd_624533 := by
    simpa [prefixWord, tailWord_624533, baseEnd_624533] using wordTrace_append hprefix tailTrace_624533
  have hstable : (prefixWord ++ tailWord_624533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624533).length < 2 ^ (prefixWord ++ tailWord_624533).sum := by decide
  have hdescent : baseEnd_624533 < baseStart_624533 := by decide
  rcases family_descends (prefixWord ++ tailWord_624533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624534 : List Nat := [5, 3, 1, 1, 2, 2, 1, 2, 6]
def baseStart_624534 : Nat := 118140960795 + 624534 * 2 ^ 59
def prefixEnd_624534 : Nat := 4983230072969 + 3 ^ 40 * 624534 * 2
def baseEnd_624534 : Nat := 35631791897240526839203

theorem tailTrace_624534 : CollatzResearch.WordTrace tailWord_624534 prefixEnd_624534 35631791897240526839203 := by
  unfold tailWord_624534
  simp only [CollatzResearch.WordTrace]
  refine ⟨1423664144964215922532541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15185750879618303173680437 1423664144964215922532541)
  ·
    refine ⟨533874054361580970949703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1423664144964215922532541 533874054361580970949703)
    ·
      refine ⟨800811081542371456424555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 533874054361580970949703 800811081542371456424555)
      ·
        refine ⟨1201216622313557184636833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800811081542371456424555 1201216622313557184636833)
        ·
          refine ⟨900912466735167888477625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1201216622313557184636833 900912466735167888477625)
          ·
            refine ⟨675684350051375916358219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 900912466735167888477625 675684350051375916358219)
            ·
              refine ⟨1013526525077063874537329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675684350051375916358219 1013526525077063874537329)
              ·
                refine ⟨760144893807797905902997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013526525077063874537329 760144893807797905902997)
                ·
                  refine ⟨35631791897240526839203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 760144893807797905902997 35631791897240526839203)
                  ·
                    rfl

theorem cell23_624534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_624534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624534 prefixEnd_624534 := by exact prefixLift 624534
  have htrace : WordTrace (prefixWord ++ tailWord_624534) baseStart_624534 baseEnd_624534 := by
    simpa [prefixWord, tailWord_624534, baseEnd_624534] using wordTrace_append hprefix tailTrace_624534
  have hstable : (prefixWord ++ tailWord_624534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624534).length < 2 ^ (prefixWord ++ tailWord_624534).sum := by decide
  have hdescent : baseEnd_624534 < baseStart_624534 := by decide
  rcases family_descends (prefixWord ++ tailWord_624534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624573 : List Nat := [1, 4, 1, 2, 3, 1, 4, 7]
def baseStart_624573 : Nat := 118140960795 + 624573 * 2 ^ 59
def prefixEnd_624573 : Nat := 4983230072969 + 3 ^ 40 * 624573 * 2
def baseEnd_624573 : Nat := 11878005660025558850561

theorem tailTrace_624573 : CollatzResearch.WordTrace tailWord_624573 prefixEnd_624573 11878005660025558850561 := by
  unfold tailWord_624573
  simp only [CollatzResearch.WordTrace]
  refine ⟨22780048766286164421190373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15186699177524109614126915 22780048766286164421190373)
  ·
    refine ⟨4271259143678655828973195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22780048766286164421190373 4271259143678655828973195)
    ·
      refine ⟨6406888715517983743459793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4271259143678655828973195 6406888715517983743459793)
      ·
        refine ⟨4805166536638487807594845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6406888715517983743459793 4805166536638487807594845)
        ·
          refine ⟨1801937451239432927848067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4805166536638487807594845 1801937451239432927848067)
          ·
            refine ⟨2702906176859149391772101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801937451239432927848067 2702906176859149391772101)
            ·
              refine ⟨506794908161090510957269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2702906176859149391772101 506794908161090510957269)
              ·
                refine ⟨11878005660025558850561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 506794908161090510957269 11878005660025558850561)
                ·
                  rfl

theorem cell23_624573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 7].length) (baseStart_624573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624573 prefixEnd_624573 := by exact prefixLift 624573
  have htrace : WordTrace (prefixWord ++ tailWord_624573) baseStart_624573 baseEnd_624573 := by
    simpa [prefixWord, tailWord_624573, baseEnd_624573] using wordTrace_append hprefix tailTrace_624573
  have hstable : (prefixWord ++ tailWord_624573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624573).length < 2 ^ (prefixWord ++ tailWord_624573).sum := by decide
  have hdescent : baseEnd_624573 < baseStart_624573 := by decide
  rcases family_descends (prefixWord ++ tailWord_624573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624584 : List Nat := [2, 1, 3, 1, 4, 1, 3, 3, 1, 2, 2]
def baseStart_624584 : Nat := 118140960795 + 624584 * 2 ^ 59
def prefixEnd_624584 : Nat := 4983230072969 + 3 ^ 40 * 624584 * 2
def baseEnd_624584 : Nat := 320711801107889545927597

theorem tailTrace_624584 : CollatzResearch.WordTrace tailWord_624584 prefixEnd_624584 320711801107889545927597 := by
  unfold tailWord_624584
  simp only [CollatzResearch.WordTrace]
  refine ⟨11390224984623156649920403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15186966646164208866560537 11390224984623156649920403)
  ·
    refine ⟨17085337476934734974880605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11390224984623156649920403 17085337476934734974880605)
    ·
      refine ⟨6407001553850525615580227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17085337476934734974880605 6407001553850525615580227)
      ·
        refine ⟨9610502330775788423370341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6407001553850525615580227 9610502330775788423370341)
        ·
          refine ⟨1801969187020460329381939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9610502330775788423370341 1801969187020460329381939)
          ·
            refine ⟨2702953780530690494072909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801969187020460329381939 2702953780530690494072909)
            ·
              refine ⟨1013607667699008935277341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2702953780530690494072909 1013607667699008935277341)
              ·
                refine ⟨380102875387128350729003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1013607667699008935277341 380102875387128350729003)
                ·
                  refine ⟨570154313080692526093505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380102875387128350729003 570154313080692526093505)
                  ·
                    refine ⟨427615734810519394570129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 570154313080692526093505 427615734810519394570129)
                    ·
                      refine ⟨320711801107889545927597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 427615734810519394570129 320711801107889545927597)
                      ·
                        rfl

theorem cell23_624584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 3, 1, 2, 2].length) (baseStart_624584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624584 prefixEnd_624584 := by exact prefixLift 624584
  have htrace : WordTrace (prefixWord ++ tailWord_624584) baseStart_624584 baseEnd_624584 := by
    simpa [prefixWord, tailWord_624584, baseEnd_624584] using wordTrace_append hprefix tailTrace_624584
  have hstable : (prefixWord ++ tailWord_624584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624584).length < 2 ^ (prefixWord ++ tailWord_624584).sum := by decide
  have hdescent : baseEnd_624584 < baseStart_624584 := by decide
  rcases family_descends (prefixWord ++ tailWord_624584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624600 : List Nat := [2, 1, 2, 2, 2, 2, 2, 4, 2, 1, 3]
def baseStart_624600 : Nat := 118140960795 + 624600 * 2 ^ 59
def prefixEnd_624600 : Nat := 4983230072969 + 3 ^ 40 * 624600 * 2
def baseEnd_624600 : Nat := 320720016798361483327523

theorem tailTrace_624600 : CollatzResearch.WordTrace tailWord_624600 prefixEnd_624600 320720016798361483327523 := by
  unfold tailWord_624600
  simp only [CollatzResearch.WordTrace]
  refine ⟨11390516768594174016211627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15187355691458898688282169 11390516768594174016211627)
  ·
    refine ⟨17085775152891261024317441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11390516768594174016211627 17085775152891261024317441)
    ·
      refine ⟨12814331364668445768238081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17085775152891261024317441 12814331364668445768238081)
      ·
        refine ⟨9610748523501334326178561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12814331364668445768238081 9610748523501334326178561)
        ·
          refine ⟨7208061392626000744633921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9610748523501334326178561 7208061392626000744633921)
          ·
            refine ⟨5406046044469500558475441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7208061392626000744633921 5406046044469500558475441)
            ·
              refine ⟨4054534533352125418856581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5406046044469500558475441 4054534533352125418856581)
              ·
                refine ⟨760225225003523516035609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4054534533352125418856581 760225225003523516035609)
                ·
                  refine ⟨570168918752642637026707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 760225225003523516035609 570168918752642637026707)
                  ·
                    refine ⟨855253378128963955540061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 570168918752642637026707 855253378128963955540061)
                    ·
                      refine ⟨320720016798361483327523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 855253378128963955540061 320720016798361483327523)
                      ·
                        rfl

theorem cell23_624600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_624600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624600 prefixEnd_624600 := by exact prefixLift 624600
  have htrace : WordTrace (prefixWord ++ tailWord_624600) baseStart_624600 baseEnd_624600 := by
    simpa [prefixWord, tailWord_624600, baseEnd_624600] using wordTrace_append hprefix tailTrace_624600
  have hstable : (prefixWord ++ tailWord_624600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624600).length < 2 ^ (prefixWord ++ tailWord_624600).sum := by decide
  have hdescent : baseEnd_624600 < baseStart_624600 := by decide
  rcases family_descends (prefixWord ++ tailWord_624600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624601 : List Nat := [1, 2, 1, 2, 6, 1, 3, 2, 1, 2, 2]
def baseStart_624601 : Nat := 118140960795 + 624601 * 2 ^ 59
def prefixEnd_624601 : Nat := 4983230072969 + 3 ^ 40 * 624601 * 2
def baseEnd_624601 : Nat := 320720530279015979415019

theorem tailTrace_624601 : CollatzResearch.WordTrace tailWord_624601 prefixEnd_624601 320720530279015979415019 := by
  unfold tailWord_624601
  simp only [CollatzResearch.WordTrace]
  refine ⟨22781070010184725203209657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15187380006789816802139771 22781070010184725203209657)
  ·
    refine ⟨17085802507638543902407243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22781070010184725203209657 17085802507638543902407243)
    ·
      refine ⟨25628703761457815853610865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17085802507638543902407243 25628703761457815853610865)
      ·
        refine ⟨19221527821093361890208149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25628703761457815853610865 19221527821093361890208149)
        ·
          refine ⟨901009116613751338603507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19221527821093361890208149 901009116613751338603507)
          ·
            refine ⟨1351513674920627007905261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901009116613751338603507 1351513674920627007905261)
            ·
              refine ⟨506817628095235127964473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1351513674920627007905261 506817628095235127964473)
              ·
                refine ⟨380113221071426345973355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506817628095235127964473 380113221071426345973355)
                ·
                  refine ⟨570169831607139518960033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380113221071426345973355 570169831607139518960033)
                  ·
                    refine ⟨427627373705354639220025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 570169831607139518960033 427627373705354639220025)
                    ·
                      refine ⟨320720530279015979415019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 427627373705354639220025 320720530279015979415019)
                      ·
                        rfl

theorem cell23_624601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 2, 1, 2, 2].length) (baseStart_624601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624601 prefixEnd_624601 := by exact prefixLift 624601
  have htrace : WordTrace (prefixWord ++ tailWord_624601) baseStart_624601 baseEnd_624601 := by
    simpa [prefixWord, tailWord_624601, baseEnd_624601] using wordTrace_append hprefix tailTrace_624601
  have hstable : (prefixWord ++ tailWord_624601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624601).length < 2 ^ (prefixWord ++ tailWord_624601).sum := by decide
  have hdescent : baseEnd_624601 < baseStart_624601 := by decide
  rcases family_descends (prefixWord ++ tailWord_624601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624616 : List Nat := [2, 1, 4, 1, 1, 1, 1, 3, 1, 8]
def baseStart_624616 : Nat := 118140960795 + 624616 * 2 ^ 59
def prefixEnd_624616 : Nat := 4983230072969 + 3 ^ 40 * 624616 * 2
def baseEnd_624616 : Nat := 106909410829611140242483

theorem tailTrace_624616 : CollatzResearch.WordTrace tailWord_624616 prefixEnd_624616 106909410829611140242483 := by
  unfold tailWord_624616
  simp only [CollatzResearch.WordTrace]
  refine ⟨11390808552565191382502851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15187744736753588510003801 11390808552565191382502851)
  ·
    refine ⟨17086212828847787073754277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11390808552565191382502851 17086212828847787073754277)
    ·
      refine ⟨3203664905408960076328927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17086212828847787073754277 3203664905408960076328927)
      ·
        refine ⟨4805497358113440114493391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3203664905408960076328927 4805497358113440114493391)
        ·
          refine ⟨7208246037170160171740087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4805497358113440114493391 7208246037170160171740087)
          ·
            refine ⟨10812369055755240257610131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7208246037170160171740087 10812369055755240257610131)
            ·
              refine ⟨16218553583632860386415197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10812369055755240257610131 16218553583632860386415197)
              ·
                refine ⟨6081957593862322644905699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16218553583632860386415197 6081957593862322644905699)
                ·
                  refine ⟨9122936390793483967358549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6081957593862322644905699 9122936390793483967358549)
                  ·
                    refine ⟨106909410829611140242483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9122936390793483967358549 106909410829611140242483)
                    ·
                      rfl

theorem cell23_624616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_624616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624616 prefixEnd_624616 := by exact prefixLift 624616
  have htrace : WordTrace (prefixWord ++ tailWord_624616) baseStart_624616 baseEnd_624616 := by
    simpa [prefixWord, tailWord_624616, baseEnd_624616] using wordTrace_append hprefix tailTrace_624616
  have hstable : (prefixWord ++ tailWord_624616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624616).length < 2 ^ (prefixWord ++ tailWord_624616).sum := by decide
  have hdescent : baseEnd_624616 < baseStart_624616 := by decide
  rcases family_descends (prefixWord ++ tailWord_624616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624621 : List Nat := [1, 5, 1, 4, 2, 1, 1, 2, 1, 2, 3]
def baseStart_624621 : Nat := 118140960795 + 624621 * 2 ^ 59
def prefixEnd_624621 : Nat := 4983230072969 + 3 ^ 40 * 624621 * 2
def baseEnd_624621 : Nat := 320730799892105901164927

theorem tailTrace_624621 : CollatzResearch.WordTrace tailWord_624621 prefixEnd_624621 320730799892105901164927 := by
  unfold tailWord_624621
  simp only [CollatzResearch.WordTrace]
  refine ⟨22781799470112268618937717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15187866313408179079291811 22781799470112268618937717)
  ·
    refine ⟨2135793700323025183025411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22781799470112268618937717 2135793700323025183025411)
    ·
      refine ⟨3203690550484537774538117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2135793700323025183025411 3203690550484537774538117)
      ·
        refine ⟨600691978215850832725897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3203690550484537774538117 600691978215850832725897)
        ·
          refine ⟨450518983661888124544423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600691978215850832725897 450518983661888124544423)
          ·
            refine ⟨675778475492832186816635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450518983661888124544423 675778475492832186816635)
            ·
              refine ⟨1013667713239248280224953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675778475492832186816635 1013667713239248280224953)
              ·
                refine ⟨760250784929436210168715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013667713239248280224953 760250784929436210168715)
                ·
                  refine ⟨1140376177394154315253073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760250784929436210168715 1140376177394154315253073)
                  ·
                    refine ⟨855282133045615736439805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1140376177394154315253073 855282133045615736439805)
                    ·
                      refine ⟨320730799892105901164927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 855282133045615736439805 320730799892105901164927)
                      ·
                        rfl

theorem cell23_624621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_624621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624621 prefixEnd_624621 := by exact prefixLift 624621
  have htrace : WordTrace (prefixWord ++ tailWord_624621) baseStart_624621 baseEnd_624621 := by
    simpa [prefixWord, tailWord_624621, baseEnd_624621] using wordTrace_append hprefix tailTrace_624621
  have hstable : (prefixWord ++ tailWord_624621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624621).length < 2 ^ (prefixWord ++ tailWord_624621).sum := by decide
  have hdescent : baseEnd_624621 < baseStart_624621 := by decide
  rcases family_descends (prefixWord ++ tailWord_624621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624640 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 4, 2, 2]
def baseStart_624640 : Nat := 118140960795 + 624640 * 2 ^ 59
def prefixEnd_624640 : Nat := 4983230072969 + 3 ^ 40 * 624640 * 2
def baseEnd_624640 : Nat := 320740556024541326827339

theorem tailTrace_624640 : CollatzResearch.WordTrace tailWord_624640 prefixEnd_624640 320740556024541326827339 := by
  unfold tailWord_624640
  simp only [CollatzResearch.WordTrace]
  refine ⟨11391246228521717431939687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15188328304695623242586249 11391246228521717431939687)
  ·
    refine ⟨17086869342782576147909531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11391246228521717431939687 17086869342782576147909531)
    ·
      refine ⟨25630304014173864221864297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17086869342782576147909531 25630304014173864221864297)
      ·
        refine ⟨19222728010630398166398223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25630304014173864221864297 19222728010630398166398223)
        ·
          refine ⟨28834092015945597249597335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19222728010630398166398223 28834092015945597249597335)
          ·
            refine ⟨43251138023918395874396003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28834092015945597249597335 43251138023918395874396003)
            ·
              refine ⟨64876707035877593811594005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43251138023918395874396003 64876707035877593811594005)
              ·
                refine ⟨3041095642306762209918469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64876707035877593811594005 3041095642306762209918469)
                ·
                  refine ⟨570205432932517914359713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3041095642306762209918469 570205432932517914359713)
                  ·
                    refine ⟨427654074699388435769785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 570205432932517914359713 427654074699388435769785)
                    ·
                      refine ⟨320740556024541326827339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 427654074699388435769785 320740556024541326827339)
                      ·
                        rfl

theorem cell23_624640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 4, 2, 2].length) (baseStart_624640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624640 prefixEnd_624640 := by exact prefixLift 624640
  have htrace : WordTrace (prefixWord ++ tailWord_624640) baseStart_624640 baseEnd_624640 := by
    simpa [prefixWord, tailWord_624640, baseEnd_624640] using wordTrace_append hprefix tailTrace_624640
  have hstable : (prefixWord ++ tailWord_624640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624640).length < 2 ^ (prefixWord ++ tailWord_624640).sum := by decide
  have hdescent : baseEnd_624640 < baseStart_624640 := by decide
  rcases family_descends (prefixWord ++ tailWord_624640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624697 : List Nat := [1, 2, 1, 5, 3, 1, 2, 3, 5]
def baseStart_624697 : Nat := 118140960795 + 624697 * 2 ^ 59
def prefixEnd_624697 : Nat := 4983230072969 + 3 ^ 40 * 624697 * 2
def baseEnd_624697 : Nat := 35641091602427511534953

theorem tailTrace_624697 : CollatzResearch.WordTrace tailWord_624697 prefixEnd_624697 35641091602427511534953 := by
  unfold tailWord_624697
  simp only [CollatzResearch.WordTrace]
  refine ⟨22784571417836933598704345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15189714278557955732469563 22784571417836933598704345)
  ·
    refine ⟨17088428563377700199028259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22784571417836933598704345 17088428563377700199028259)
    ·
      refine ⟨25632642845066550298542389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17088428563377700199028259 25632642845066550298542389)
      ·
        refine ⟨2403060266724989090488349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25632642845066550298542389 2403060266724989090488349)
        ·
          refine ⟨901147600021870908933131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2403060266724989090488349 901147600021870908933131)
          ·
            refine ⟨1351721400032806363399697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901147600021870908933131 1351721400032806363399697)
            ·
              refine ⟨1013791050024604772549773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351721400032806363399697 1013791050024604772549773)
              ·
                refine ⟨380171643759226789706165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1013791050024604772549773 380171643759226789706165)
                ·
                  refine ⟨35641091602427511534953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 380171643759226789706165 35641091602427511534953)
                  ·
                    rfl

theorem cell23_624697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 5].length) (baseStart_624697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624697 prefixEnd_624697 := by exact prefixLift 624697
  have htrace : WordTrace (prefixWord ++ tailWord_624697) baseStart_624697 baseEnd_624697 := by
    simpa [prefixWord, tailWord_624697, baseEnd_624697] using wordTrace_append hprefix tailTrace_624697
  have hstable : (prefixWord ++ tailWord_624697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624697).length < 2 ^ (prefixWord ++ tailWord_624697).sum := by decide
  have hdescent : baseEnd_624697 < baseStart_624697 := by decide
  rcases family_descends (prefixWord ++ tailWord_624697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624713 : List Nat := [1, 2, 1, 1, 2, 2, 4, 1, 4, 1, 4]
def baseStart_624713 : Nat := 118140960795 + 624713 * 2 ^ 59
def prefixEnd_624713 : Nat := 4983230072969 + 3 ^ 40 * 624713 * 2
def baseEnd_624713 : Nat := 320778040112319541214503

theorem tailTrace_624713 : CollatzResearch.WordTrace tailWord_624713 prefixEnd_624713 320778040112319541214503 := by
  unfold tailWord_624713
  simp only [CollatzResearch.WordTrace]
  refine ⟨22785154985778968331286793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15190103323852645554191195 22785154985778968331286793)
  ·
    refine ⟨17088866239334226248465095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22785154985778968331286793 17088866239334226248465095)
    ·
      refine ⟨25633299359001339372697643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17088866239334226248465095 25633299359001339372697643)
      ·
        refine ⟨38449949038502009059046465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25633299359001339372697643 38449949038502009059046465)
        ·
          refine ⟨28837461778876506794284849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38449949038502009059046465 28837461778876506794284849)
          ·
            refine ⟨21628096334157380095713637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28837461778876506794284849 21628096334157380095713637)
            ·
              refine ⟨4055268062654508767946307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21628096334157380095713637 4055268062654508767946307)
              ·
                refine ⟨6082902093981763151919461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4055268062654508767946307 6082902093981763151919461)
                ·
                  refine ⟨1140544142621580590984899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6082902093981763151919461 1140544142621580590984899)
                  ·
                    refine ⟨1710816213932370886477349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1140544142621580590984899 1710816213932370886477349)
                    ·
                      refine ⟨320778040112319541214503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1710816213932370886477349 320778040112319541214503)
                      ·
                        rfl

theorem cell23_624713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 4, 1, 4].length) (baseStart_624713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624713 prefixEnd_624713 := by exact prefixLift 624713
  have htrace : WordTrace (prefixWord ++ tailWord_624713) baseStart_624713 baseEnd_624713 := by
    simpa [prefixWord, tailWord_624713, baseEnd_624713] using wordTrace_append hprefix tailTrace_624713
  have hstable : (prefixWord ++ tailWord_624713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624713).length < 2 ^ (prefixWord ++ tailWord_624713).sum := by decide
  have hdescent : baseEnd_624713 < baseStart_624713 := by decide
  rcases family_descends (prefixWord ++ tailWord_624713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624730 : List Nat := [3, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2]
def baseStart_624730 : Nat := 118140960795 + 624730 * 2 ^ 59
def prefixEnd_624730 : Nat := 4983230072969 + 3 ^ 40 * 624730 * 2
def baseEnd_624730 : Nat := 320786769283445974701925

theorem tailTrace_624730 : CollatzResearch.WordTrace tailWord_624730 prefixEnd_624730 320786769283445974701925 := by
  unfold tailWord_624730
  simp only [CollatzResearch.WordTrace]
  refine ⟨5696443756679345058663911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15190516684478253489770429 5696443756679345058663911)
  ·
    refine ⟨8544665635019017587995867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5696443756679345058663911 8544665635019017587995867)
    ·
      refine ⟨12816998452528526381993801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8544665635019017587995867 12816998452528526381993801)
      ·
        refine ⟨9612748839396394786495351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12816998452528526381993801 9612748839396394786495351)
        ·
          refine ⟨14419123259094592179743027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9612748839396394786495351 14419123259094592179743027)
          ·
            refine ⟨21628684888641888269614541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14419123259094592179743027 21628684888641888269614541)
            ·
              refine ⟨8110756833240708101105453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21628684888641888269614541 8110756833240708101105453)
              ·
                refine ⟨3041533812465265537914545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8110756833240708101105453 3041533812465265537914545)
                ·
                  refine ⟨2281150359348949153435909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3041533812465265537914545 2281150359348949153435909)
                  ·
                    refine ⟨427715692377927966269233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2281150359348949153435909 427715692377927966269233)
                    ·
                      refine ⟨320786769283445974701925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 427715692377927966269233 320786769283445974701925)
                      ·
                        rfl

theorem cell23_624730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 3, 2, 4, 2].length) (baseStart_624730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624730 prefixEnd_624730 := by exact prefixLift 624730
  have htrace : WordTrace (prefixWord ++ tailWord_624730) baseStart_624730 baseEnd_624730 := by
    simpa [prefixWord, tailWord_624730, baseEnd_624730] using wordTrace_append hprefix tailTrace_624730
  have hstable : (prefixWord ++ tailWord_624730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624730).length < 2 ^ (prefixWord ++ tailWord_624730).sum := by decide
  have hdescent : baseEnd_624730 < baseStart_624730 := by decide
  rcases family_descends (prefixWord ++ tailWord_624730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624740 : List Nat := [2, 3, 1, 1, 2, 1, 4, 2, 3, 4]
def baseStart_624740 : Nat := 118140960795 + 624740 * 2 ^ 59
def prefixEnd_624740 : Nat := 4983230072969 + 3 ^ 40 * 624740 * 2
def baseEnd_624740 : Nat := 106930634696663645192293

theorem tailTrace_624740 : CollatzResearch.WordTrace tailWord_624740 prefixEnd_624740 106930634696663645192293 := by
  unfold tailWord_624740
  simp only [CollatzResearch.WordTrace]
  refine ⟨11393069878340575971259837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15190759837787434628346449 11393069878340575971259837)
  ·
    refine ⟨4272401204377715989222439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11393069878340575971259837 4272401204377715989222439)
    ·
      refine ⟨6408601806566573983833659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4272401204377715989222439 6408601806566573983833659)
      ·
        refine ⟨9612902709849860975750489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6408601806566573983833659 9612902709849860975750489)
        ·
          refine ⟨7209677032387395731812867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9612902709849860975750489 7209677032387395731812867)
          ·
            refine ⟨10814515548581093597719301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7209677032387395731812867 10814515548581093597719301)
            ·
              refine ⟨2027721665358955049572369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10814515548581093597719301 2027721665358955049572369)
              ·
                refine ⟨1520791249019216287179277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2027721665358955049572369 1520791249019216287179277)
                ·
                  refine ⟨570296718382206107692229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1520791249019216287179277 570296718382206107692229)
                  ·
                    refine ⟨106930634696663645192293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 570296718382206107692229 106930634696663645192293)
                    ·
                      rfl

theorem cell23_624740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 4, 2, 3, 4].length) (baseStart_624740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624740 prefixEnd_624740 := by exact prefixLift 624740
  have htrace : WordTrace (prefixWord ++ tailWord_624740) baseStart_624740 baseEnd_624740 := by
    simpa [prefixWord, tailWord_624740, baseEnd_624740] using wordTrace_append hprefix tailTrace_624740
  have hstable : (prefixWord ++ tailWord_624740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624740).length < 2 ^ (prefixWord ++ tailWord_624740).sum := by decide
  have hdescent : baseEnd_624740 < baseStart_624740 := by decide
  rcases family_descends (prefixWord ++ tailWord_624740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624743 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_624743 : Nat := 118140960795 + 624743 * 2 ^ 59
def prefixEnd_624743 : Nat := 4983230072969 + 3 ^ 40 * 624743 * 2
def baseEnd_624743 : Nat := 320793444531954423839365

theorem tailTrace_624743 : CollatzResearch.WordTrace tailWord_624743 prefixEnd_624743 320793444531954423839365 := by
  unfold tailWord_624743
  simp only [CollatzResearch.WordTrace]
  refine ⟨22786249175670283454878883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15190832783780188969919255 22786249175670283454878883)
  ·
    refine ⟨34179373763505425182318325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22786249175670283454878883 34179373763505425182318325)
    ·
      refine ⟨3204316290328633610842343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34179373763505425182318325 3204316290328633610842343)
      ·
        refine ⟨4806474435492950416263515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3204316290328633610842343 4806474435492950416263515)
        ·
          refine ⟨7209711653239425624395273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4806474435492950416263515 7209711653239425624395273)
          ·
            refine ⟨5407283739929569218296455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7209711653239425624395273 5407283739929569218296455)
            ·
              refine ⟨8110925609894353827444683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5407283739929569218296455 8110925609894353827444683)
              ·
                refine ⟨12166388414841530741167025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8110925609894353827444683 12166388414841530741167025)
                ·
                  refine ⟨9124791311131148055875269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12166388414841530741167025 9124791311131148055875269)
                  ·
                    refine ⟨1710898370837090260476613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9124791311131148055875269 1710898370837090260476613)
                    ·
                      refine ⟨320793444531954423839365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1710898370837090260476613 320793444531954423839365)
                      ·
                        rfl

theorem cell23_624743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_624743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624743 prefixEnd_624743 := by exact prefixLift 624743
  have htrace : WordTrace (prefixWord ++ tailWord_624743) baseStart_624743 baseEnd_624743 := by
    simpa [prefixWord, tailWord_624743, baseEnd_624743] using wordTrace_append hprefix tailTrace_624743
  have hstable : (prefixWord ++ tailWord_624743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624743).length < 2 ^ (prefixWord ++ tailWord_624743).sum := by decide
  have hdescent : baseEnd_624743 < baseStart_624743 := by decide
  rcases family_descends (prefixWord ++ tailWord_624743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624750 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3]
def baseStart_624750 : Nat := 118140960795 + 624750 * 2 ^ 59
def prefixEnd_624750 : Nat := 4983230072969 + 3 ^ 40 * 624750 * 2
def baseEnd_624750 : Nat := 320797038896535896451833

theorem tailTrace_624750 : CollatzResearch.WordTrace tailWord_624750 prefixEnd_624750 320797038896535896451833 := by
  unfold tailWord_624750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2848313060830615456297963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15191002991096615766922469 2848313060830615456297963)
  ·
    refine ⟨4272469591245923184446945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2848313060830615456297963 4272469591245923184446945)
    ·
      refine ⟨3204352193434442388335209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4272469591245923184446945 3204352193434442388335209)
      ·
        refine ⟨2403264145075831791251407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3204352193434442388335209 2403264145075831791251407)
        ·
          refine ⟨3604896217613747686877111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2403264145075831791251407 3604896217613747686877111)
          ·
            refine ⟨5407344326420621530315667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3604896217613747686877111 5407344326420621530315667)
            ·
              refine ⟨8111016489630932295473501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5407344326420621530315667 8111016489630932295473501)
              ·
                refine ⟨3041631183611599610802563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8111016489630932295473501 3041631183611599610802563)
                ·
                  refine ⟨4562446775417399416203845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3041631183611599610802563 4562446775417399416203845)
                  ·
                    refine ⟨855458770390762390538221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4562446775417399416203845 855458770390762390538221)
                    ·
                      refine ⟨320797038896535896451833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 855458770390762390538221 320797038896535896451833)
                      ·
                        rfl

theorem cell23_624750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_624750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624750 prefixEnd_624750 := by exact prefixLift 624750
  have htrace : WordTrace (prefixWord ++ tailWord_624750) baseStart_624750 baseEnd_624750 := by
    simpa [prefixWord, tailWord_624750, baseEnd_624750] using wordTrace_append hprefix tailTrace_624750
  have hstable : (prefixWord ++ tailWord_624750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624750).length < 2 ^ (prefixWord ++ tailWord_624750).sum := by decide
  have hdescent : baseEnd_624750 < baseStart_624750 := by decide
  rcases family_descends (prefixWord ++ tailWord_624750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624800 : List Nat := [2, 1, 1, 4, 2, 3, 1, 1, 3, 5]
def baseStart_624800 : Nat := 118140960795 + 624800 * 2 ^ 59
def prefixEnd_624800 : Nat := 4983230072969 + 3 ^ 40 * 624800 * 2
def baseEnd_624800 : Nat := 106940904309753566942201

theorem tailTrace_624800 : CollatzResearch.WordTrace tailWord_624800 prefixEnd_624800 106940904309753566942201 := by
  unfold tailWord_624800
  simp only [CollatzResearch.WordTrace]
  refine ⟨11394164068231891094851927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15192218757642521459802569 11394164068231891094851927)
  ·
    refine ⟨17091246102347836642277891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11394164068231891094851927 17091246102347836642277891)
    ·
      refine ⟨25636869153521754963416837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17091246102347836642277891 25636869153521754963416837)
      ·
        refine ⟨4806912966285329055640657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25636869153521754963416837 4806912966285329055640657)
        ·
          refine ⟨3605184724713996791730493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4806912966285329055640657 3605184724713996791730493)
          ·
            refine ⟨1351944271767748796898935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3605184724713996791730493 1351944271767748796898935)
            ·
              refine ⟨2027916407651623195348403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351944271767748796898935 2027916407651623195348403)
              ·
                refine ⟨3041874611477434793022605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2027916407651623195348403 3041874611477434793022605)
                ·
                  refine ⟨1140702979304038047383477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3041874611477434793022605 1140702979304038047383477)
                  ·
                    refine ⟨106940904309753566942201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1140702979304038047383477 106940904309753566942201)
                    ·
                      rfl

theorem cell23_624800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 3, 5].length) (baseStart_624800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624800 prefixEnd_624800 := by exact prefixLift 624800
  have htrace : WordTrace (prefixWord ++ tailWord_624800) baseStart_624800 baseEnd_624800 := by
    simpa [prefixWord, tailWord_624800, baseEnd_624800] using wordTrace_append hprefix tailTrace_624800
  have hstable : (prefixWord ++ tailWord_624800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624800).length < 2 ^ (prefixWord ++ tailWord_624800).sum := by decide
  have hdescent : baseEnd_624800 < baseStart_624800 := by decide
  rcases family_descends (prefixWord ++ tailWord_624800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624834 : List Nat := [3, 5, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_624834 : Nat := 118140960795 + 624834 * 2 ^ 59
def prefixEnd_624834 : Nat := 4983230072969 + 3 ^ 40 * 624834 * 2
def baseEnd_624834 : Nat := 106946723757171189267149

theorem tailTrace_624834 : CollatzResearch.WordTrace tailWord_624834 prefixEnd_624834 106946723757171189267149 := by
  unfold tailWord_624834
  simp only [CollatzResearch.WordTrace]
  refine ⟨5697392054585151499110389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15193045478893737330961037 5697392054585151499110389)
  ·
    refine ⟨534130505117357953041599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5697392054585151499110389 534130505117357953041599)
    ·
      refine ⟨801195757676036929562399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 534130505117357953041599 801195757676036929562399)
      ·
        refine ⟨1201793636514055394343599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801195757676036929562399 1201793636514055394343599)
        ·
          refine ⟨1802690454771083091515399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1201793636514055394343599 1802690454771083091515399)
          ·
            refine ⟨2704035682156624637273099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802690454771083091515399 2704035682156624637273099)
            ·
              refine ⟨4056053523234936955909649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2704035682156624637273099 4056053523234936955909649)
              ·
                refine ⟨3042040142426202716932237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4056053523234936955909649 3042040142426202716932237)
                ·
                  refine ⟨1140765053409826018849589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3042040142426202716932237 1140765053409826018849589)
                  ·
                    refine ⟨106946723757171189267149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1140765053409826018849589 106946723757171189267149)
                    ·
                      rfl

theorem cell23_624834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_624834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624834 prefixEnd_624834 := by exact prefixLift 624834
  have htrace : WordTrace (prefixWord ++ tailWord_624834) baseStart_624834 baseEnd_624834 := by
    simpa [prefixWord, tailWord_624834, baseEnd_624834] using wordTrace_append hprefix tailTrace_624834
  have hstable : (prefixWord ++ tailWord_624834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624834).length < 2 ^ (prefixWord ++ tailWord_624834).sum := by decide
  have hdescent : baseEnd_624834 < baseStart_624834 := by decide
  rcases family_descends (prefixWord ++ tailWord_624834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624854 : List Nat := [5, 2, 1, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_624854 : Nat := 118140960795 + 624854 * 2 ^ 59
def prefixEnd_624854 : Nat := 4983230072969 + 3 ^ 40 * 624854 * 2
def baseEnd_624854 : Nat := 320850440884603489551355

theorem tailTrace_624854 : CollatzResearch.WordTrace tailWord_624854 prefixEnd_624854 320850440884603489551355 := by
  unfold tailWord_624854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424393604891759338260601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15193531785512099608113077 1424393604891759338260601)
  ·
    refine ⟨1068295203668819503695451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1424393604891759338260601 1068295203668819503695451)
    ·
      refine ⟨1602442805503229255543177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1068295203668819503695451 1602442805503229255543177)
      ·
        refine ⟨1201832104127421941657383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1602442805503229255543177 1201832104127421941657383)
        ·
          refine ⟨1802748156191132912486075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1201832104127421941657383 1802748156191132912486075)
          ·
            refine ⟨2704122234286699368729113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802748156191132912486075 2704122234286699368729113)
            ·
              refine ⟨2028091675715024526546835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2704122234286699368729113 2028091675715024526546835)
              ·
                refine ⟨3042137513572536789820253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2028091675715024526546835 3042137513572536789820253)
                ·
                  refine ⟨1140801567589701296182595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3042137513572536789820253 1140801567589701296182595)
                  ·
                    refine ⟨1711202351384551944273893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1140801567589701296182595 1711202351384551944273893)
                    ·
                      refine ⟨320850440884603489551355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1711202351384551944273893 320850440884603489551355)
                      ·
                        rfl

theorem cell23_624854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_624854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624854 prefixEnd_624854 := by exact prefixLift 624854
  have htrace : WordTrace (prefixWord ++ tailWord_624854) baseStart_624854 baseEnd_624854 := by
    simpa [prefixWord, tailWord_624854, baseEnd_624854] using wordTrace_append hprefix tailTrace_624854
  have hstable : (prefixWord ++ tailWord_624854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624854).length < 2 ^ (prefixWord ++ tailWord_624854).sum := by decide
  have hdescent : baseEnd_624854 < baseStart_624854 := by decide
  rcases family_descends (prefixWord ++ tailWord_624854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624871 : List Nat := [1, 1, 5, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_624871 : Nat := 118140960795 + 624871 * 2 ^ 59
def prefixEnd_624871 : Nat := 4983230072969 + 3 ^ 40 * 624871 * 2
def baseEnd_624871 : Nat := 320859170055729923038777

theorem tailTrace_624871 : CollatzResearch.WordTrace tailWord_624871 prefixEnd_624871 320859170055729923038777 := by
  unfold tailWord_624871
  simp only [CollatzResearch.WordTrace]
  refine ⟨22790917719206561315538467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15193945146137707543692311 22790917719206561315538467)
  ·
    refine ⟨34186376578809841973307701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22790917719206561315538467 34186376578809841973307701)
    ·
      refine ⟨3204972804263422684997597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34186376578809841973307701 3204972804263422684997597)
      ·
        refine ⟨1201864801598783506874099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3204972804263422684997597 1201864801598783506874099)
        ·
          refine ⟨1802797202398175260311149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1201864801598783506874099 1802797202398175260311149)
          ·
            refine ⟨676048950899315722616681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1802797202398175260311149 676048950899315722616681)
            ·
              refine ⟨507036713174486791962511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 676048950899315722616681 507036713174486791962511)
              ·
                refine ⟨760555069761730187943767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507036713174486791962511 760555069761730187943767)
                ·
                  refine ⟨1140832604642595281915651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760555069761730187943767 1140832604642595281915651)
                  ·
                    refine ⟨1711248906963892922873477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1140832604642595281915651 1711248906963892922873477)
                    ·
                      refine ⟨320859170055729923038777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1711248906963892922873477 320859170055729923038777)
                      ·
                        rfl

theorem cell23_624871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_624871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624871 prefixEnd_624871 := by exact prefixLift 624871
  have htrace : WordTrace (prefixWord ++ tailWord_624871) baseStart_624871 baseEnd_624871 := by
    simpa [prefixWord, tailWord_624871, baseEnd_624871] using wordTrace_append hprefix tailTrace_624871
  have hstable : (prefixWord ++ tailWord_624871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624871).length < 2 ^ (prefixWord ++ tailWord_624871).sum := by decide
  have hdescent : baseEnd_624871 < baseStart_624871 := by decide
  rcases family_descends (prefixWord ++ tailWord_624871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624873 : List Nat := [1, 2, 1, 1, 1, 2, 2, 2, 4, 7]
def baseStart_624873 : Nat := 118140960795 + 624873 * 2 ^ 59
def prefixEnd_624873 : Nat := 4983230072969 + 3 ^ 40 * 624873 * 2
def baseEnd_624873 : Nat := 106953399005679638404589

theorem tailTrace_624873 : CollatzResearch.WordTrace tailWord_624873 prefixEnd_624873 106953399005679638404589 := by
  unfold tailWord_624873
  simp only [CollatzResearch.WordTrace]
  refine ⟨22790990665199315657111273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15193993776799543771407515 22790990665199315657111273)
  ·
    refine ⟨17093242998899486742833455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22790990665199315657111273 17093242998899486742833455)
    ·
      refine ⟨25639864498349230114250183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17093242998899486742833455 25639864498349230114250183)
      ·
        refine ⟨38459796747523845171375275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25639864498349230114250183 38459796747523845171375275)
        ·
          refine ⟨57689695121285767757062913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38459796747523845171375275 57689695121285767757062913)
          ·
            refine ⟨43267271340964325817797185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57689695121285767757062913 43267271340964325817797185)
            ·
              refine ⟨32450453505723244363347889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43267271340964325817797185 32450453505723244363347889)
              ·
                refine ⟨24337840129292433272510917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32450453505723244363347889 24337840129292433272510917)
                ·
                  refine ⟨4563345024242331238595797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24337840129292433272510917 4563345024242331238595797)
                  ·
                    refine ⟨106953399005679638404589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4563345024242331238595797 106953399005679638404589)
                    ·
                      rfl

theorem cell23_624873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 4, 7].length) (baseStart_624873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624873 prefixEnd_624873 := by exact prefixLift 624873
  have htrace : WordTrace (prefixWord ++ tailWord_624873) baseStart_624873 baseEnd_624873 := by
    simpa [prefixWord, tailWord_624873, baseEnd_624873] using wordTrace_append hprefix tailTrace_624873
  have hstable : (prefixWord ++ tailWord_624873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624873).length < 2 ^ (prefixWord ++ tailWord_624873).sum := by decide
  have hdescent : baseEnd_624873 < baseStart_624873 := by decide
  rcases family_descends (prefixWord ++ tailWord_624873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624904 : List Nat := [2, 1, 3, 2, 3, 3, 1, 1, 1, 3, 3]
def baseStart_624904 : Nat := 118140960795 + 624904 * 2 ^ 59
def prefixEnd_624904 : Nat := 4983230072969 + 3 ^ 40 * 624904 * 2
def baseEnd_624904 : Nat := 320876114917328293926125

theorem tailTrace_624904 : CollatzResearch.WordTrace tailWord_624904 prefixEnd_624904 320876114917328293926125 := by
  unfold tailWord_624904
  simp only [CollatzResearch.WordTrace]
  refine ⟨11396060664043503975744883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15194747552058005300993177 11396060664043503975744883)
  ·
    refine ⟨17094090996065255963617325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11396060664043503975744883 17094090996065255963617325)
    ·
      refine ⟨6410284123524470986356497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17094090996065255963617325 6410284123524470986356497)
      ·
        refine ⟨4807713092643353239767373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6410284123524470986356497 4807713092643353239767373)
        ·
          refine ⟨1802892409741257464912765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4807713092643353239767373 1802892409741257464912765)
          ·
            refine ⟨676084653652971549342287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1802892409741257464912765 676084653652971549342287)
            ·
              refine ⟨1014126980479457324013431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676084653652971549342287 1014126980479457324013431)
              ·
                refine ⟨1521190470719185986020147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014126980479457324013431 1521190470719185986020147)
                ·
                  refine ⟨2281785706078778979030221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521190470719185986020147 2281785706078778979030221)
                  ·
                    refine ⟨855669639779542117136333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2281785706078778979030221 855669639779542117136333)
                    ·
                      refine ⟨320876114917328293926125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 855669639779542117136333 320876114917328293926125)
                      ·
                        rfl

theorem cell23_624904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_624904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624904 prefixEnd_624904 := by exact prefixLift 624904
  have htrace : WordTrace (prefixWord ++ tailWord_624904) baseStart_624904 baseEnd_624904 := by
    simpa [prefixWord, tailWord_624904, baseEnd_624904] using wordTrace_append hprefix tailTrace_624904
  have hstable : (prefixWord ++ tailWord_624904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624904).length < 2 ^ (prefixWord ++ tailWord_624904).sum := by decide
  have hdescent : baseEnd_624904 < baseStart_624904 := by decide
  rcases family_descends (prefixWord ++ tailWord_624904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624940 : List Nat := [2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 4]
def baseStart_624940 : Nat := 118140960795 + 624940 * 2 ^ 59
def prefixEnd_624940 : Nat := 4983230072969 + 3 ^ 40 * 624940 * 2
def baseEnd_624940 : Nat := 320894600220890153075959

theorem tailTrace_624940 : CollatzResearch.WordTrace tailWord_624940 prefixEnd_624940 320894600220890153075959 := by
  unfold tailWord_624940
  simp only [CollatzResearch.WordTrace]
  refine ⟨11396717177978293049900137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15195622903971057399866849 11396717177978293049900137)
  ·
    refine ⟨8547537883483719787425103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11396717177978293049900137 8547537883483719787425103)
    ·
      refine ⟨12821306825225579681137655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8547537883483719787425103 12821306825225579681137655)
      ·
        refine ⟨19231960237838369521706483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12821306825225579681137655 19231960237838369521706483)
        ·
          refine ⟨28847940356757554282559725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19231960237838369521706483 28847940356757554282559725)
          ·
            refine ⟨10817977633784082855959897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28847940356757554282559725 10817977633784082855959897)
            ·
              refine ⟨8113483225338062141969923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10817977633784082855959897 8113483225338062141969923)
              ·
                refine ⟨12170224838007093212954885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8113483225338062141969923 12170224838007093212954885)
                ·
                  refine ⟨2281917157126329977429041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12170224838007093212954885 2281917157126329977429041)
                  ·
                    refine ⟨1711437867844747483071781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2281917157126329977429041 1711437867844747483071781)
                    ·
                      refine ⟨320894600220890153075959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1711437867844747483071781 320894600220890153075959)
                      ·
                        rfl

theorem cell23_624940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 4].length) (baseStart_624940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624940 prefixEnd_624940 := by exact prefixLift 624940
  have htrace : WordTrace (prefixWord ++ tailWord_624940) baseStart_624940 baseEnd_624940 := by
    simpa [prefixWord, tailWord_624940, baseEnd_624940] using wordTrace_append hprefix tailTrace_624940
  have hstable : (prefixWord ++ tailWord_624940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624940).length < 2 ^ (prefixWord ++ tailWord_624940).sum := by decide
  have hdescent : baseEnd_624940 < baseStart_624940 := by decide
  rcases family_descends (prefixWord ++ tailWord_624940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_624997 : List Nat := [1, 3, 1, 3, 1, 3, 2, 2, 2, 5]
def baseStart_624997 : Nat := 118140960795 + 624997 * 2 ^ 59
def prefixEnd_624997 : Nat := 4983230072969 + 3 ^ 40 * 624997 * 2
def baseEnd_624997 : Nat := 106974622872732143354399

theorem tailTrace_624997 : CollatzResearch.WordTrace tailWord_624997 prefixEnd_624997 106974622872732143354399 := by
  unfold tailWord_624997
  simp only [CollatzResearch.WordTrace]
  refine ⟨22795513316750084834625245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15197008877833389889750163 22795513316750084834625245)
  ·
    refine ⟨8548317493781281812984467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22795513316750084834625245 8548317493781281812984467)
    ·
      refine ⟨12822476240671922719476701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8548317493781281812984467 12822476240671922719476701)
      ·
        refine ⟨4808428590251971019803763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12822476240671922719476701 4808428590251971019803763)
        ·
          refine ⟨7212642885377956529705645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4808428590251971019803763 7212642885377956529705645)
          ·
            refine ⟨2704741082016733698639617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7212642885377956529705645 2704741082016733698639617)
            ·
              refine ⟨2028555811512550273979713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2704741082016733698639617 2028555811512550273979713)
              ·
                refine ⟨1521416858634412705484785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2028555811512550273979713 1521416858634412705484785)
                ·
                  refine ⟨1141062643975809529113589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1521416858634412705484785 1141062643975809529113589)
                  ·
                    refine ⟨106974622872732143354399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1141062643975809529113589 106974622872732143354399)
                    ·
                      rfl

theorem cell23_624997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 2, 2, 5].length) (baseStart_624997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_624997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_624997 prefixEnd_624997 := by exact prefixLift 624997
  have htrace : WordTrace (prefixWord ++ tailWord_624997) baseStart_624997 baseEnd_624997 := by
    simpa [prefixWord, tailWord_624997, baseEnd_624997] using wordTrace_append hprefix tailTrace_624997
  have hstable : (prefixWord ++ tailWord_624997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_624997).length < 2 ^ (prefixWord ++ tailWord_624997).sum := by decide
  have hdescent : baseEnd_624997 < baseStart_624997 := by decide
  rcases family_descends (prefixWord ++ tailWord_624997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625046 : List Nat := [5, 3, 1, 2, 2, 1, 1, 2, 2, 2, 2]
def baseStart_625046 : Nat := 118140960795 + 625046 * 2 ^ 59
def prefixEnd_625046 : Nat := 4983230072969 + 3 ^ 40 * 625046 * 2
def baseEnd_625046 : Nat := 320949029170266738350473

theorem tailTrace_625046 : CollatzResearch.WordTrace tailWord_625046 prefixEnd_625046 320949029170266738350473 := by
  unfold tailWord_625046
  simp only [CollatzResearch.WordTrace]
  refine ⟨1424831280848285387697437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15198200329048377468772661 1424831280848285387697437)
  ·
    refine ⟨534311730318107020386539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1424831280848285387697437 534311730318107020386539)
    ·
      refine ⟨801467595477160530579809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 534311730318107020386539 801467595477160530579809)
      ·
        refine ⟨601100696607870397934857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 801467595477160530579809 601100696607870397934857)
        ·
          refine ⟨450825522455902798451143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 601100696607870397934857 450825522455902798451143)
          ·
            refine ⟨676238283683854197676715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450825522455902798451143 676238283683854197676715)
            ·
              refine ⟨1014357425525781296515073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676238283683854197676715 1014357425525781296515073)
              ·
                refine ⟨760768069144335972386305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014357425525781296515073 760768069144335972386305)
                ·
                  refine ⟨570576051858251979289729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 760768069144335972386305 570576051858251979289729)
                  ·
                    refine ⟨427932038893688984467297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 570576051858251979289729 427932038893688984467297)
                    ·
                      refine ⟨320949029170266738350473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 427932038893688984467297 320949029170266738350473)
                      ·
                        rfl

theorem cell23_625046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_625046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625046 prefixEnd_625046 := by exact prefixLift 625046
  have htrace : WordTrace (prefixWord ++ tailWord_625046) baseStart_625046 baseEnd_625046 := by
    simpa [prefixWord, tailWord_625046, baseEnd_625046] using wordTrace_append hprefix tailTrace_625046
  have hstable : (prefixWord ++ tailWord_625046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625046).length < 2 ^ (prefixWord ++ tailWord_625046).sum := by decide
  have hdescent : baseEnd_625046 < baseStart_625046 := by decide
  rcases family_descends (prefixWord ++ tailWord_625046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625074 : List Nat := [3, 2, 1, 1, 1, 1, 7, 1, 6]
def baseStart_625074 : Nat := 118140960795 + 625074 * 2 ^ 59
def prefixEnd_625074 : Nat := 4983230072969 + 3 ^ 40 * 625074 * 2
def baseEnd_625074 : Nat := 35662600736510292088927

theorem tailTrace_625074 : CollatzResearch.WordTrace tailWord_625074 prefixEnd_625074 35662600736510292088927 := by
  unfold tailWord_625074
  simp only [CollatzResearch.WordTrace]
  refine ⟨5699580434367781746294569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15198881158314084656785517 5699580434367781746294569)
  ·
    refine ⟨4274685325775836309720927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5699580434367781746294569 4274685325775836309720927)
    ·
      refine ⟨6412027988663754464581391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4274685325775836309720927 6412027988663754464581391)
      ·
        refine ⟨9618041982995631696872087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6412027988663754464581391 9618041982995631696872087)
        ·
          refine ⟨14427062974493447545308131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9618041982995631696872087 14427062974493447545308131)
          ·
            refine ⟨21640594461740171317962197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14427062974493447545308131 21640594461740171317962197)
            ·
              refine ⟨507201432697035265264739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 21640594461740171317962197 507201432697035265264739)
              ·
                refine ⟨760802149045552897897109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507201432697035265264739 760802149045552897897109)
                ·
                  refine ⟨35662600736510292088927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 760802149045552897897109 35662600736510292088927)
                  ·
                    rfl

theorem cell23_625074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_625074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625074 prefixEnd_625074 := by exact prefixLift 625074
  have htrace : WordTrace (prefixWord ++ tailWord_625074) baseStart_625074 baseEnd_625074 := by
    simpa [prefixWord, tailWord_625074, baseEnd_625074] using wordTrace_append hprefix tailTrace_625074
  have hstable : (prefixWord ++ tailWord_625074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625074).length < 2 ^ (prefixWord ++ tailWord_625074).sum := by decide
  have hdescent : baseEnd_625074 < baseStart_625074 := by decide
  rcases family_descends (prefixWord ++ tailWord_625074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625137 : List Nat := [1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 6]
def baseStart_625137 : Nat := 118140960795 + 625137 * 2 ^ 59
def prefixEnd_625137 : Nat := 4983230072969 + 3 ^ 40 * 625137 * 2
def baseEnd_625137 : Nat := 320995755909825882312553

theorem tailTrace_625137 : CollatzResearch.WordTrace tailWord_625137 prefixEnd_625137 320995755909825882312553 := by
  unfold tailWord_625137
  simp only [CollatzResearch.WordTrace]
  refine ⟨22800619536242888744721665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15200413024161925829814443 22800619536242888744721665)
  ·
    refine ⟨17100464652182166558541249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22800619536242888744721665 17100464652182166558541249)
    ·
      refine ⟨12825348489136624918905937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17100464652182166558541249 12825348489136624918905937)
      ·
        refine ⟨9619011366852468689179453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12825348489136624918905937 9619011366852468689179453)
        ·
          refine ⟨3607129262569675758442295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9619011366852468689179453 3607129262569675758442295)
          ·
            refine ⟨5410693893854513637663443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3607129262569675758442295 5410693893854513637663443)
            ·
              refine ⟨8116040840781770456495165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5410693893854513637663443 8116040840781770456495165)
              ·
                refine ⟨3043515315293163921185687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8116040840781770456495165 3043515315293163921185687)
                ·
                  refine ⟨4565272972939745881778531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3043515315293163921185687 4565272972939745881778531)
                  ·
                    refine ⟨6847909459409618822667797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4565272972939745881778531 6847909459409618822667797)
                    ·
                      refine ⟨320995755909825882312553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6847909459409618822667797 320995755909825882312553)
                      ·
                        rfl

theorem cell23_625137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_625137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625137 prefixEnd_625137 := by exact prefixLift 625137
  have htrace : WordTrace (prefixWord ++ tailWord_625137) baseStart_625137 baseEnd_625137 := by
    simpa [prefixWord, tailWord_625137, baseEnd_625137] using wordTrace_append hprefix tailTrace_625137
  have hstable : (prefixWord ++ tailWord_625137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625137).length < 2 ^ (prefixWord ++ tailWord_625137).sum := by decide
  have hdescent : baseEnd_625137 < baseStart_625137 := by decide
  rcases family_descends (prefixWord ++ tailWord_625137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625138 : List Nat := [3, 2, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_625138 : Nat := 118140960795 + 625138 * 2 ^ 59
def prefixEnd_625138 : Nat := 4983230072969 + 3 ^ 40 * 625138 * 2
def baseEnd_625138 : Nat := 106998756463493459466683

theorem tailTrace_625138 : CollatzResearch.WordTrace tailWord_625138 prefixEnd_625138 106998756463493459466683 := by
  unfold tailWord_625138
  simp only [CollatzResearch.WordTrace]
  refine ⟨5700164002309816478877017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15200437339492843943672045 5700164002309816478877017)
  ·
    refine ⟨4275123001732362359157763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5700164002309816478877017 4275123001732362359157763)
    ·
      refine ⟨6412684502598543538736645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4275123001732362359157763 6412684502598543538736645)
      ·
        refine ⟨1202378344237226913513121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6412684502598543538736645 1202378344237226913513121)
        ·
          refine ⟨901783758177920185134841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1202378344237226913513121 901783758177920185134841)
          ·
            refine ⟨676337818633440138851131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 901783758177920185134841 676337818633440138851131)
            ·
              refine ⟨1014506727950160208276697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 676337818633440138851131 1014506727950160208276697)
              ·
                refine ⟨760880045962620156207523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014506727950160208276697 760880045962620156207523)
                ·
                  refine ⟨1141320068943930234311285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760880045962620156207523 1141320068943930234311285)
                  ·
                    refine ⟨106998756463493459466683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1141320068943930234311285 106998756463493459466683)
                    ·
                      rfl

theorem cell23_625138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_625138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625138 prefixEnd_625138 := by exact prefixLift 625138
  have htrace : WordTrace (prefixWord ++ tailWord_625138) baseStart_625138 baseEnd_625138 := by
    simpa [prefixWord, tailWord_625138, baseEnd_625138] using wordTrace_append hprefix tailTrace_625138
  have hstable : (prefixWord ++ tailWord_625138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625138).length < 2 ^ (prefixWord ++ tailWord_625138).sum := by decide
  have hdescent : baseEnd_625138 < baseStart_625138 := by decide
  rcases family_descends (prefixWord ++ tailWord_625138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625144 : List Nat := [2, 1, 2, 1, 1, 4, 3, 1, 3, 2, 3]
def baseStart_625144 : Nat := 118140960795 + 625144 * 2 ^ 59
def prefixEnd_625144 : Nat := 4983230072969 + 3 ^ 40 * 625144 * 2
def baseEnd_625144 : Nat := 320999350274407354925021

theorem tailTrace_625144 : CollatzResearch.WordTrace tailWord_625144 prefixEnd_625144 320999350274407354925021 := by
  unfold tailWord_625144
  simp only [CollatzResearch.WordTrace]
  refine ⟨11400437423608764470113243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15200583231478352626817657 11400437423608764470113243)
  ·
    refine ⟨17100656135413146705169865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11400437423608764470113243 17100656135413146705169865)
    ·
      refine ⟨12825492101559860028877399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17100656135413146705169865 12825492101559860028877399)
      ·
        refine ⟨19238238152339790043316099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12825492101559860028877399 19238238152339790043316099)
        ·
          refine ⟨28857357228509685064974149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19238238152339790043316099 28857357228509685064974149)
          ·
            refine ⟨5410754480345565949682653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28857357228509685064974149 5410754480345565949682653)
            ·
              refine ⟨2029032930129587231130995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5410754480345565949682653 2029032930129587231130995)
              ·
                refine ⟨3043549395194380846696493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029032930129587231130995 3043549395194380846696493)
                ·
                  refine ⟨1141331023197892817511185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3043549395194380846696493 1141331023197892817511185)
                  ·
                    refine ⟨855998267398419613133389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1141331023197892817511185 855998267398419613133389)
                    ·
                      refine ⟨320999350274407354925021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 855998267398419613133389 320999350274407354925021)
                      ·
                        rfl

theorem cell23_625144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 3, 2, 3].length) (baseStart_625144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625144 prefixEnd_625144 := by exact prefixLift 625144
  have htrace : WordTrace (prefixWord ++ tailWord_625144) baseStart_625144 baseEnd_625144 := by
    simpa [prefixWord, tailWord_625144, baseEnd_625144] using wordTrace_append hprefix tailTrace_625144
  have hstable : (prefixWord ++ tailWord_625144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625144).length < 2 ^ (prefixWord ++ tailWord_625144).sum := by decide
  have hdescent : baseEnd_625144 < baseStart_625144 := by decide
  rcases family_descends (prefixWord ++ tailWord_625144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625188 : List Nat := [2, 3, 1, 5, 1, 1, 2, 1, 1, 2, 4]
def baseStart_625188 : Nat := 118140960795 + 625188 * 2 ^ 59
def prefixEnd_625188 : Nat := 4983230072969 + 3 ^ 40 * 625188 * 2
def baseEnd_625188 : Nat := 321021943423205182774819

theorem tailTrace_625188 : CollatzResearch.WordTrace tailWord_625188 prefixEnd_625188 321021943423205182774819 := by
  unfold tailWord_625188
  simp only [CollatzResearch.WordTrace]
  refine ⟨11401239829529062227414109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15201653106038749636552145 11401239829529062227414109)
  ·
    refine ⟨4275464936073398335280291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11401239829529062227414109 4275464936073398335280291)
    ·
      refine ⟨6413197404110097502920437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4275464936073398335280291 6413197404110097502920437)
      ·
        refine ⟨601237256635321640898791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6413197404110097502920437 601237256635321640898791)
        ·
          refine ⟨901855884952982461348187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601237256635321640898791 901855884952982461348187)
          ·
            refine ⟨1352783827429473692022281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901855884952982461348187 1352783827429473692022281)
            ·
              refine ⟨1014587870572105269016711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1352783827429473692022281 1014587870572105269016711)
              ·
                refine ⟨1521881805858157903525067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014587870572105269016711 1521881805858157903525067)
                ·
                  refine ⟨2282822708787236855287601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521881805858157903525067 2282822708787236855287601)
                  ·
                    refine ⟨1712117031590427641465701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2282822708787236855287601 1712117031590427641465701)
                    ·
                      refine ⟨321021943423205182774819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1712117031590427641465701 321021943423205182774819)
                      ·
                        rfl

theorem cell23_625188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_625188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625188 prefixEnd_625188 := by exact prefixLift 625188
  have htrace : WordTrace (prefixWord ++ tailWord_625188) baseStart_625188 baseEnd_625188 := by
    simpa [prefixWord, tailWord_625188, baseEnd_625188] using wordTrace_append hprefix tailTrace_625188
  have hstable : (prefixWord ++ tailWord_625188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625188).length < 2 ^ (prefixWord ++ tailWord_625188).sum := by decide
  have hdescent : baseEnd_625188 < baseStart_625188 := by decide
  rcases family_descends (prefixWord ++ tailWord_625188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625201 : List Nat := [1, 2, 2, 3, 1, 1, 4, 1, 3, 3, 2]
def baseStart_625201 : Nat := 118140960795 + 625201 * 2 ^ 59
def prefixEnd_625201 : Nat := 4983230072969 + 3 ^ 40 * 625201 * 2
def baseEnd_625201 : Nat := 321028618671713631912259

theorem tailTrace_625201 : CollatzResearch.WordTrace tailWord_625201 prefixEnd_625201 321028618671713631912259 := by
  unfold tailWord_625201
  simp only [CollatzResearch.WordTrace]
  refine ⟨22802953808011027675051457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15201969205340685116700971 22802953808011027675051457)
  ·
    refine ⟨17102215356008270756288593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22802953808011027675051457 17102215356008270756288593)
    ·
      refine ⟨12826661517006203067216445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17102215356008270756288593 12826661517006203067216445)
      ·
        refine ⟨4809998068877326150206167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12826661517006203067216445 4809998068877326150206167)
        ·
          refine ⟨7214997103315989225309251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4809998068877326150206167 7214997103315989225309251)
          ·
            refine ⟨10822495654973983837963877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7214997103315989225309251 10822495654973983837963877)
            ·
              refine ⟨2029217935307621969618227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10822495654973983837963877 2029217935307621969618227)
              ·
                refine ⟨3043826902961432954427341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029217935307621969618227 3043826902961432954427341)
                ·
                  refine ⟨1141435088610537357910253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3043826902961432954427341 1141435088610537357910253)
                  ·
                    refine ⟨428038158228951509216345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1141435088610537357910253 428038158228951509216345)
                    ·
                      refine ⟨321028618671713631912259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 428038158228951509216345 321028618671713631912259)
                      ·
                        rfl

theorem cell23_625201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 4, 1, 3, 3, 2].length) (baseStart_625201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625201 prefixEnd_625201 := by exact prefixLift 625201
  have htrace : WordTrace (prefixWord ++ tailWord_625201) baseStart_625201 baseEnd_625201 := by
    simpa [prefixWord, tailWord_625201, baseEnd_625201] using wordTrace_append hprefix tailTrace_625201
  have hstable : (prefixWord ++ tailWord_625201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625201).length < 2 ^ (prefixWord ++ tailWord_625201).sum := by decide
  have hdescent : baseEnd_625201 < baseStart_625201 := by decide
  rcases family_descends (prefixWord ++ tailWord_625201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625207 : List Nat := [1, 1, 3, 1, 2, 3, 1, 2, 1, 8]
def baseStart_625207 : Nat := 118140960795 + 625207 * 2 ^ 59
def prefixEnd_625207 : Nat := 4983230072969 + 3 ^ 40 * 625207 * 2
def baseEnd_625207 : Nat := 107010566518546869479077

theorem tailTrace_625207 : CollatzResearch.WordTrace tailWord_625207 prefixEnd_625207 107010566518546869479077 := by
  unfold tailWord_625207
  simp only [CollatzResearch.WordTrace]
  refine ⟨22803172645989290699769875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15202115097326193799846583 22803172645989290699769875)
  ·
    refine ⟨34204758968983936049654813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22803172645989290699769875 34204758968983936049654813)
    ·
      refine ⟨12826784613368976018620555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34204758968983936049654813 12826784613368976018620555)
      ·
        refine ⟨19240176920053464027930833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12826784613368976018620555 19240176920053464027930833)
        ·
          refine ⟨14430132690040098020948125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19240176920053464027930833 14430132690040098020948125)
          ·
            refine ⟨5411299758765036757855547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14430132690040098020948125 5411299758765036757855547)
            ·
              refine ⟨8116949638147555136783321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5411299758765036757855547 8116949638147555136783321)
              ·
                refine ⟨6087712228610666352587491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8116949638147555136783321 6087712228610666352587491)
                ·
                  refine ⟨9131568342915999528881237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6087712228610666352587491 9131568342915999528881237)
                  ·
                    refine ⟨107010566518546869479077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 9131568342915999528881237 107010566518546869479077)
                    ·
                      rfl

theorem cell23_625207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 8].length) (baseStart_625207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625207 prefixEnd_625207 := by exact prefixLift 625207
  have htrace : WordTrace (prefixWord ++ tailWord_625207) baseStart_625207 baseEnd_625207 := by
    simpa [prefixWord, tailWord_625207, baseEnd_625207] using wordTrace_append hprefix tailTrace_625207
  have hstable : (prefixWord ++ tailWord_625207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625207).length < 2 ^ (prefixWord ++ tailWord_625207).sum := by decide
  have hdescent : baseEnd_625207 < baseStart_625207 := by decide
  rcases family_descends (prefixWord ++ tailWord_625207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625247 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 9]
def baseStart_625247 : Nat := 118140960795 + 625247 * 2 ^ 59
def prefixEnd_625247 : Nat := 4983230072969 + 3 ^ 40 * 625247 * 2
def baseEnd_625247 : Nat := 321052238781820451937047

theorem tailTrace_625247 : CollatzResearch.WordTrace tailWord_625247 prefixEnd_625247 321052238781820451937047 := by
  unfold tailWord_625247
  simp only [CollatzResearch.WordTrace]
  refine ⟨22804631565844377531225995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15203087710562918354150663 22804631565844377531225995)
  ·
    refine ⟨34206947348766566296838993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22804631565844377531225995 34206947348766566296838993)
    ·
      refine ⟨25655210511574924722629245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34206947348766566296838993 25655210511574924722629245)
      ·
        refine ⟨9620703941840596770985967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25655210511574924722629245 9620703941840596770985967)
        ·
          refine ⟨14431055912760895156478951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9620703941840596770985967 14431055912760895156478951)
          ·
            refine ⟨21646583869141342734718427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14431055912760895156478951 21646583869141342734718427)
            ·
              refine ⟨32469875803712014102077641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21646583869141342734718427 32469875803712014102077641)
              ·
                refine ⟨24352406852784010576558231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32469875803712014102077641 24352406852784010576558231)
                ·
                  refine ⟨36528610279176015864837347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24352406852784010576558231 36528610279176015864837347)
                  ·
                    refine ⟨54792915418764023797256021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36528610279176015864837347 54792915418764023797256021)
                    ·
                      refine ⟨321052238781820451937047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 54792915418764023797256021 321052238781820451937047)
                      ·
                        rfl

theorem cell23_625247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_625247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625247 prefixEnd_625247 := by exact prefixLift 625247
  have htrace : WordTrace (prefixWord ++ tailWord_625247) baseStart_625247 baseEnd_625247 := by
    simpa [prefixWord, tailWord_625247, baseEnd_625247] using wordTrace_append hprefix tailTrace_625247
  have hstable : (prefixWord ++ tailWord_625247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625247).length < 2 ^ (prefixWord ++ tailWord_625247).sum := by decide
  have hdescent : baseEnd_625247 < baseStart_625247 := by decide
  rcases family_descends (prefixWord ++ tailWord_625247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625248 : List Nat := [2, 1, 1, 3, 2, 1, 2, 5, 2, 2, 2]
def baseStart_625248 : Nat := 118140960795 + 625248 * 2 ^ 59
def prefixEnd_625248 : Nat := 4983230072969 + 3 ^ 40 * 625248 * 2
def baseEnd_625248 : Nat := 321052752262474948024543

theorem tailTrace_625248 : CollatzResearch.WordTrace tailWord_625248 prefixEnd_625248 321052752262474948024543 := by
  unfold tailWord_625248
  simp only [CollatzResearch.WordTrace]
  refine ⟨11402334019420377351006199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15203112025893836468008265 11402334019420377351006199)
  ·
    refine ⟨17103501029130566026509299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11402334019420377351006199 17103501029130566026509299)
    ·
      refine ⟨25655251543695849039763949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17103501029130566026509299 25655251543695849039763949)
      ·
        refine ⟨9620719328885943389911481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25655251543695849039763949 9620719328885943389911481)
        ·
          refine ⟨7215539496664457542433611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9620719328885943389911481 7215539496664457542433611)
          ·
            refine ⟨10823309244996686313650417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7215539496664457542433611 10823309244996686313650417)
            ·
              refine ⟨8117481933747514735237813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10823309244996686313650417 8117481933747514735237813)
              ·
                refine ⟨761013931288829506428545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8117481933747514735237813 761013931288829506428545)
                ·
                  refine ⟨570760448466622129821409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 761013931288829506428545 570760448466622129821409)
                  ·
                    refine ⟨428070336349966597366057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 570760448466622129821409 428070336349966597366057)
                    ·
                      refine ⟨321052752262474948024543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 428070336349966597366057 321052752262474948024543)
                      ·
                        rfl

theorem cell23_625248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_625248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625248 prefixEnd_625248 := by exact prefixLift 625248
  have htrace : WordTrace (prefixWord ++ tailWord_625248) baseStart_625248 baseEnd_625248 := by
    simpa [prefixWord, tailWord_625248, baseEnd_625248] using wordTrace_append hprefix tailTrace_625248
  have hstable : (prefixWord ++ tailWord_625248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625248).length < 2 ^ (prefixWord ++ tailWord_625248).sum := by decide
  have hdescent : baseEnd_625248 < baseStart_625248 := by decide
  rcases family_descends (prefixWord ++ tailWord_625248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625271 : List Nat := [1, 1, 3, 1, 1, 3, 5, 3, 5]
def baseStart_625271 : Nat := 118140960795 + 625271 * 2 ^ 59
def prefixEnd_625271 : Nat := 4983230072969 + 3 ^ 40 * 625271 * 2
def baseEnd_625271 : Nat := 35673840257503150892993

theorem tailTrace_625271 : CollatzResearch.WordTrace tailWord_625271 prefixEnd_625271 35673840257503150892993 := by
  unfold tailWord_625271
  simp only [CollatzResearch.WordTrace]
  refine ⟨22805506917757429630099667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15203671278504953086733111 22805506917757429630099667)
  ·
    refine ⟨34208260376636144445149501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22805506917757429630099667 34208260376636144445149501)
    ·
      refine ⟨12828097641238554166931063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34208260376636144445149501 12828097641238554166931063)
      ·
        refine ⟨19242146461857831250396595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12828097641238554166931063 19242146461857831250396595)
        ·
          refine ⟨28863219692786746875594893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19242146461857831250396595 28863219692786746875594893)
          ·
            refine ⟨10823707384795030078348085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28863219692786746875594893 10823707384795030078348085)
            ·
              refine ⟨1014722567324534069845133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10823707384795030078348085 1014722567324534069845133)
              ·
                refine ⟨380520962746700276191925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1014722567324534069845133 380520962746700276191925)
                ·
                  refine ⟨35673840257503150892993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 380520962746700276191925 35673840257503150892993)
                  ·
                    rfl

theorem cell23_625271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 5].length) (baseStart_625271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625271 prefixEnd_625271 := by exact prefixLift 625271
  have htrace : WordTrace (prefixWord ++ tailWord_625271) baseStart_625271 baseEnd_625271 := by
    simpa [prefixWord, tailWord_625271, baseEnd_625271] using wordTrace_append hprefix tailTrace_625271
  have hstable : (prefixWord ++ tailWord_625271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625271).length < 2 ^ (prefixWord ++ tailWord_625271).sum := by decide
  have hdescent : baseEnd_625271 < baseStart_625271 := by decide
  rcases family_descends (prefixWord ++ tailWord_625271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625365 : List Nat := [1, 3, 2, 5, 1, 1, 1, 2, 3, 4]
def baseStart_625365 : Nat := 118140960795 + 625365 * 2 ^ 59
def prefixEnd_625365 : Nat := 4983230072969 + 3 ^ 40 * 625365 * 2
def baseEnd_625365 : Nat := 107037609833016996753835

theorem tailTrace_625365 : CollatzResearch.WordTrace tailWord_625365 prefixEnd_625365 107037609833016996753835 := by
  unfold tailWord_625365
  simp only [CollatzResearch.WordTrace]
  refine ⟨22808935379416883684021549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15205956919611255789347699 22808935379416883684021549)
  ·
    refine ⟨8553350767281331381508081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22808935379416883684021549 8553350767281331381508081)
    ·
      refine ⟨6415013075460998536131061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8553350767281331381508081 6415013075460998536131061)
      ·
        refine ⟨601407475824468612762287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6415013075460998536131061 601407475824468612762287)
        ·
          refine ⟨902111213736702919143431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601407475824468612762287 902111213736702919143431)
          ·
            refine ⟨1353166820605054378715147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902111213736702919143431 1353166820605054378715147)
            ·
              refine ⟨2029750230907581568072721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353166820605054378715147 2029750230907581568072721)
              ·
                refine ⟨1522312673180686176054541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2029750230907581568072721 1522312673180686176054541)
                ·
                  refine ⟨570867252442757316020453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1522312673180686176054541 570867252442757316020453)
                  ·
                    refine ⟨107037609833016996753835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 570867252442757316020453 107037609833016996753835)
                    ·
                      rfl

theorem cell23_625365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_625365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625365 prefixEnd_625365 := by exact prefixLift 625365
  have htrace : WordTrace (prefixWord ++ tailWord_625365) baseStart_625365 baseEnd_625365 := by
    simpa [prefixWord, tailWord_625365, baseEnd_625365] using wordTrace_append hprefix tailTrace_625365
  have hstable : (prefixWord ++ tailWord_625365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625365).length < 2 ^ (prefixWord ++ tailWord_625365).sum := by decide
  have hdescent : baseEnd_625365 < baseStart_625365 := by decide
  rcases family_descends (prefixWord ++ tailWord_625365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625405 : List Nat := [1, 4, 1, 1, 1, 1, 3, 6, 1, 1, 3]
def baseStart_625405 : Nat := 118140960795 + 625405 * 2 ^ 59
def prefixEnd_625405 : Nat := 4983230072969 + 3 ^ 40 * 625405 * 2
def baseEnd_625405 : Nat := 321133368725230833761321

theorem tailTrace_625405 : CollatzResearch.WordTrace tailWord_625405 prefixEnd_625405 321133368725230833761321 := by
  unfold tailWord_625405
  simp only [CollatzResearch.WordTrace]
  refine ⟨22810394299271970515477669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15206929532847980343651779 22810394299271970515477669)
  ·
    refine ⟨4276948931113494471652063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22810394299271970515477669 4276948931113494471652063)
    ·
      refine ⟨6415423396670241707478095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4276948931113494471652063 6415423396670241707478095)
      ·
        refine ⟨9623135095005362561217143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6415423396670241707478095 9623135095005362561217143)
        ·
          refine ⟨14434702642508043841825715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9623135095005362561217143 14434702642508043841825715)
          ·
            refine ⟨21652053963762065762738573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14434702642508043841825715 21652053963762065762738573)
            ·
              refine ⟨8119520236410774661026965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21652053963762065762738573 8119520236410774661026965)
              ·
                refine ⟨380602511081755062235639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 8119520236410774661026965 380602511081755062235639)
                ·
                  refine ⟨570903766622632593353459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380602511081755062235639 570903766622632593353459)
                  ·
                    refine ⟨856355649933948890030189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 570903766622632593353459 856355649933948890030189)
                    ·
                      refine ⟨321133368725230833761321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 856355649933948890030189 321133368725230833761321)
                      ·
                        rfl

theorem cell23_625405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 1, 1, 3].length) (baseStart_625405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625405 prefixEnd_625405 := by exact prefixLift 625405
  have htrace : WordTrace (prefixWord ++ tailWord_625405) baseStart_625405 baseEnd_625405 := by
    simpa [prefixWord, tailWord_625405, baseEnd_625405] using wordTrace_append hprefix tailTrace_625405
  have hstable : (prefixWord ++ tailWord_625405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625405).length < 2 ^ (prefixWord ++ tailWord_625405).sum := by decide
  have hdescent : baseEnd_625405 < baseStart_625405 := by decide
  rcases family_descends (prefixWord ++ tailWord_625405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625441 : List Nat := [1, 2, 3, 2, 1, 2, 2, 1, 3, 2, 4]
def baseStart_625441 : Nat := 118140960795 + 625441 * 2 ^ 59
def prefixEnd_625441 : Nat := 4983230072969 + 3 ^ 40 * 625441 * 2
def baseEnd_625441 : Nat := 321151854028792692911155

theorem tailTrace_625441 : CollatzResearch.WordTrace tailWord_625441 prefixEnd_625441 321151854028792692911155 := by
  unfold tailWord_625441
  simp only [CollatzResearch.WordTrace]
  refine ⟨22811707327141548663788177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15207804884761032442525451 22811707327141548663788177)
  ·
    refine ⟨17108780495356161497841133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22811707327141548663788177 17108780495356161497841133)
    ·
      refine ⟨6415792685758560561690425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17108780495356161497841133 6415792685758560561690425)
      ·
        refine ⟨4811844514318920421267819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6415792685758560561690425 4811844514318920421267819)
        ·
          refine ⟨7217766771478380631901729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4811844514318920421267819 7217766771478380631901729)
          ·
            refine ⟨5413325078608785473926297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7217766771478380631901729 5413325078608785473926297)
            ·
              refine ⟨4059993808956589105444723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5413325078608785473926297 4059993808956589105444723)
              ·
                refine ⟨6089990713434883658167085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4059993808956589105444723 6089990713434883658167085)
                ·
                  refine ⟨2283746517538081371812657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6089990713434883658167085 2283746517538081371812657)
                  ·
                    refine ⟨1712809888153561028859493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2283746517538081371812657 1712809888153561028859493)
                    ·
                      refine ⟨321151854028792692911155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1712809888153561028859493 321151854028792692911155)
                      ·
                        rfl

theorem cell23_625441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 2, 1, 3, 2, 4].length) (baseStart_625441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625441 prefixEnd_625441 := by exact prefixLift 625441
  have htrace : WordTrace (prefixWord ++ tailWord_625441) baseStart_625441 baseEnd_625441 := by
    simpa [prefixWord, tailWord_625441, baseEnd_625441] using wordTrace_append hprefix tailTrace_625441
  have hstable : (prefixWord ++ tailWord_625441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625441).length < 2 ^ (prefixWord ++ tailWord_625441).sum := by decide
  have hdescent : baseEnd_625441 < baseStart_625441 := by decide
  rcases family_descends (prefixWord ++ tailWord_625441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625448 : List Nat := [2, 1, 5, 1, 1, 1, 4, 1, 1, 1, 5]
def baseStart_625448 : Nat := 118140960795 + 625448 * 2 ^ 59
def prefixEnd_625448 : Nat := 4983230072969 + 3 ^ 40 * 625448 * 2
def baseEnd_625448 : Nat := 321155448393374165523623

theorem tailTrace_625448 : CollatzResearch.WordTrace tailWord_625448 prefixEnd_625448 321155448393374165523623 := by
  unfold tailWord_625448
  simp only [CollatzResearch.WordTrace]
  refine ⟨11405981319058094429646499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15207975092077459239528665 11405981319058094429646499)
  ·
    refine ⟨17108971978587141644469749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11405981319058094429646499 17108971978587141644469749)
    ·
      refine ⟨1603966122992544529169039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17108971978587141644469749 1603966122992544529169039)
      ·
        refine ⟨2405949184488816793753559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603966122992544529169039 2405949184488816793753559)
        ·
          refine ⟨3608923776733225190630339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2405949184488816793753559 3608923776733225190630339)
          ·
            refine ⟨5413385665099837785945509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3608923776733225190630339 5413385665099837785945509)
            ·
              refine ⟨1015009812206219584864783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5413385665099837785945509 1015009812206219584864783)
              ·
                refine ⟨1522514718309329377297175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015009812206219584864783 1522514718309329377297175)
                ·
                  refine ⟨2283772077463994065945763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522514718309329377297175 2283772077463994065945763)
                  ·
                    refine ⟨3425658116195991098918645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2283772077463994065945763 3425658116195991098918645)
                    ·
                      refine ⟨321155448393374165523623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3425658116195991098918645 321155448393374165523623)
                      ·
                        rfl

theorem cell23_625448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_625448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625448 prefixEnd_625448 := by exact prefixLift 625448
  have htrace : WordTrace (prefixWord ++ tailWord_625448) baseStart_625448 baseEnd_625448 := by
    simpa [prefixWord, tailWord_625448, baseEnd_625448] using wordTrace_append hprefix tailTrace_625448
  have hstable : (prefixWord ++ tailWord_625448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625448).length < 2 ^ (prefixWord ++ tailWord_625448).sum := by decide
  have hdescent : baseEnd_625448 < baseStart_625448 := by decide
  rcases family_descends (prefixWord ++ tailWord_625448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625512 : List Nat := [2, 1, 4, 2, 1, 3, 2, 2, 2, 1, 3]
def baseStart_625512 : Nat := 118140960795 + 625512 * 2 ^ 59
def prefixEnd_625512 : Nat := 4983230072969 + 3 ^ 40 * 625512 * 2
def baseEnd_625512 : Nat := 321188311155261915123329

theorem tailTrace_625512 : CollatzResearch.WordTrace tailWord_625512 prefixEnd_625512 321188311155261915123329 := by
  unfold tailWord_625512
  simp only [CollatzResearch.WordTrace]
  refine ⟨11407148454942163894811395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15209531273256218526415193 11407148454942163894811395)
  ·
    refine ⟨17110722682413245842217093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11407148454942163894811395 17110722682413245842217093)
    ·
      refine ⟨3208260502952483595415705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17110722682413245842217093 3208260502952483595415705)
      ·
        refine ⟨2406195377214362696561779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3208260502952483595415705 2406195377214362696561779)
        ·
          refine ⟨3609293065821544044842669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2406195377214362696561779 3609293065821544044842669)
          ·
            refine ⟨1353484899683079016816001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3609293065821544044842669 1353484899683079016816001)
            ·
              refine ⟨1015113674762309262612001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1353484899683079016816001 1015113674762309262612001)
              ·
                refine ⟨761335256071731946959001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1015113674762309262612001 761335256071731946959001)
                ·
                  refine ⟨571001442053798960219251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 761335256071731946959001 571001442053798960219251)
                  ·
                    refine ⟨856502163080698440328877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 571001442053798960219251 856502163080698440328877)
                    ·
                      refine ⟨321188311155261915123329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 856502163080698440328877 321188311155261915123329)
                      ·
                        rfl

theorem cell23_625512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_625512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625512 prefixEnd_625512 := by exact prefixLift 625512
  have htrace : WordTrace (prefixWord ++ tailWord_625512) baseStart_625512 baseEnd_625512 := by
    simpa [prefixWord, tailWord_625512, baseEnd_625512] using wordTrace_append hprefix tailTrace_625512
  have hstable : (prefixWord ++ tailWord_625512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625512).length < 2 ^ (prefixWord ++ tailWord_625512).sum := by decide
  have hdescent : baseEnd_625512 < baseStart_625512 := by decide
  rcases family_descends (prefixWord ++ tailWord_625512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625531 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 4]
def baseStart_625531 : Nat := 118140960795 + 625531 * 2 ^ 59
def prefixEnd_625531 : Nat := 4983230072969 + 3 ^ 40 * 625531 * 2
def baseEnd_625531 : Nat := 321198067287697340785741

theorem tailTrace_625531 : CollatzResearch.WordTrace tailWord_625531 prefixEnd_625531 321198067287697340785741 := by
  unfold tailWord_625531
  simp only [CollatzResearch.WordTrace]
  refine ⟨22814989896815494034564447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15209993264543662689709631 22814989896815494034564447)
  ·
    refine ⟨34222484845223241051846671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22814989896815494034564447 34222484845223241051846671)
    ·
      refine ⟨51333727267834861577770007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34222484845223241051846671 51333727267834861577770007)
      ·
        refine ⟨77000590901752292366655011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51333727267834861577770007 77000590901752292366655011)
        ·
          refine ⟨115500886352628438549982517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77000590901752292366655011 115500886352628438549982517)
          ·
            refine ⟨10828208095558916114060861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 115500886352628438549982517 10828208095558916114060861)
            ·
              refine ⟨4060578035834593542772823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10828208095558916114060861 4060578035834593542772823)
              ·
                refine ⟨6090867053751890314159235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4060578035834593542772823 6090867053751890314159235)
                ·
                  refine ⟨9136300580627835471238853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6090867053751890314159235 9136300580627835471238853)
                  ·
                    refine ⟨1713056358867719150857285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9136300580627835471238853 1713056358867719150857285)
                    ·
                      refine ⟨321198067287697340785741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1713056358867719150857285 321198067287697340785741)
                      ·
                        rfl

theorem cell23_625531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 1, 4, 4].length) (baseStart_625531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625531 prefixEnd_625531 := by exact prefixLift 625531
  have htrace : WordTrace (prefixWord ++ tailWord_625531) baseStart_625531 baseEnd_625531 := by
    simpa [prefixWord, tailWord_625531, baseEnd_625531] using wordTrace_append hprefix tailTrace_625531
  have hstable : (prefixWord ++ tailWord_625531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625531).length < 2 ^ (prefixWord ++ tailWord_625531).sum := by decide
  have hdescent : baseEnd_625531 < baseStart_625531 := by decide
  rcases family_descends (prefixWord ++ tailWord_625531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625541 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 9]
def baseStart_625541 : Nat := 118140960795 + 625541 * 2 ^ 59
def prefixEnd_625541 : Nat := 4983230072969 + 3 ^ 40 * 625541 * 2
def baseEnd_625541 : Nat := 35689244677138033517855

theorem tailTrace_625541 : CollatzResearch.WordTrace tailWord_625541 prefixEnd_625541 35689244677138033517855 := by
  unfold tailWord_625541
  simp only [CollatzResearch.WordTrace]
  refine ⟨22815354626779265742428477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15210236417852843828285651 22815354626779265742428477)
  ·
    refine ⟨8555757985042224653410679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22815354626779265742428477 8555757985042224653410679)
    ·
      refine ⟨12833636977563336980116019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8555757985042224653410679 12833636977563336980116019)
      ·
        refine ⟨19250455466345005470174029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12833636977563336980116019 19250455466345005470174029)
        ·
          refine ⟨7218920799879377051315261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19250455466345005470174029 7218920799879377051315261)
          ·
            refine ⟨2707095299954766394243223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7218920799879377051315261 2707095299954766394243223)
            ·
              refine ⟨4060642949932149591364835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2707095299954766394243223 4060642949932149591364835)
              ·
                refine ⟨6090964424898224387047253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4060642949932149591364835 6090964424898224387047253)
                ·
                  refine ⟨35689244677138033517855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6090964424898224387047253 35689244677138033517855)
                  ·
                    rfl

theorem cell23_625541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 9].length) (baseStart_625541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625541 prefixEnd_625541 := by exact prefixLift 625541
  have htrace : WordTrace (prefixWord ++ tailWord_625541) baseStart_625541 baseEnd_625541 := by
    simpa [prefixWord, tailWord_625541, baseEnd_625541] using wordTrace_append hprefix tailTrace_625541
  have hstable : (prefixWord ++ tailWord_625541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625541).length < 2 ^ (prefixWord ++ tailWord_625541).sum := by decide
  have hdescent : baseEnd_625541 < baseStart_625541 := by decide
  rcases family_descends (prefixWord ++ tailWord_625541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625568 : List Nat := [2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 3]
def baseStart_625568 : Nat := 118140960795 + 625568 * 2 ^ 59
def prefixEnd_625568 : Nat := 4983230072969 + 3 ^ 40 * 625568 * 2
def baseEnd_625568 : Nat := 321217066071913696023071

theorem tailTrace_625568 : CollatzResearch.WordTrace tailWord_625568 prefixEnd_625568 321217066071913696023071 := by
  unfold tailWord_625568
  simp only [CollatzResearch.WordTrace]
  refine ⟨11408169698840724676830679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15210892931787632902440905 11408169698840724676830679)
  ·
    refine ⟨17112254548261087015246019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11408169698840724676830679 17112254548261087015246019)
    ·
      refine ⟨25668381822391630522869029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17112254548261087015246019 25668381822391630522869029)
      ·
        refine ⟨4812821591698430723037943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25668381822391630522869029 4812821591698430723037943)
        ·
          refine ⟨7219232387547646084556915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4812821591698430723037943 7219232387547646084556915)
          ·
            refine ⟨10828848581321469126835373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7219232387547646084556915 10828848581321469126835373)
            ·
              refine ⟨4060818217995550922563265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10828848581321469126835373 4060818217995550922563265)
              ·
                refine ⟨3045613663496663191922449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4060818217995550922563265 3045613663496663191922449)
                ·
                  refine ⟨2284210247622497393941837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3045613663496663191922449 2284210247622497393941837)
                  ·
                    refine ⟨856578842858436522728189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2284210247622497393941837 856578842858436522728189)
                    ·
                      refine ⟨321217066071913696023071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 856578842858436522728189 321217066071913696023071)
                      ·
                        rfl

theorem cell23_625568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_625568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625568 prefixEnd_625568 := by exact prefixLift 625568
  have htrace : WordTrace (prefixWord ++ tailWord_625568) baseStart_625568 baseEnd_625568 := by
    simpa [prefixWord, tailWord_625568, baseEnd_625568] using wordTrace_append hprefix tailTrace_625568
  have hstable : (prefixWord ++ tailWord_625568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625568).length < 2 ^ (prefixWord ++ tailWord_625568).sum := by decide
  have hdescent : baseEnd_625568 < baseStart_625568 := by decide
  rcases family_descends (prefixWord ++ tailWord_625568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625569 : List Nat := [1, 2, 3, 4, 1, 1, 3, 2, 2, 2, 2]
def baseStart_625569 : Nat := 118140960795 + 625569 * 2 ^ 59
def prefixEnd_625569 : Nat := 4983230072969 + 3 ^ 40 * 625569 * 2
def baseEnd_625569 : Nat := 321217579552568192110567

theorem tailTrace_625569 : CollatzResearch.WordTrace tailWord_625569 prefixEnd_625569 321217579552568192110567 := by
  unfold tailWord_625569
  simp only [CollatzResearch.WordTrace]
  refine ⟨22816375870677826524447761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15210917247118551016298507 22816375870677826524447761)
  ·
    refine ⟨17112281903008369893335821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22816375870677826524447761 17112281903008369893335821)
    ·
      refine ⟨6417105713628138710000933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17112281903008369893335821 6417105713628138710000933)
      ·
        refine ⟨1203207321305276008125175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6417105713628138710000933 1203207321305276008125175)
        ·
          refine ⟨1804810981957914012187763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203207321305276008125175 1804810981957914012187763)
          ·
            refine ⟨2707216472936871018281645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1804810981957914012187763 2707216472936871018281645)
            ·
              refine ⟨1015206177351326631855617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2707216472936871018281645 1015206177351326631855617)
              ·
                refine ⟨761404633013494973891713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1015206177351326631855617 761404633013494973891713)
                ·
                  refine ⟨571053474760121230418785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 761404633013494973891713 571053474760121230418785)
                  ·
                    refine ⟨428290106070090922814089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 571053474760121230418785 428290106070090922814089)
                    ·
                      refine ⟨321217579552568192110567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 428290106070090922814089 321217579552568192110567)
                      ·
                        rfl

theorem cell23_625569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_625569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625569 prefixEnd_625569 := by exact prefixLift 625569
  have htrace : WordTrace (prefixWord ++ tailWord_625569) baseStart_625569 baseEnd_625569 := by
    simpa [prefixWord, tailWord_625569, baseEnd_625569] using wordTrace_append hprefix tailTrace_625569
  have hstable : (prefixWord ++ tailWord_625569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625569).length < 2 ^ (prefixWord ++ tailWord_625569).sum := by decide
  have hdescent : baseEnd_625569 < baseStart_625569 := by decide
  rcases family_descends (prefixWord ++ tailWord_625569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625575 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 7]
def baseStart_625575 : Nat := 118140960795 + 625575 * 2 ^ 59
def prefixEnd_625575 : Nat := 4983230072969 + 3 ^ 40 * 625575 * 2
def baseEnd_625575 : Nat := 35691184492943907626171

theorem tailTrace_625575 : CollatzResearch.WordTrace tailWord_625575 prefixEnd_625575 35691184492943907626171 := by
  unfold tailWord_625575
  simp only [CollatzResearch.WordTrace]
  refine ⟨22816594708656089549166179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15211063139104059699444119 22816594708656089549166179)
  ·
    refine ⟨34224892062984134323749269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22816594708656089549166179 34224892062984134323749269)
    ·
      refine ⟨1604291815452381296425747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34224892062984134323749269 1604291815452381296425747)
      ·
        refine ⟨2406437723178571944638621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1604291815452381296425747 2406437723178571944638621)
        ·
          refine ⟨902414146191964479239483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2406437723178571944638621 902414146191964479239483)
          ·
            refine ⟨1353621219287946718859225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902414146191964479239483 1353621219287946718859225)
            ·
              refine ⟨1015215914465960039144419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1353621219287946718859225 1015215914465960039144419)
              ·
                refine ⟨1522823871698940058716629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015215914465960039144419 1522823871698940058716629)
                ·
                  refine ⟨35691184492943907626171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1522823871698940058716629 35691184492943907626171)
                  ·
                    rfl

theorem cell23_625575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 7].length) (baseStart_625575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625575 prefixEnd_625575 := by exact prefixLift 625575
  have htrace : WordTrace (prefixWord ++ tailWord_625575) baseStart_625575 baseEnd_625575 := by
    simpa [prefixWord, tailWord_625575, baseEnd_625575] using wordTrace_append hprefix tailTrace_625575
  have hstable : (prefixWord ++ tailWord_625575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625575).length < 2 ^ (prefixWord ++ tailWord_625575).sum := by decide
  have hdescent : baseEnd_625575 < baseStart_625575 := by decide
  rcases family_descends (prefixWord ++ tailWord_625575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625606 : List Nat := [6, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_625606 : Nat := 118140960795 + 625606 * 2 ^ 59
def prefixEnd_625606 : Nat := 4983230072969 + 3 ^ 40 * 625606 * 2
def baseEnd_625606 : Nat := 321236578336784547347897

theorem tailTrace_625606 : CollatzResearch.WordTrace tailWord_625606 prefixEnd_625606 321236578336784547347897 := by
  unfold tailWord_625606
  simp only [CollatzResearch.WordTrace]
  refine ⟨713053917860743182610771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15211816914362521229029781 713053917860743182610771)
  ·
    refine ⟨1069580876791114773916157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 713053917860743182610771 1069580876791114773916157)
    ·
      refine ⟨401092828796668040218559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1069580876791114773916157 401092828796668040218559)
      ·
        refine ⟨601639243195002060327839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401092828796668040218559 601639243195002060327839)
        ·
          refine ⟨902458864792503090491759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 601639243195002060327839 902458864792503090491759)
          ·
            refine ⟨1353688297188754635737639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902458864792503090491759 1353688297188754635737639)
            ·
              refine ⟨2030532445783131953606459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353688297188754635737639 2030532445783131953606459)
              ·
                refine ⟨3045798668674697930409689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030532445783131953606459 3045798668674697930409689)
                ·
                  refine ⟨2284349001506023447807267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3045798668674697930409689 2284349001506023447807267)
                  ·
                    refine ⟨3426523502259035171710901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2284349001506023447807267 3426523502259035171710901)
                    ·
                      refine ⟨321236578336784547347897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3426523502259035171710901 321236578336784547347897)
                      ·
                        rfl

theorem cell23_625606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_625606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625606 prefixEnd_625606 := by exact prefixLift 625606
  have htrace : WordTrace (prefixWord ++ tailWord_625606) baseStart_625606 baseEnd_625606 := by
    simpa [prefixWord, tailWord_625606, baseEnd_625606] using wordTrace_append hprefix tailTrace_625606
  have hstable : (prefixWord ++ tailWord_625606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625606).length < 2 ^ (prefixWord ++ tailWord_625606).sum := by decide
  have hdescent : baseEnd_625606 < baseStart_625606 := by decide
  rcases family_descends (prefixWord ++ tailWord_625606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625622 : List Nat := [5, 2, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_625622 : Nat := 118140960795 + 625622 * 2 ^ 59
def prefixEnd_625622 : Nat := 4983230072969 + 3 ^ 40 * 625622 * 2
def baseEnd_625622 : Nat := 107081598009085494915941

theorem tailTrace_625622 : CollatzResearch.WordTrace tailWord_625622 prefixEnd_625622 107081598009085494915941 := by
  unfold tailWord_625622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426144308717863536007945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15212205959657211050751413 1426144308717863536007945)
  ·
    refine ⟨1069608231538397652005959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1426144308717863536007945 1069608231538397652005959)
    ·
      refine ⟨1604412347307596478008939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1069608231538397652005959 1604412347307596478008939)
      ·
        refine ⟨2406618520961394717013409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1604412347307596478008939 2406618520961394717013409)
        ·
          refine ⟨1804963890721046037760057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2406618520961394717013409 1804963890721046037760057)
          ·
            refine ⟨1353722918040784528320043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1804963890721046037760057 1353722918040784528320043)
            ·
              refine ⟨2030584377061176792480065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353722918040784528320043 2030584377061176792480065)
              ·
                refine ⟨1522938282795882594360049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2030584377061176792480065 1522938282795882594360049)
                ·
                  refine ⟨1142203712096911945770037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1522938282795882594360049 1142203712096911945770037)
                  ·
                    refine ⟨107081598009085494915941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1142203712096911945770037 107081598009085494915941)
                    ·
                      rfl

theorem cell23_625622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_625622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625622 prefixEnd_625622 := by exact prefixLift 625622
  have htrace : WordTrace (prefixWord ++ tailWord_625622) baseStart_625622 baseEnd_625622 := by
    simpa [prefixWord, tailWord_625622, baseEnd_625622] using wordTrace_append hprefix tailTrace_625622
  have hstable : (prefixWord ++ tailWord_625622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625622).length < 2 ^ (prefixWord ++ tailWord_625622).sum := by decide
  have hdescent : baseEnd_625622 < baseStart_625622 := by decide
  rcases family_descends (prefixWord ++ tailWord_625622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625625 : List Nat := [1, 2, 1, 2, 5, 2, 1, 2, 2, 1, 4]
def baseStart_625625 : Nat := 118140960795 + 625625 * 2 ^ 59
def prefixEnd_625625 : Nat := 4983230072969 + 3 ^ 40 * 625625 * 2
def baseEnd_625625 : Nat := 321246334469219973010309

theorem tailTrace_625625 : CollatzResearch.WordTrace tailWord_625625 prefixEnd_625625 321246334469219973010309 := by
  unfold tailWord_625625
  simp only [CollatzResearch.WordTrace]
  refine ⟨22818418358474948088486329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15212278905649965392324219 22818418358474948088486329)
  ·
    refine ⟨17113813768856211066364747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22818418358474948088486329 17113813768856211066364747)
    ·
      refine ⟨25670720653284316599547121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17113813768856211066364747 25670720653284316599547121)
      ·
        refine ⟨19253040489963237449660341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25670720653284316599547121 19253040489963237449660341)
        ·
          refine ⟨1804972545934053510905657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19253040489963237449660341 1804972545934053510905657)
          ·
            refine ⟨1353729409450540133179243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1804972545934053510905657 1353729409450540133179243)
            ·
              refine ⟨2030594114175810199768865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353729409450540133179243 2030594114175810199768865)
              ·
                refine ⟨1522945585631857649826649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2030594114175810199768865 1522945585631857649826649)
                ·
                  refine ⟨1142209189223893237369987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1522945585631857649826649 1142209189223893237369987)
                  ·
                    refine ⟨1713313783835839856054981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1142209189223893237369987 1713313783835839856054981)
                    ·
                      refine ⟨321246334469219973010309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1713313783835839856054981 321246334469219973010309)
                      ·
                        rfl

theorem cell23_625625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 2, 1, 4].length) (baseStart_625625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625625 prefixEnd_625625 := by exact prefixLift 625625
  have htrace : WordTrace (prefixWord ++ tailWord_625625) baseStart_625625 baseEnd_625625 := by
    simpa [prefixWord, tailWord_625625, baseEnd_625625] using wordTrace_append hprefix tailTrace_625625
  have hstable : (prefixWord ++ tailWord_625625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625625).length < 2 ^ (prefixWord ++ tailWord_625625).sum := by decide
  have hdescent : baseEnd_625625 < baseStart_625625 := by decide
  rcases family_descends (prefixWord ++ tailWord_625625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625658 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3]
def baseStart_625658 : Nat := 118140960795 + 625658 * 2 ^ 59
def prefixEnd_625658 : Nat := 4983230072969 + 3 ^ 40 * 625658 * 2
def baseEnd_625658 : Nat := 321263279330818343897657

theorem tailTrace_625658 : CollatzResearch.WordTrace tailWord_625658 prefixEnd_625658 321263279330818343897657 := by
  unfold tailWord_625658
  simp only [CollatzResearch.WordTrace]
  refine ⟨5704905491838848681109407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15213081311570263149625085 5704905491838848681109407)
  ·
    refine ⟨8557358237758273021664111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5704905491838848681109407 8557358237758273021664111)
    ·
      refine ⟨12836037356637409532496167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8557358237758273021664111 12836037356637409532496167)
      ·
        refine ⟨19254056034956114298744251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12836037356637409532496167 19254056034956114298744251)
        ·
          refine ⟨28881084052434171448116377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19254056034956114298744251 28881084052434171448116377)
          ·
            refine ⟨21660813039325628586087283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28881084052434171448116377 21660813039325628586087283)
            ·
              refine ⟨32491219558988442879130925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21660813039325628586087283 32491219558988442879130925)
              ·
                refine ⟨12184207334620666079674097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32491219558988442879130925 12184207334620666079674097)
                ·
                  refine ⟨9138155500965499559755573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12184207334620666079674097 9138155500965499559755573)
                  ·
                    refine ⟨856702078215515583727085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9138155500965499559755573 856702078215515583727085)
                    ·
                      refine ⟨321263279330818343897657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 856702078215515583727085 321263279330818343897657)
                      ·
                        rfl

theorem cell23_625658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_625658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625658 prefixEnd_625658 := by exact prefixLift 625658
  have htrace : WordTrace (prefixWord ++ tailWord_625658) baseStart_625658 baseEnd_625658 := by
    simpa [prefixWord, tailWord_625658, baseEnd_625658] using wordTrace_append hprefix tailTrace_625658
  have hstable : (prefixWord ++ tailWord_625658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625658).length < 2 ^ (prefixWord ++ tailWord_625658).sum := by decide
  have hdescent : baseEnd_625658 < baseStart_625658 := by decide
  rcases family_descends (prefixWord ++ tailWord_625658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625715 : List Nat := [1, 1, 1, 2, 4, 1, 1, 6, 1, 1, 4]
def baseStart_625715 : Nat := 118140960795 + 625715 * 2 ^ 59
def prefixEnd_625715 : Nat := 4983230072969 + 3 ^ 40 * 625715 * 2
def baseEnd_625715 : Nat := 321292547728124620884895

theorem tailTrace_625715 : CollatzResearch.WordTrace tailWord_625715 prefixEnd_625715 321292547728124620884895 := by
  unfold tailWord_625715
  simp only [CollatzResearch.WordTrace]
  refine ⟨22821700928148893459262599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15214467285432595639508399 22821700928148893459262599)
  ·
    refine ⟨34232551392223340188893899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22821700928148893459262599 34232551392223340188893899)
    ·
      refine ⟨51348827088335010283340849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34232551392223340188893899 51348827088335010283340849)
      ·
        refine ⟨38511620316251257712505637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51348827088335010283340849 38511620316251257712505637)
        ·
          refine ⟨7220928809297110821094807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38511620316251257712505637 7220928809297110821094807)
          ·
            refine ⟨10831393213945666231642211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7220928809297110821094807 10831393213945666231642211)
            ·
              refine ⟨16247089820918499347463317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10831393213945666231642211 16247089820918499347463317)
              ·
                refine ⟨761582335355554656912343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16247089820918499347463317 761582335355554656912343)
                ·
                  refine ⟨1142373503033331985368515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761582335355554656912343 1142373503033331985368515)
                  ·
                    refine ⟨1713560254549997978052773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1142373503033331985368515 1713560254549997978052773)
                    ·
                      refine ⟨321292547728124620884895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1713560254549997978052773 321292547728124620884895)
                      ·
                        rfl

theorem cell23_625715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 1, 1, 4].length) (baseStart_625715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625715 prefixEnd_625715 := by exact prefixLift 625715
  have htrace : WordTrace (prefixWord ++ tailWord_625715) baseStart_625715 baseEnd_625715 := by
    simpa [prefixWord, tailWord_625715, baseEnd_625715] using wordTrace_append hprefix tailTrace_625715
  have hstable : (prefixWord ++ tailWord_625715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625715).length < 2 ^ (prefixWord ++ tailWord_625715).sum := by decide
  have hdescent : baseEnd_625715 < baseStart_625715 := by decide
  rcases family_descends (prefixWord ++ tailWord_625715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625725 : List Nat := [1, 4, 1, 3, 1, 2, 2, 2, 1, 6]
def baseStart_625725 : Nat := 118140960795 + 625725 * 2 ^ 59
def prefixEnd_625725 : Nat := 4983230072969 + 3 ^ 40 * 625725 * 2
def baseEnd_625725 : Nat := 107099227511556527253283

theorem tailTrace_625725 : CollatzResearch.WordTrace tailWord_625725 prefixEnd_625725 107099227511556527253283 := by
  unfold tailWord_625725
  simp only [CollatzResearch.WordTrace]
  refine ⟨22822065658112665167126629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15214710438741776778084419 22822065658112665167126629)
  ·
    refine ⟨4279137310896124718836243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22822065658112665167126629 4279137310896124718836243)
    ·
      refine ⟨6418705966344187078254365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4279137310896124718836243 6418705966344187078254365)
      ·
        refine ⟨2407014737379070154345387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6418705966344187078254365 2407014737379070154345387)
        ·
          refine ⟨3610522106068605231518081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407014737379070154345387 3610522106068605231518081)
          ·
            refine ⟨2707891579551453923638561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3610522106068605231518081 2707891579551453923638561)
            ·
              refine ⟨2030918684663590442728921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2707891579551453923638561 2030918684663590442728921)
              ·
                refine ⟨1523189013497692832046691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2030918684663590442728921 1523189013497692832046691)
                ·
                  refine ⟨2284783520246539248070037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523189013497692832046691 2284783520246539248070037)
                  ·
                    refine ⟨107099227511556527253283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2284783520246539248070037 107099227511556527253283)
                    ·
                      rfl

theorem cell23_625725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 2, 1, 6].length) (baseStart_625725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625725 prefixEnd_625725 := by exact prefixLift 625725
  have htrace : WordTrace (prefixWord ++ tailWord_625725) baseStart_625725 baseEnd_625725 := by
    simpa [prefixWord, tailWord_625725, baseEnd_625725] using wordTrace_append hprefix tailTrace_625725
  have hstable : (prefixWord ++ tailWord_625725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625725).length < 2 ^ (prefixWord ++ tailWord_625725).sum := by decide
  have hdescent : baseEnd_625725 < baseStart_625725 := by decide
  rcases family_descends (prefixWord ++ tailWord_625725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625726 : List Nat := [4, 2, 1, 3, 1, 1, 1, 5, 1, 1, 3]
def baseStart_625726 : Nat := 118140960795 + 625726 * 2 ^ 59
def prefixEnd_625726 : Nat := 4983230072969 + 3 ^ 40 * 625726 * 2
def baseEnd_625726 : Nat := 321298196015324077847345

theorem tailTrace_625726 : CollatzResearch.WordTrace tailWord_625726 prefixEnd_625726 321298196015324077847345 := by
  unfold tailWord_625726
  simp only [CollatzResearch.WordTrace]
  refine ⟨2852762766388630292239129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15214734754072694891942021 2852762766388630292239129)
  ·
    refine ⟨2139572074791472719179347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2852762766388630292239129 2139572074791472719179347)
    ·
      refine ⟨3209358112187209078769021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2139572074791472719179347 3209358112187209078769021)
      ·
        refine ⟨1203509292070203404538383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3209358112187209078769021 1203509292070203404538383)
        ·
          refine ⟨1805263938105305106807575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203509292070203404538383 1805263938105305106807575)
          ·
            refine ⟨2707895907157957660211363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805263938105305106807575 2707895907157957660211363)
            ·
              refine ⟨4061843860736936490317045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2707895907157957660211363 4061843860736936490317045)
              ·
                refine ⟨380797861944087795967223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4061843860736936490317045 380797861944087795967223)
                ·
                  refine ⟨571196792916131693950835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380797861944087795967223 571196792916131693950835)
                  ·
                    refine ⟨856795189374197540926253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 571196792916131693950835 856795189374197540926253)
                    ·
                      refine ⟨321298196015324077847345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 856795189374197540926253 321298196015324077847345)
                      ·
                        rfl

theorem cell23_625726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_625726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625726 prefixEnd_625726 := by exact prefixLift 625726
  have htrace : WordTrace (prefixWord ++ tailWord_625726) baseStart_625726 baseEnd_625726 := by
    simpa [prefixWord, tailWord_625726, baseEnd_625726] using wordTrace_append hprefix tailTrace_625726
  have hstable : (prefixWord ++ tailWord_625726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625726).length < 2 ^ (prefixWord ++ tailWord_625726).sum := by decide
  have hdescent : baseEnd_625726 < baseStart_625726 := by decide
  rcases family_descends (prefixWord ++ tailWord_625726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625749 : List Nat := [1, 3, 2, 2, 1, 2, 4, 1, 3, 2, 2]
def baseStart_625749 : Nat := 118140960795 + 625749 * 2 ^ 59
def prefixEnd_625749 : Nat := 4983230072969 + 3 ^ 40 * 625749 * 2
def baseEnd_625749 : Nat := 321310006070377487859739

theorem tailTrace_625749 : CollatzResearch.WordTrace tailWord_625749 prefixEnd_625749 321310006070377487859739 := by
  unfold tailWord_625749
  simp only [CollatzResearch.WordTrace]
  refine ⟨22822941010025717266000301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15215294006683811510666867 22822941010025717266000301)
  ·
    refine ⟨8558602878759643974750113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22822941010025717266000301 8558602878759643974750113)
    ·
      refine ⟨6418952159069732981062585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8558602878759643974750113 6418952159069732981062585)
      ·
        refine ⟨4814214119302299735796939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6418952159069732981062585 4814214119302299735796939)
        ·
          refine ⟨7221321178953449603695409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4814214119302299735796939 7221321178953449603695409)
          ·
            refine ⟨5415990884215087202771557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7221321178953449603695409 5415990884215087202771557)
            ·
              refine ⟨1015498290790328850519667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5415990884215087202771557 1015498290790328850519667)
              ·
                refine ⟨1523247436185493275779501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015498290790328850519667 1523247436185493275779501)
                ·
                  refine ⟨571217788569559978417313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1523247436185493275779501 571217788569559978417313)
                  ·
                    refine ⟨428413341427169983812985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 571217788569559978417313 428413341427169983812985)
                    ·
                      refine ⟨321310006070377487859739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 428413341427169983812985 321310006070377487859739)
                      ·
                        rfl

theorem cell23_625749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_625749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625749 prefixEnd_625749 := by exact prefixLift 625749
  have htrace : WordTrace (prefixWord ++ tailWord_625749) baseStart_625749 baseEnd_625749 := by
    simpa [prefixWord, tailWord_625749, baseEnd_625749] using wordTrace_append hprefix tailTrace_625749
  have hstable : (prefixWord ++ tailWord_625749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625749).length < 2 ^ (prefixWord ++ tailWord_625749).sum := by decide
  have hdescent : baseEnd_625749 < baseStart_625749 := by decide
  rcases family_descends (prefixWord ++ tailWord_625749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625762 : List Nat := [3, 3, 2, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_625762 : Nat := 118140960795 + 625762 * 2 ^ 59
def prefixEnd_625762 : Nat := 4983230072969 + 3 ^ 40 * 625762 * 2
def baseEnd_625762 : Nat := 321316681318885936997179

theorem tailTrace_625762 : CollatzResearch.WordTrace tailWord_625762 prefixEnd_625762 321316681318885936997179 := by
  unfold tailWord_625762
  simp only [CollatzResearch.WordTrace]
  refine ⟨5705853789744655121555885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15215610105985746990815693 5705853789744655121555885)
  ·
    refine ⟨2139695171154245670583457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5705853789744655121555885 2139695171154245670583457)
    ·
      refine ⟨1604771378365684252937593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2139695171154245670583457 1604771378365684252937593)
      ·
        refine ⟨1203578533774263189703195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1604771378365684252937593 1203578533774263189703195)
        ·
          refine ⟨1805367800661394784554793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203578533774263189703195 1805367800661394784554793)
          ·
            refine ⟨1354025850496046088416095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1805367800661394784554793 1354025850496046088416095)
            ·
              refine ⟨2031038775744069132624143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354025850496046088416095 2031038775744069132624143)
              ·
                refine ⟨3046558163616103698936215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031038775744069132624143 3046558163616103698936215)
                ·
                  refine ⟨4569837245424155548404323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3046558163616103698936215 4569837245424155548404323)
                  ·
                    refine ⟨6854755868136233322606485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4569837245424155548404323 6854755868136233322606485)
                    ·
                      refine ⟨321316681318885936997179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6854755868136233322606485 321316681318885936997179)
                      ·
                        rfl

theorem cell23_625762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_625762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625762 prefixEnd_625762 := by exact prefixLift 625762
  have htrace : WordTrace (prefixWord ++ tailWord_625762) baseStart_625762 baseEnd_625762 := by
    simpa [prefixWord, tailWord_625762, baseEnd_625762] using wordTrace_append hprefix tailTrace_625762
  have hstable : (prefixWord ++ tailWord_625762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625762).length < 2 ^ (prefixWord ++ tailWord_625762).sum := by decide
  have hdescent : baseEnd_625762 < baseStart_625762 := by decide
  rcases family_descends (prefixWord ++ tailWord_625762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625782 : List Nat := [5, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_625782 : Nat := 118140960795 + 625782 * 2 ^ 59
def prefixEnd_625782 : Nat := 4983230072969 + 3 ^ 40 * 625782 * 2
def baseEnd_625782 : Nat := 321326950931975858747087

theorem tailTrace_625782 : CollatzResearch.WordTrace tailWord_625782 prefixEnd_625782 321326950931975858747087 := by
  unfold tailWord_625782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426509038681635243871975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15216096412604109267967733 1426509038681635243871975)
  ·
    refine ⟨2139763558022452865807963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1426509038681635243871975 2139763558022452865807963)
    ·
      refine ⟨3209645337033679298711945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2139763558022452865807963 3209645337033679298711945)
      ·
        refine ⟨2407234002775259474033959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3209645337033679298711945 2407234002775259474033959)
        ·
          refine ⟨3610851004162889211050939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407234002775259474033959 3610851004162889211050939)
          ·
            refine ⟨5416276506244333816576409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3610851004162889211050939 5416276506244333816576409)
            ·
              refine ⟨4062207379683250362432307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5416276506244333816576409 4062207379683250362432307)
              ·
                refine ⟨6093311069524875543648461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4062207379683250362432307 6093311069524875543648461)
                ·
                  refine ⟨2284991651071828328868173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6093311069524875543648461 2284991651071828328868173)
                  ·
                    refine ⟨856871869151935623325565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2284991651071828328868173 856871869151935623325565)
                    ·
                      refine ⟨321326950931975858747087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 856871869151935623325565 321326950931975858747087)
                      ·
                        rfl

theorem cell23_625782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_625782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625782 prefixEnd_625782 := by exact prefixLift 625782
  have htrace : WordTrace (prefixWord ++ tailWord_625782) baseStart_625782 baseEnd_625782 := by
    simpa [prefixWord, tailWord_625782, baseEnd_625782] using wordTrace_append hprefix tailTrace_625782
  have hstable : (prefixWord ++ tailWord_625782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625782).length < 2 ^ (prefixWord ++ tailWord_625782).sum := by decide
  have hdescent : baseEnd_625782 < baseStart_625782 := by decide
  rcases family_descends (prefixWord ++ tailWord_625782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625800 : List Nat := [2, 1, 3, 4, 2, 1, 3, 2, 1, 2, 2]
def baseStart_625800 : Nat := 118140960795 + 625800 * 2 ^ 59
def prefixEnd_625800 : Nat := 4983230072969 + 3 ^ 40 * 625800 * 2
def baseEnd_625800 : Nat := 321336193583756788322005

theorem tailTrace_625800 : CollatzResearch.WordTrace tailWord_625800 prefixEnd_625800 321336193583756788322005 := by
  unfold tailWord_625800
  simp only [CollatzResearch.WordTrace]
  refine ⟨11412400566420476488053427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15216534088560635317404569 11412400566420476488053427)
  ·
    refine ⟨17118600849630714732080141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11412400566420476488053427 17118600849630714732080141)
    ·
      refine ⟨6419475318611518024530053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17118600849630714732080141 6419475318611518024530053)
      ·
        refine ⟨1203651622239659629599385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6419475318611518024530053 1203651622239659629599385)
        ·
          refine ⟨902738716679744722199539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1203651622239659629599385 902738716679744722199539)
          ·
            refine ⟨1354108075019617083299309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902738716679744722199539 1354108075019617083299309)
            ·
              refine ⟨507790528132356406237241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1354108075019617083299309 507790528132356406237241)
              ·
                refine ⟨380842896099267304677931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507790528132356406237241 380842896099267304677931)
                ·
                  refine ⟨571264344148900957016897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380842896099267304677931 571264344148900957016897)
                  ·
                    refine ⟨428448258111675717762673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 571264344148900957016897 428448258111675717762673)
                    ·
                      refine ⟨321336193583756788322005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 428448258111675717762673 321336193583756788322005)
                      ·
                        rfl

theorem cell23_625800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 3, 2, 1, 2, 2].length) (baseStart_625800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625800 prefixEnd_625800 := by exact prefixLift 625800
  have htrace : WordTrace (prefixWord ++ tailWord_625800) baseStart_625800 baseEnd_625800 := by
    simpa [prefixWord, tailWord_625800, baseEnd_625800] using wordTrace_append hprefix tailTrace_625800
  have hstable : (prefixWord ++ tailWord_625800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625800).length < 2 ^ (prefixWord ++ tailWord_625800).sum := by decide
  have hdescent : baseEnd_625800 < baseStart_625800 := by decide
  rcases family_descends (prefixWord ++ tailWord_625800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625816 : List Nat := [2, 1, 2, 4, 2, 1, 4, 1, 2, 1, 3]
def baseStart_625816 : Nat := 118140960795 + 625816 * 2 ^ 59
def prefixEnd_625816 : Nat := 4983230072969 + 3 ^ 40 * 625816 * 2
def baseEnd_625816 : Nat := 321344409274228725721931

theorem tailTrace_625816 : CollatzResearch.WordTrace tailWord_625816 prefixEnd_625816 321344409274228725721931 := by
  unfold tailWord_625816
  simp only [CollatzResearch.WordTrace]
  refine ⟨11412692350391493854344651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15216923133855325139126201 11412692350391493854344651)
  ·
    refine ⟨17119038525587240781516977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11412692350391493854344651 17119038525587240781516977)
    ·
      refine ⟨12839278894190430586137733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17119038525587240781516977 12839278894190430586137733)
      ·
        refine ⟨2407364792660705734900825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12839278894190430586137733 2407364792660705734900825)
        ·
          refine ⟨1805523594495529301175619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2407364792660705734900825 1805523594495529301175619)
          ·
            refine ⟨2708285391743293951763429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805523594495529301175619 2708285391743293951763429)
            ·
              refine ⟨507803510951867615955643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2708285391743293951763429 507803510951867615955643)
              ·
                refine ⟨761705266427801423933465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507803510951867615955643 761705266427801423933465)
                ·
                  refine ⟨571278949820851067950099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 761705266427801423933465 571278949820851067950099)
                  ·
                    refine ⟨856918424731276601925149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 571278949820851067950099 856918424731276601925149)
                    ·
                      refine ⟨321344409274228725721931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 856918424731276601925149 321344409274228725721931)
                      ·
                        rfl

theorem cell23_625816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_625816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625816 prefixEnd_625816 := by exact prefixLift 625816
  have htrace : WordTrace (prefixWord ++ tailWord_625816) baseStart_625816 baseEnd_625816 := by
    simpa [prefixWord, tailWord_625816, baseEnd_625816] using wordTrace_append hprefix tailTrace_625816
  have hstable : (prefixWord ++ tailWord_625816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625816).length < 2 ^ (prefixWord ++ tailWord_625816).sum := by decide
  have hdescent : baseEnd_625816 < baseStart_625816 := by decide
  rcases family_descends (prefixWord ++ tailWord_625816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625825 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 4, 1, 5]
def baseStart_625825 : Nat := 118140960795 + 625825 * 2 ^ 59
def prefixEnd_625825 : Nat := 4983230072969 + 3 ^ 40 * 625825 * 2
def baseEnd_625825 : Nat := 321349030600119190509389

theorem tailTrace_625825 : CollatzResearch.WordTrace tailWord_625825 prefixEnd_625825 321349030600119190509389 := by
  unfold tailWord_625825
  simp only [CollatzResearch.WordTrace]
  refine ⟨22825712957750382245766929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15217141971833588163844619 22825712957750382245766929)
  ·
    refine ⟨17119284718312786684325197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22825712957750382245766929 17119284718312786684325197)
    ·
      refine ⟨6419731769367295006621949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17119284718312786684325197 6419731769367295006621949)
      ·
        refine ⟨2407399413512735627483231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6419731769367295006621949 2407399413512735627483231)
        ·
          refine ⟨3611099120269103441224847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407399413512735627483231 3611099120269103441224847)
          ·
            refine ⟨5416648680403655161837271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611099120269103441224847 5416648680403655161837271)
            ·
              refine ⟨8124973020605482742755907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5416648680403655161837271 8124973020605482742755907)
              ·
                refine ⟨12187459530908224114133861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8124973020605482742755907 12187459530908224114133861)
                ·
                  refine ⟨2285148662045292021400099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12187459530908224114133861 2285148662045292021400099)
                  ·
                    refine ⟨3427722993067938032100149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2285148662045292021400099 3427722993067938032100149)
                    ·
                      refine ⟨321349030600119190509389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3427722993067938032100149 321349030600119190509389)
                      ·
                        rfl

theorem cell23_625825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 4, 1, 5].length) (baseStart_625825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625825 prefixEnd_625825 := by exact prefixLift 625825
  have htrace : WordTrace (prefixWord ++ tailWord_625825) baseStart_625825 baseEnd_625825 := by
    simpa [prefixWord, tailWord_625825, baseEnd_625825] using wordTrace_append hprefix tailTrace_625825
  have hstable : (prefixWord ++ tailWord_625825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625825).length < 2 ^ (prefixWord ++ tailWord_625825).sum := by decide
  have hdescent : baseEnd_625825 < baseStart_625825 := by decide
  rcases family_descends (prefixWord ++ tailWord_625825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625826 : List Nat := [3, 3, 1, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_625826 : Nat := 118140960795 + 625826 * 2 ^ 59
def prefixEnd_625826 : Nat := 4983230072969 + 3 ^ 40 * 625826 * 2
def baseEnd_625826 : Nat := 321349544080773686596885

theorem tailTrace_625826 : CollatzResearch.WordTrace tailWord_625826 prefixEnd_625826 321349544080773686596885 := by
  unfold tailWord_625826
  simp only [CollatzResearch.WordTrace]
  refine ⟨5706437357686689854138333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15217166287164506277702221 5706437357686689854138333)
  ·
    refine ⟨2139914009132508695301875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5706437357686689854138333 2139914009132508695301875)
    ·
      refine ⟨3209871013698763042952813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2139914009132508695301875 3209871013698763042952813)
      ·
        refine ⟨1203701630137036141107305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3209871013698763042952813 1203701630137036141107305)
        ·
          refine ⟨902776222602777105830479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1203701630137036141107305 902776222602777105830479)
          ·
            refine ⟨1354164333904165658745719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902776222602777105830479 1354164333904165658745719)
            ·
              refine ⟨2031246500856248488118579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354164333904165658745719 2031246500856248488118579)
              ·
                refine ⟨3046869751284372732177869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031246500856248488118579 3046869751284372732177869)
                ·
                  refine ⟨1142576156731639774566701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3046869751284372732177869 1142576156731639774566701)
                  ·
                    refine ⟨428466058774364915462513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1142576156731639774566701 428466058774364915462513)
                    ·
                      refine ⟨321349544080773686596885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 428466058774364915462513 321349544080773686596885)
                      ·
                        rfl

theorem cell23_625826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_625826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625826 prefixEnd_625826 := by exact prefixLift 625826
  have htrace : WordTrace (prefixWord ++ tailWord_625826) baseStart_625826 baseEnd_625826 := by
    simpa [prefixWord, tailWord_625826, baseEnd_625826] using wordTrace_append hprefix tailTrace_625826
  have hstable : (prefixWord ++ tailWord_625826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625826).length < 2 ^ (prefixWord ++ tailWord_625826).sum := by decide
  have hdescent : baseEnd_625826 < baseStart_625826 := by decide
  rcases family_descends (prefixWord ++ tailWord_625826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625882 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2]
def baseStart_625882 : Nat := 118140960795 + 625882 * 2 ^ 59
def prefixEnd_625882 : Nat := 4983230072969 + 3 ^ 40 * 625882 * 2
def baseEnd_625882 : Nat := 321378298997425467496627

theorem tailTrace_625882 : CollatzResearch.WordTrace tailWord_625882 prefixEnd_625882 321378298997425467496627 := by
  unfold tailWord_625882
  simp only [CollatzResearch.WordTrace]
  refine ⟨5706947979635970245147975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15218527945695920653727933 5706947979635970245147975)
  ·
    refine ⟨8560421969453955367721963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5706947979635970245147975 8560421969453955367721963)
    ·
      refine ⟨12840632954180933051582945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8560421969453955367721963 12840632954180933051582945)
      ·
        refine ⟨9630474715635699788687209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12840632954180933051582945 9630474715635699788687209)
        ·
          refine ⟨7222856036726774841515407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9630474715635699788687209 7222856036726774841515407)
          ·
            refine ⟨10834284055090162262273111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7222856036726774841515407 10834284055090162262273111)
            ·
              refine ⟨16251426082635243393409667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10834284055090162262273111 16251426082635243393409667)
              ·
                refine ⟨24377139123952865090114501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16251426082635243393409667 24377139123952865090114501)
                ·
                  refine ⟨4570713585741162204396469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24377139123952865090114501 4570713585741162204396469)
                  ·
                    refine ⟨428504398663233956662169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4570713585741162204396469 428504398663233956662169)
                    ·
                      refine ⟨321378298997425467496627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 428504398663233956662169 321378298997425467496627)
                      ·
                        rfl

theorem cell23_625882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 2].length) (baseStart_625882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625882 prefixEnd_625882 := by exact prefixLift 625882
  have htrace : WordTrace (prefixWord ++ tailWord_625882) baseStart_625882 baseEnd_625882 := by
    simpa [prefixWord, tailWord_625882, baseEnd_625882] using wordTrace_append hprefix tailTrace_625882
  have hstable : (prefixWord ++ tailWord_625882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625882).length < 2 ^ (prefixWord ++ tailWord_625882).sum := by decide
  have hdescent : baseEnd_625882 < baseStart_625882 := by decide
  rcases family_descends (prefixWord ++ tailWord_625882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625892 : List Nat := [2, 3, 1, 1, 1, 2, 5, 1, 2, 5]
def baseStart_625892 : Nat := 118140960795 + 625892 * 2 ^ 59
def prefixEnd_625892 : Nat := 4983230072969 + 3 ^ 40 * 625892 * 2
def baseEnd_625892 : Nat := 107127811267990142790527

theorem tailTrace_625892 : CollatzResearch.WordTrace tailWord_625892 prefixEnd_625892 107127811267990142790527 := by
  unfold tailWord_625892
  simp only [CollatzResearch.WordTrace]
  refine ⟨11414078324253826344227965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15218771099005101792303953 11414078324253826344227965)
  ·
    refine ⟨4280279371595184879085487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11414078324253826344227965 4280279371595184879085487)
    ·
      refine ⟨6420419057392777318628231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4280279371595184879085487 6420419057392777318628231)
      ·
        refine ⟨9630628586089165977942347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6420419057392777318628231 9630628586089165977942347)
        ·
          refine ⟨14445942879133748966913521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9630628586089165977942347 14445942879133748966913521)
          ·
            refine ⟨10834457159350311725185141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14445942879133748966913521 10834457159350311725185141)
            ·
              refine ⟨1015730358689091724236107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10834457159350311725185141 1015730358689091724236107)
              ·
                refine ⟨1523595538033637586354161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015730358689091724236107 1523595538033637586354161)
                ·
                  refine ⟨1142696653525228189765621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1523595538033637586354161 1142696653525228189765621)
                  ·
                    refine ⟨107127811267990142790527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1142696653525228189765621 107127811267990142790527)
                    ·
                      rfl

theorem cell23_625892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 2, 5].length) (baseStart_625892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625892 prefixEnd_625892 := by exact prefixLift 625892
  have htrace : WordTrace (prefixWord ++ tailWord_625892) baseStart_625892 baseEnd_625892 := by
    simpa [prefixWord, tailWord_625892, baseEnd_625892] using wordTrace_append hprefix tailTrace_625892
  have hstable : (prefixWord ++ tailWord_625892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625892).length < 2 ^ (prefixWord ++ tailWord_625892).sum := by decide
  have hdescent : baseEnd_625892 < baseStart_625892 := by decide
  rcases family_descends (prefixWord ++ tailWord_625892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625925 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 6]
def baseStart_625925 : Nat := 118140960795 + 625925 * 2 ^ 59
def prefixEnd_625925 : Nat := 4983230072969 + 3 ^ 40 * 625925 * 2
def baseEnd_625925 : Nat := 321400378665568799258929

theorem tailTrace_625925 : CollatzResearch.WordTrace tailWord_625925 prefixEnd_625925 321400378665568799258929 := by
  unfold tailWord_625925
  simp only [CollatzResearch.WordTrace]
  refine ⟨22829360257388099324407229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15219573504925399549604819 22829360257388099324407229)
  ·
    refine ⟨8561010096520537246652711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22829360257388099324407229 8561010096520537246652711)
    ·
      refine ⟨12841515144780805869979067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8561010096520537246652711 12841515144780805869979067)
      ·
        refine ⟨19262272717171208804968601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12841515144780805869979067 19262272717171208804968601)
        ·
          refine ⟨14446704537878406603726451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19262272717171208804968601 14446704537878406603726451)
          ·
            refine ⟨21670056806817609905589677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14446704537878406603726451 21670056806817609905589677)
            ·
              refine ⟨8126271302556603714596129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21670056806817609905589677 8126271302556603714596129)
              ·
                refine ⟨6094703476917452785947097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8126271302556603714596129 6094703476917452785947097)
                ·
                  refine ⟨4571027607688089589460323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6094703476917452785947097 4571027607688089589460323)
                  ·
                    refine ⟨6856541411532134384190485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4571027607688089589460323 6856541411532134384190485)
                    ·
                      refine ⟨321400378665568799258929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6856541411532134384190485 321400378665568799258929)
                      ·
                        rfl

theorem cell23_625925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_625925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625925 prefixEnd_625925 := by exact prefixLift 625925
  have htrace : WordTrace (prefixWord ++ tailWord_625925) baseStart_625925 baseEnd_625925 := by
    simpa [prefixWord, tailWord_625925, baseEnd_625925] using wordTrace_append hprefix tailTrace_625925
  have hstable : (prefixWord ++ tailWord_625925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625925).length < 2 ^ (prefixWord ++ tailWord_625925).sum := by decide
  have hdescent : baseEnd_625925 < baseStart_625925 := by decide
  rcases family_descends (prefixWord ++ tailWord_625925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625932 : List Nat := [2, 2, 1, 2, 2, 3, 1, 2, 1, 4, 3]
def baseStart_625932 : Nat := 118140960795 + 625932 * 2 ^ 59
def prefixEnd_625932 : Nat := 4983230072969 + 3 ^ 40 * 625932 * 2
def baseEnd_625932 : Nat := 321403973030150271871397

theorem tailTrace_625932 : CollatzResearch.WordTrace tailWord_625932 prefixEnd_625932 321403973030150271871397 := by
  unfold tailWord_625932
  simp only [CollatzResearch.WordTrace]
  refine ⟨11414807784181369759956025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15219743712241826346608033 11414807784181369759956025)
  ·
    refine ⟨8561105838136027319967019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11414807784181369759956025 8561105838136027319967019)
    ·
      refine ⟨12841658757204040979950529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8561105838136027319967019 12841658757204040979950529)
      ·
        refine ⟨9631244067903030734962897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12841658757204040979950529 9631244067903030734962897)
        ·
          refine ⟨7223433050927273051222173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9631244067903030734962897 7223433050927273051222173)
          ·
            refine ⟨2708787394097727394208315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7223433050927273051222173 2708787394097727394208315)
            ·
              refine ⟨4063181091146591091312473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2708787394097727394208315 4063181091146591091312473)
              ·
                refine ⟨3047385818359943318484355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4063181091146591091312473 3047385818359943318484355)
                ·
                  refine ⟨4571078727539914977726533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047385818359943318484355 4571078727539914977726533)
                  ·
                    refine ⟨857077261413734058323725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4571078727539914977726533 857077261413734058323725)
                    ·
                      refine ⟨321403973030150271871397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 857077261413734058323725 321403973030150271871397)
                      ·
                        rfl

theorem cell23_625932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 2, 1, 4, 3].length) (baseStart_625932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625932 prefixEnd_625932 := by exact prefixLift 625932
  have htrace : WordTrace (prefixWord ++ tailWord_625932) baseStart_625932 baseEnd_625932 := by
    simpa [prefixWord, tailWord_625932, baseEnd_625932] using wordTrace_append hprefix tailTrace_625932
  have hstable : (prefixWord ++ tailWord_625932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625932).length < 2 ^ (prefixWord ++ tailWord_625932).sum := by decide
  have hdescent : baseEnd_625932 < baseStart_625932 := by decide
  rcases family_descends (prefixWord ++ tailWord_625932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625949 : List Nat := [1, 4, 2, 3, 1, 1, 2, 1, 1, 4, 3]
def baseStart_625949 : Nat := 118140960795 + 625949 * 2 ^ 59
def prefixEnd_625949 : Nat := 4983230072969 + 3 ^ 40 * 625949 * 2
def baseEnd_625949 : Nat := 321412702201276705358819

theorem tailTrace_625949 : CollatzResearch.WordTrace tailWord_625949 prefixEnd_625949 321412702201276705358819 := by
  unfold tailWord_625949
  simp only [CollatzResearch.WordTrace]
  refine ⟨22830235609301151423280901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15220157072867434282187267 22830235609301151423280901)
  ·
    refine ⟨4280669176743965891865169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22830235609301151423280901 4280669176743965891865169)
    ·
      refine ⟨3210501882557974418898877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4280669176743965891865169 3210501882557974418898877)
      ·
        refine ⟨1203938205959240407087079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3210501882557974418898877 1203938205959240407087079)
        ·
          refine ⟨1805907308938860610630619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203938205959240407087079 1805907308938860610630619)
          ·
            refine ⟨2708860963408290915945929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805907308938860610630619 2708860963408290915945929)
            ·
              refine ⟨2031645722556218186959447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2708860963408290915945929 2031645722556218186959447)
              ·
                refine ⟨3047468583834327280439171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031645722556218186959447 3047468583834327280439171)
                ·
                  refine ⟨4571202875751490920658757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047468583834327280439171 4571202875751490920658757)
                  ·
                    refine ⟨857100539203404547623517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4571202875751490920658757 857100539203404547623517)
                    ·
                      refine ⟨321412702201276705358819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 857100539203404547623517 321412702201276705358819)
                      ·
                        rfl

theorem cell23_625949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_625949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625949 prefixEnd_625949 := by exact prefixLift 625949
  have htrace : WordTrace (prefixWord ++ tailWord_625949) baseStart_625949 baseEnd_625949 := by
    simpa [prefixWord, tailWord_625949, baseEnd_625949] using wordTrace_append hprefix tailTrace_625949
  have hstable : (prefixWord ++ tailWord_625949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625949).length < 2 ^ (prefixWord ++ tailWord_625949).sum := by decide
  have hdescent : baseEnd_625949 < baseStart_625949 := by decide
  rcases family_descends (prefixWord ++ tailWord_625949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625973 : List Nat := [1, 3, 3, 1, 2, 3, 3, 2, 1, 4]
def baseStart_625973 : Nat := 118140960795 + 625973 * 2 ^ 59
def prefixEnd_625973 : Nat := 4983230072969 + 3 ^ 40 * 625973 * 2
def baseEnd_625973 : Nat := 107141675245661537152903

theorem tailTrace_625973 : CollatzResearch.WordTrace tailWord_625973 prefixEnd_625973 107141675245661537152903 := by
  unfold tailWord_625973
  simp only [CollatzResearch.WordTrace]
  refine ⟨22831110961214203522154573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15220740640809469014769715 22831110961214203522154573)
  ·
    refine ⟨8561666610455326320807965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22831110961214203522154573 8561666610455326320807965)
    ·
      refine ⟨3210624978920747370302987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8561666610455326320807965 3210624978920747370302987)
      ·
        refine ⟨4815937468381121055454481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3210624978920747370302987 4815937468381121055454481)
        ·
          refine ⟨3611953101285840791590861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4815937468381121055454481 3611953101285840791590861)
          ·
            refine ⟨1354482412982190296846573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3611953101285840791590861 1354482412982190296846573)
            ·
              refine ⟨507930904868321361317465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1354482412982190296846573 507930904868321361317465)
              ·
                refine ⟨380948178651241020988099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 507930904868321361317465 380948178651241020988099)
                ·
                  refine ⟨571422267976861531482149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380948178651241020988099 571422267976861531482149)
                  ·
                    refine ⟨107141675245661537152903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 571422267976861531482149 107141675245661537152903)
                    ·
                      rfl

theorem cell23_625973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_625973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625973 prefixEnd_625973 := by exact prefixLift 625973
  have htrace : WordTrace (prefixWord ++ tailWord_625973) baseStart_625973 baseEnd_625973 := by
    simpa [prefixWord, tailWord_625973, baseEnd_625973] using wordTrace_append hprefix tailTrace_625973
  have hstable : (prefixWord ++ tailWord_625973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625973).length < 2 ^ (prefixWord ++ tailWord_625973).sum := by decide
  have hdescent : baseEnd_625973 < baseStart_625973 := by decide
  rcases family_descends (prefixWord ++ tailWord_625973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_625975 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_625975 : Nat := 118140960795 + 625975 * 2 ^ 59
def prefixEnd_625975 : Nat := 4983230072969 + 3 ^ 40 * 625975 * 2
def baseEnd_625975 : Nat := 321426052698293603633699

theorem tailTrace_625975 : CollatzResearch.WordTrace tailWord_625975 prefixEnd_625975 321426052698293603633699 := by
  unfold tailWord_625975
  simp only [CollatzResearch.WordTrace]
  refine ⟨22831183907206957863727379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15220789271471305242484919 22831183907206957863727379)
  ·
    refine ⟨34246775860810436795591069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22831183907206957863727379 34246775860810436795591069)
    ·
      refine ⟨12842540947803913798346651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34246775860810436795591069 12842540947803913798346651)
      ·
        refine ⟨19263811421705870697519977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12842540947803913798346651 19263811421705870697519977)
        ·
          refine ⟨14447858566279403023139983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19263811421705870697519977 14447858566279403023139983)
          ·
            refine ⟨21671787849419104534709975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14447858566279403023139983 21671787849419104534709975)
            ·
              refine ⟨32507681774128656802064963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21671787849419104534709975 32507681774128656802064963)
              ·
                refine ⟨48761522661192985203097445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32507681774128656802064963 48761522661192985203097445)
                ·
                  refine ⟨9142785498973684725580771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48761522661192985203097445 9142785498973684725580771)
                  ·
                    refine ⟨13714178248460527088371157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9142785498973684725580771 13714178248460527088371157)
                    ·
                      refine ⟨321426052698293603633699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13714178248460527088371157 321426052698293603633699)
                      ·
                        rfl

theorem cell23_625975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_625975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_625975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_625975 prefixEnd_625975 := by exact prefixLift 625975
  have htrace : WordTrace (prefixWord ++ tailWord_625975) baseStart_625975 baseEnd_625975 := by
    simpa [prefixWord, tailWord_625975, baseEnd_625975] using wordTrace_append hprefix tailTrace_625975
  have hstable : (prefixWord ++ tailWord_625975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_625975).length < 2 ^ (prefixWord ++ tailWord_625975).sum := by decide
  have hdescent : baseEnd_625975 < baseStart_625975 := by decide
  rcases family_descends (prefixWord ++ tailWord_625975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626016 : List Nat := [2, 1, 1, 3, 4, 2, 3, 1, 1, 5]
def baseStart_626016 : Nat := 118140960795 + 626016 * 2 ^ 59
def prefixEnd_626016 : Nat := 4983230072969 + 3 ^ 40 * 626016 * 2
def baseEnd_626016 : Nat := 107149035135042647740337

theorem tailTrace_626016 : CollatzResearch.WordTrace tailWord_626016 prefixEnd_626016 107149035135042647740337 := by
  unfold tailWord_626016
  simp only [CollatzResearch.WordTrace]
  refine ⟨11416339650029210932984951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15221786200038947910646601 11416339650029210932984951)
  ·
    refine ⟨17124509475043816399477427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11416339650029210932984951 17124509475043816399477427)
    ·
      refine ⟨25686764212565724599216141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17124509475043816399477427 25686764212565724599216141)
      ·
        refine ⟨9632536579712146724706053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25686764212565724599216141 9632536579712146724706053)
        ·
          refine ⟨1806100608696027510882385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9632536579712146724706053 1806100608696027510882385)
          ·
            refine ⟨1354575456522020633161789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1806100608696027510882385 1354575456522020633161789)
            ·
              refine ⟨507965796195757737435671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1354575456522020633161789 507965796195757737435671)
              ·
                refine ⟨761948694293636606153507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 507965796195757737435671 761948694293636606153507)
                ·
                  refine ⟨1142923041440454909230261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761948694293636606153507 1142923041440454909230261)
                  ·
                    refine ⟨107149035135042647740337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1142923041440454909230261 107149035135042647740337)
                    ·
                      rfl

theorem cell23_626016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 3, 1, 1, 5].length) (baseStart_626016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626016 prefixEnd_626016 := by exact prefixLift 626016
  have htrace : WordTrace (prefixWord ++ tailWord_626016) baseStart_626016 baseEnd_626016 := by
    simpa [prefixWord, tailWord_626016, baseEnd_626016] using wordTrace_append hprefix tailTrace_626016
  have hstable : (prefixWord ++ tailWord_626016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626016).length < 2 ^ (prefixWord ++ tailWord_626016).sum := by decide
  have hdescent : baseEnd_626016 < baseStart_626016 := by decide
  rcases family_descends (prefixWord ++ tailWord_626016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626032 : List Nat := [2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 4]
def baseStart_626032 : Nat := 118140960795 + 626032 * 2 ^ 59
def prefixEnd_626032 : Nat := 4983230072969 + 3 ^ 40 * 626032 * 2
def baseEnd_626032 : Nat := 321455321095599880620937

theorem tailTrace_626032 : CollatzResearch.WordTrace tailWord_626032 prefixEnd_626032 321455321095599880620937 := by
  unfold tailWord_626032
  simp only [CollatzResearch.WordTrace]
  refine ⟨11416631434000228299276175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15222175245333637732368233 11416631434000228299276175)
  ·
    refine ⟨17124947151000342448914263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11416631434000228299276175 17124947151000342448914263)
    ·
      refine ⟨25687420726500513673371395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17124947151000342448914263 25687420726500513673371395)
      ·
        refine ⟨38531131089750770510057093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25687420726500513673371395 38531131089750770510057093)
        ·
          refine ⟨7224587079328269470635705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38531131089750770510057093 7224587079328269470635705)
          ·
            refine ⟨5418440309496202102976779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7224587079328269470635705 5418440309496202102976779)
            ·
              refine ⟨8127660464244303154465169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5418440309496202102976779 8127660464244303154465169)
              ·
                refine ⟨6095745348183227365848877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8127660464244303154465169 6095745348183227365848877)
                ·
                  refine ⟨2285904505568710262193329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6095745348183227365848877 2285904505568710262193329)
                  ·
                    refine ⟨1714428379176532696644997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2285904505568710262193329 1714428379176532696644997)
                    ·
                      refine ⟨321455321095599880620937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1714428379176532696644997 321455321095599880620937)
                      ·
                        rfl

theorem cell23_626032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 4].length) (baseStart_626032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626032 prefixEnd_626032 := by exact prefixLift 626032
  have htrace : WordTrace (prefixWord ++ tailWord_626032) baseStart_626032 baseEnd_626032 := by
    simpa [prefixWord, tailWord_626032, baseEnd_626032] using wordTrace_append hprefix tailTrace_626032
  have hstable : (prefixWord ++ tailWord_626032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626032).length < 2 ^ (prefixWord ++ tailWord_626032).sum := by decide
  have hdescent : baseEnd_626032 < baseStart_626032 := by decide
  rcases family_descends (prefixWord ++ tailWord_626032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626069 : List Nat := [1, 3, 2, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_626069 : Nat := 118140960795 + 626069 * 2 ^ 59
def prefixEnd_626069 : Nat := 4983230072969 + 3 ^ 40 * 626069 * 2
def baseEnd_626069 : Nat := 321474319879816235858267

theorem tailTrace_626069 : CollatzResearch.WordTrace tailWord_626069 prefixEnd_626069 321474319879816235858267 := by
  unfold tailWord_626069
  simp only [CollatzResearch.WordTrace]
  refine ⟨22834612368866411917649261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15223074912577607945099507 22834612368866411917649261)
  ·
    refine ⟨8562979638324904469118473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22834612368866411917649261 8562979638324904469118473)
    ·
      refine ⟨6422234728743678351838855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8562979638324904469118473 6422234728743678351838855)
      ·
        refine ⟨9633352093115517527758283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6422234728743678351838855 9633352093115517527758283)
        ·
          refine ⟨14450028139673276291637425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9633352093115517527758283 14450028139673276291637425)
          ·
            refine ⟨10837521104754957218728069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14450028139673276291637425 10837521104754957218728069)
            ·
              refine ⟨2032035207141554478511513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10837521104754957218728069 2032035207141554478511513)
              ·
                refine ⟨1524026405356165858883635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2032035207141554478511513 1524026405356165858883635)
                ·
                  refine ⟨2286039608034248788325453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524026405356165858883635 2286039608034248788325453)
                  ·
                    refine ⟨857264853012843295622045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2286039608034248788325453 857264853012843295622045)
                    ·
                      refine ⟨321474319879816235858267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 857264853012843295622045 321474319879816235858267)
                      ·
                        rfl

theorem cell23_626069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_626069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626069 prefixEnd_626069 := by exact prefixLift 626069
  have htrace : WordTrace (prefixWord ++ tailWord_626069) baseStart_626069 baseEnd_626069 := by
    simpa [prefixWord, tailWord_626069, baseEnd_626069] using wordTrace_append hprefix tailTrace_626069
  have hstable : (prefixWord ++ tailWord_626069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626069).length < 2 ^ (prefixWord ++ tailWord_626069).sum := by decide
  have hdescent : baseEnd_626069 < baseStart_626069 := by decide
  rcases family_descends (prefixWord ++ tailWord_626069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626073 : List Nat := [1, 2, 1, 2, 1, 7, 2, 1, 1, 2, 3]
def baseStart_626073 : Nat := 118140960795 + 626073 * 2 ^ 59
def prefixEnd_626073 : Nat := 4983230072969 + 3 ^ 40 * 626073 * 2
def baseEnd_626073 : Nat := 321476373802434220208249

theorem tailTrace_626073 : CollatzResearch.WordTrace tailWord_626073 prefixEnd_626073 321476373802434220208249 := by
  unfold tailWord_626073
  simp only [CollatzResearch.WordTrace]
  refine ⟨22834758260851920600794873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15223172173901280400529915 22834758260851920600794873)
  ·
    refine ⟨17126068695638940450596155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22834758260851920600794873 17126068695638940450596155)
    ·
      refine ⟨25689103043458410675894233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17126068695638940450596155 25689103043458410675894233)
      ·
        refine ⟨19266827282593808006920675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25689103043458410675894233 19266827282593808006920675)
        ·
          refine ⟨28900240923890712010381013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19266827282593808006920675 28900240923890712010381013)
          ·
            refine ⟨677349396653688562743305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 28900240923890712010381013 677349396653688562743305)
            ·
              refine ⟨508012047490266422057479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677349396653688562743305 508012047490266422057479)
              ·
                refine ⟨762018071235399633086219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508012047490266422057479 762018071235399633086219)
                ·
                  refine ⟨1143027106853099449629329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762018071235399633086219 1143027106853099449629329)
                  ·
                    refine ⟨857270330139824587221997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1143027106853099449629329 857270330139824587221997)
                    ·
                      refine ⟨321476373802434220208249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 857270330139824587221997 321476373802434220208249)
                      ·
                        rfl

theorem cell23_626073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 1, 2, 3].length) (baseStart_626073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626073 prefixEnd_626073 := by exact prefixLift 626073
  have htrace : WordTrace (prefixWord ++ tailWord_626073) baseStart_626073 baseEnd_626073 := by
    simpa [prefixWord, tailWord_626073, baseEnd_626073] using wordTrace_append hprefix tailTrace_626073
  have hstable : (prefixWord ++ tailWord_626073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626073).length < 2 ^ (prefixWord ++ tailWord_626073).sum := by decide
  have hdescent : baseEnd_626073 < baseStart_626073 := by decide
  rcases family_descends (prefixWord ++ tailWord_626073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626092 : List Nat := [2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 4]
def baseStart_626092 : Nat := 118140960795 + 626092 * 2 ^ 59
def prefixEnd_626092 : Nat := 4983230072969 + 3 ^ 40 * 626092 * 2
def baseEnd_626092 : Nat := 321486129934869645870661

theorem tailTrace_626092 : CollatzResearch.WordTrace tailWord_626092 prefixEnd_626092 321486129934869645870661 := by
  unfold tailWord_626092
  simp only [CollatzResearch.WordTrace]
  refine ⟨11417725623891543422868265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15223634165188724563824353 11417725623891543422868265)
  ·
    refine ⟨8563294217918657567151199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11417725623891543422868265 8563294217918657567151199)
    ·
      refine ⟨12844941326877986350726799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8563294217918657567151199 12844941326877986350726799)
      ·
        refine ⟨19267411990316979526090199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12844941326877986350726799 19267411990316979526090199)
        ·
          refine ⟨28901117985475469289135299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19267411990316979526090199 28901117985475469289135299)
          ·
            refine ⟨43351676978213203933702949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28901117985475469289135299 43351676978213203933702949)
            ·
              refine ⟨8128439433414975737569303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43351676978213203933702949 8128439433414975737569303)
              ·
                refine ⟨12192659150122463606353955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8128439433414975737569303 12192659150122463606353955)
                ·
                  refine ⟨18288988725183695409530933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12192659150122463606353955 18288988725183695409530933)
                  ·
                    refine ⟨1714592692985971444643525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18288988725183695409530933 1714592692985971444643525)
                    ·
                      refine ⟨321486129934869645870661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1714592692985971444643525 321486129934869645870661)
                      ·
                        rfl

theorem cell23_626092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 4].length) (baseStart_626092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626092 prefixEnd_626092 := by exact prefixLift 626092
  have htrace : WordTrace (prefixWord ++ tailWord_626092) baseStart_626092 baseEnd_626092 := by
    simpa [prefixWord, tailWord_626092, baseEnd_626092] using wordTrace_append hprefix tailTrace_626092
  have hstable : (prefixWord ++ tailWord_626092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626092).length < 2 ^ (prefixWord ++ tailWord_626092).sum := by decide
  have hdescent : baseEnd_626092 < baseStart_626092 := by decide
  rcases family_descends (prefixWord ++ tailWord_626092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626103 : List Nat := [1, 1, 3, 1, 3, 2, 5, 1, 2, 1, 3]
def baseStart_626103 : Nat := 118140960795 + 626103 * 2 ^ 59
def prefixEnd_626103 : Nat := 4983230072969 + 3 ^ 40 * 626103 * 2
def baseEnd_626103 : Nat := 321491778222069102833111

theorem tailTrace_626103 : CollatzResearch.WordTrace tailWord_626103 prefixEnd_626103 321491778222069102833111 := by
  unfold tailWord_626103
  simp only [CollatzResearch.WordTrace]
  refine ⟨22835852450743235724386963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15223901633828823816257975 22835852450743235724386963)
  ·
    refine ⟨34253778676114853586580445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22835852450743235724386963 34253778676114853586580445)
    ·
      refine ⟨12845167003543070094967667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34253778676114853586580445 12845167003543070094967667)
      ·
        refine ⟨19267750505314605142451501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12845167003543070094967667 19267750505314605142451501)
        ·
          refine ⟨7225406439492976928419313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19267750505314605142451501 7225406439492976928419313)
          ·
            refine ⟨5419054829619732696314485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7225406439492976928419313 5419054829619732696314485)
            ·
              refine ⟨508036390276849940279483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5419054829619732696314485 508036390276849940279483)
              ·
                refine ⟨762054585415274910419225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508036390276849940279483 762054585415274910419225)
                ·
                  refine ⟨571540939061456182814419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 762054585415274910419225 571540939061456182814419)
                  ·
                    refine ⟨857311408592184274221629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 571540939061456182814419 857311408592184274221629)
                    ·
                      refine ⟨321491778222069102833111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 857311408592184274221629 321491778222069102833111)
                      ·
                        rfl

theorem cell23_626103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 5, 1, 2, 1, 3].length) (baseStart_626103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626103 prefixEnd_626103 := by exact prefixLift 626103
  have htrace : WordTrace (prefixWord ++ tailWord_626103) baseStart_626103 baseEnd_626103 := by
    simpa [prefixWord, tailWord_626103, baseEnd_626103] using wordTrace_append hprefix tailTrace_626103
  have hstable : (prefixWord ++ tailWord_626103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626103).length < 2 ^ (prefixWord ++ tailWord_626103).sum := by decide
  have hdescent : baseEnd_626103 < baseStart_626103 := by decide
  rcases family_descends (prefixWord ++ tailWord_626103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626126 : List Nat := [4, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2]
def baseStart_626126 : Nat := 118140960795 + 626126 * 2 ^ 59
def prefixEnd_626126 : Nat := 4983230072969 + 3 ^ 40 * 626126 * 2
def baseEnd_626126 : Nat := 321503588277122512845505

theorem tailTrace_626126 : CollatzResearch.WordTrace tailWord_626126 prefixEnd_626126 321503588277122512845505 := by
  unfold tailWord_626126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2854586416207488831559279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15224460886439940434982821 2854586416207488831559279)
  ·
    refine ⟨4281879624311233247338919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2854586416207488831559279 4281879624311233247338919)
    ·
      refine ⟨6422819436466849871008379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4281879624311233247338919 6422819436466849871008379)
      ·
        refine ⟨9634229154700274806512569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6422819436466849871008379 9634229154700274806512569)
        ·
          refine ⟨7225671866025206104884427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9634229154700274806512569 7225671866025206104884427)
          ·
            refine ⟨10838507799037809157326641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7225671866025206104884427 10838507799037809157326641)
            ·
              refine ⟨8128880849278356867994981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10838507799037809157326641 8128880849278356867994981)
              ·
                refine ⟨1524165159239691912749059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8128880849278356867994981 1524165159239691912749059)
                ·
                  refine ⟨2286247738859537869123589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524165159239691912749059 2286247738859537869123589)
                  ·
                    refine ⟨428671451036163350460673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2286247738859537869123589 428671451036163350460673)
                    ·
                      refine ⟨321503588277122512845505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 428671451036163350460673 321503588277122512845505)
                      ·
                        rfl

theorem cell23_626126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2].length) (baseStart_626126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626126 prefixEnd_626126 := by exact prefixLift 626126
  have htrace : WordTrace (prefixWord ++ tailWord_626126) baseStart_626126 baseEnd_626126 := by
    simpa [prefixWord, tailWord_626126, baseEnd_626126] using wordTrace_append hprefix tailTrace_626126
  have hstable : (prefixWord ++ tailWord_626126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626126).length < 2 ^ (prefixWord ++ tailWord_626126).sum := by decide
  have hdescent : baseEnd_626126 < baseStart_626126 := by decide
  rcases family_descends (prefixWord ++ tailWord_626126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626143 : List Nat := [1, 1, 2, 3, 3, 1, 2, 4, 2, 2, 2]
def baseStart_626143 : Nat := 118140960795 + 626143 * 2 ^ 59
def prefixEnd_626143 : Nat := 4983230072969 + 3 ^ 40 * 626143 * 2
def baseEnd_626143 : Nat := 321512317448248946332927

theorem tailTrace_626143 : CollatzResearch.WordTrace tailWord_626143 prefixEnd_626143 321512317448248946332927 := by
  unfold tailWord_626143
  simp only [CollatzResearch.WordTrace]
  refine ⟨22837311370598322555843083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15224874247065548370562055 22837311370598322555843083)
  ·
    refine ⟨34255967055897483833764625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22837311370598322555843083 34255967055897483833764625)
    ·
      refine ⟨25691975291923112875323469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34255967055897483833764625 25691975291923112875323469)
      ·
        refine ⟨9634490734471167328246301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25691975291923112875323469 9634490734471167328246301)
        ·
          refine ⟨3612934025426687748092363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9634490734471167328246301 3612934025426687748092363)
          ·
            refine ⟨5419401038140031622138545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3612934025426687748092363 5419401038140031622138545)
            ·
              refine ⟨4064550778605023716603909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5419401038140031622138545 4064550778605023716603909)
              ·
                refine ⟨762103270988441946863233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4064550778605023716603909 762103270988441946863233)
                ·
                  refine ⟨571577453241331460147425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 762103270988441946863233 571577453241331460147425)
                  ·
                    refine ⟨428683089930998595110569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 571577453241331460147425 428683089930998595110569)
                    ·
                      refine ⟨321512317448248946332927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 428683089930998595110569 321512317448248946332927)
                      ·
                        rfl

theorem cell23_626143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_626143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626143 prefixEnd_626143 := by exact prefixLift 626143
  have htrace : WordTrace (prefixWord ++ tailWord_626143) baseStart_626143 baseEnd_626143 := by
    simpa [prefixWord, tailWord_626143, baseEnd_626143] using wordTrace_append hprefix tailTrace_626143
  have hstable : (prefixWord ++ tailWord_626143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626143).length < 2 ^ (prefixWord ++ tailWord_626143).sum := by decide
  have hdescent : baseEnd_626143 < baseStart_626143 := by decide
  rcases family_descends (prefixWord ++ tailWord_626143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626159 : List Nat := [1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 3]
def baseStart_626159 : Nat := 118140960795 + 626159 * 2 ^ 59
def prefixEnd_626159 : Nat := 4983230072969 + 3 ^ 40 * 626159 * 2
def baseEnd_626159 : Nat := 321520533138720883732853

theorem tailTrace_626159 : CollatzResearch.WordTrace tailWord_626159 prefixEnd_626159 321520533138720883732853 := by
  unfold tailWord_626159
  simp only [CollatzResearch.WordTrace]
  refine ⟨22837894938540357288425531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15225263292360238192283687 22837894938540357288425531)
  ·
    refine ⟨34256842407810535932638297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22837894938540357288425531 34256842407810535932638297)
    ·
      refine ⟨25692631805857901949478723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34256842407810535932638297 25692631805857901949478723)
      ·
        refine ⟨38538947708786852924218085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25692631805857901949478723 38538947708786852924218085)
        ·
          refine ⟨7226052695397534923290891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38538947708786852924218085 7226052695397534923290891)
          ·
            refine ⟨10839079043096302384936337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7226052695397534923290891 10839079043096302384936337)
            ·
              refine ⟨8129309282322226788702253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10839079043096302384936337 8129309282322226788702253)
              ·
                refine ⟨3048490980870835045763345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8129309282322226788702253 3048490980870835045763345)
                ·
                  refine ⟨2286368235653126284322509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3048490980870835045763345 2286368235653126284322509)
                  ·
                    refine ⟨857388088369922356620941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2286368235653126284322509 857388088369922356620941)
                    ·
                      refine ⟨321520533138720883732853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 857388088369922356620941 321520533138720883732853)
                      ·
                        rfl

theorem cell23_626159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 3, 2, 3, 3].length) (baseStart_626159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626159 prefixEnd_626159 := by exact prefixLift 626159
  have htrace : WordTrace (prefixWord ++ tailWord_626159) baseStart_626159 baseEnd_626159 := by
    simpa [prefixWord, tailWord_626159, baseEnd_626159] using wordTrace_append hprefix tailTrace_626159
  have hstable : (prefixWord ++ tailWord_626159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626159).length < 2 ^ (prefixWord ++ tailWord_626159).sum := by decide
  have hdescent : baseEnd_626159 < baseStart_626159 := by decide
  rcases family_descends (prefixWord ++ tailWord_626159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626160 : List Nat := [2, 1, 1, 1, 3, 4, 4, 1, 2, 2, 2]
def baseStart_626160 : Nat := 118140960795 + 626160 * 2 ^ 59
def prefixEnd_626160 : Nat := 4983230072969 + 3 ^ 40 * 626160 * 2
def baseEnd_626160 : Nat := 321521046619375379820349

theorem tailTrace_626160 : CollatzResearch.WordTrace tailWord_626160 prefixEnd_626160 321521046619375379820349 := by
  unfold tailWord_626160
  simp only [CollatzResearch.WordTrace]
  refine ⟨11418965705768367229605967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15225287607691156306141289 11418965705768367229605967)
  ·
    refine ⟨17128448558652550844408951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11418965705768367229605967 17128448558652550844408951)
    ·
      refine ⟨25692672837978826266613427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17128448558652550844408951 25692672837978826266613427)
      ·
        refine ⟨38539009256968239399920141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25692672837978826266613427 38539009256968239399920141)
        ·
          refine ⟨14452128471363089774970053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38539009256968239399920141 14452128471363089774970053)
          ·
            refine ⟨2709774088380579332806885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14452128471363089774970053 2709774088380579332806885)
            ·
              refine ⟨508082641571358624901291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2709774088380579332806885 508082641571358624901291)
              ·
                refine ⟨762123962357037937351937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508082641571358624901291 762123962357037937351937)
                ·
                  refine ⟨571592971767778453013953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 762123962357037937351937 571592971767778453013953)
                  ·
                    refine ⟨428694728825833839760465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 571592971767778453013953 428694728825833839760465)
                    ·
                      refine ⟨321521046619375379820349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 428694728825833839760465 321521046619375379820349)
                      ·
                        rfl

theorem cell23_626160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 4, 1, 2, 2, 2].length) (baseStart_626160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626160 prefixEnd_626160 := by exact prefixLift 626160
  have htrace : WordTrace (prefixWord ++ tailWord_626160) baseStart_626160 baseEnd_626160 := by
    simpa [prefixWord, tailWord_626160, baseEnd_626160] using wordTrace_append hprefix tailTrace_626160
  have hstable : (prefixWord ++ tailWord_626160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626160).length < 2 ^ (prefixWord ++ tailWord_626160).sum := by decide
  have hdescent : baseEnd_626160 < baseStart_626160 := by decide
  rcases family_descends (prefixWord ++ tailWord_626160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626200 : List Nat := [2, 1, 2, 3, 4, 2, 2, 2, 5]
def baseStart_626200 : Nat := 118140960795 + 626200 * 2 ^ 59
def prefixEnd_626200 : Nat := 4983230072969 + 3 ^ 40 * 626200 * 2
def baseEnd_626200 : Nat := 35726842871728358146685

theorem tailTrace_626200 : CollatzResearch.WordTrace tailWord_626200 prefixEnd_626200 35726842871728358146685 := by
  unfold tailWord_626200
  simp only [CollatzResearch.WordTrace]
  refine ⟨11419695165695910645334027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15226260220927880860445369 11419695165695910645334027)
  ·
    refine ⟨17129542748543865968001041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11419695165695910645334027 17129542748543865968001041)
    ·
      refine ⟨12847157061407899476000781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17129542748543865968001041 12847157061407899476000781)
      ·
        refine ⟨4817683898027962303500293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12847157061407899476000781 4817683898027962303500293)
        ·
          refine ⟨903315730880242931906305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4817683898027962303500293 903315730880242931906305)
          ·
            refine ⟨677486798160182198929729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 903315730880242931906305 677486798160182198929729)
            ·
              refine ⟨508115098620136649197297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 677486798160182198929729 508115098620136649197297)
              ·
                refine ⟨381086323965102486897973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508115098620136649197297 381086323965102486897973)
                ·
                  refine ⟨35726842871728358146685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 381086323965102486897973 35726842871728358146685)
                  ·
                    rfl

theorem cell23_626200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 5].length) (baseStart_626200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626200 prefixEnd_626200 := by exact prefixLift 626200
  have htrace : WordTrace (prefixWord ++ tailWord_626200) baseStart_626200 baseEnd_626200 := by
    simpa [prefixWord, tailWord_626200, baseEnd_626200] using wordTrace_append hprefix tailTrace_626200
  have hstable : (prefixWord ++ tailWord_626200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626200).length < 2 ^ (prefixWord ++ tailWord_626200).sum := by decide
  have hdescent : baseEnd_626200 < baseStart_626200 := by decide
  rcases family_descends (prefixWord ++ tailWord_626200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626230 : List Nat := [5, 1, 2, 1, 3, 2, 1, 1, 2, 5]
def baseStart_626230 : Nat := 118140960795 + 626230 * 2 ^ 59
def prefixEnd_626230 : Nat := 4983230072969 + 3 ^ 40 * 626230 * 2
def baseEnd_626230 : Nat := 107185663421730035315009

theorem tailTrace_626230 : CollatzResearch.WordTrace tailWord_626230 prefixEnd_626230 107185663421730035315009 := by
  unfold tailWord_626230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1427530282580196025891259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15226989680855424276173429 1427530282580196025891259)
  ·
    refine ⟨2141295423870294038836889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1427530282580196025891259 2141295423870294038836889)
    ·
      refine ⟨1605971567902720529127667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2141295423870294038836889 1605971567902720529127667)
      ·
        refine ⟨2408957351854080793691501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1605971567902720529127667 2408957351854080793691501)
        ·
          refine ⟨903359006945280297634313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2408957351854080793691501 903359006945280297634313)
          ·
            refine ⟨677519255208960223225735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 903359006945280297634313 677519255208960223225735)
            ·
              refine ⟨1016278882813440334838603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677519255208960223225735 1016278882813440334838603)
              ·
                refine ⟨1524418324220160502257905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1016278882813440334838603 1524418324220160502257905)
                ·
                  refine ⟨1143313743165120376693429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1524418324220160502257905 1143313743165120376693429)
                  ·
                    refine ⟨107185663421730035315009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1143313743165120376693429 107185663421730035315009)
                    ·
                      rfl

theorem cell23_626230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_626230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626230 prefixEnd_626230 := by exact prefixLift 626230
  have htrace : WordTrace (prefixWord ++ tailWord_626230) baseStart_626230 baseEnd_626230 := by
    simpa [prefixWord, tailWord_626230, baseEnd_626230] using wordTrace_append hprefix tailTrace_626230
  have hstable : (prefixWord ++ tailWord_626230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626230).length < 2 ^ (prefixWord ++ tailWord_626230).sum := by decide
  have hdescent : baseEnd_626230 < baseStart_626230 := by decide
  rcases family_descends (prefixWord ++ tailWord_626230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626233 : List Nat := [1, 2, 1, 5, 1, 4, 1, 1, 2, 1, 4]
def baseStart_626233 : Nat := 118140960795 + 626233 * 2 ^ 59
def prefixEnd_626233 : Nat := 4983230072969 + 3 ^ 40 * 626233 * 2
def baseEnd_626233 : Nat := 321558530707153594207513

theorem tailTrace_626233 : CollatzResearch.WordTrace tailWord_626233 prefixEnd_626233 321558530707153594207513 := by
  unfold tailWord_626233
  simp only [CollatzResearch.WordTrace]
  refine ⟨22840593940272267926619353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15227062626848178617746235 22840593940272267926619353)
  ·
    refine ⟨17130445455204200944964515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22840593940272267926619353 17130445455204200944964515)
    ·
      refine ⟨25695668182806301417446773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17130445455204200944964515 25695668182806301417446773)
      ·
        refine ⟨2408968892138090757885635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25695668182806301417446773 2408968892138090757885635)
        ·
          refine ⟨3613453338207136136828453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2408968892138090757885635 3613453338207136136828453)
          ·
            refine ⟨677522500913838025655335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3613453338207136136828453 677522500913838025655335)
            ·
              refine ⟨1016283751370757038483003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677522500913838025655335 1016283751370757038483003)
              ·
                refine ⟨1524425627056135557724505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1016283751370757038483003 1524425627056135557724505)
                ·
                  refine ⟨1143319220292101668293379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1524425627056135557724505 1143319220292101668293379)
                  ·
                    refine ⟨1714978830438152502440069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1143319220292101668293379 1714978830438152502440069)
                    ·
                      refine ⟨321558530707153594207513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1714978830438152502440069 321558530707153594207513)
                      ·
                        rfl

theorem cell23_626233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_626233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626233 prefixEnd_626233 := by exact prefixLift 626233
  have htrace : WordTrace (prefixWord ++ tailWord_626233) baseStart_626233 baseEnd_626233 := by
    simpa [prefixWord, tailWord_626233, baseEnd_626233] using wordTrace_append hprefix tailTrace_626233
  have hstable : (prefixWord ++ tailWord_626233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626233).length < 2 ^ (prefixWord ++ tailWord_626233).sum := by decide
  have hdescent : baseEnd_626233 < baseStart_626233 := by decide
  rcases family_descends (prefixWord ++ tailWord_626233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626249 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 1, 7, 3]
def baseStart_626249 : Nat := 118140960795 + 626249 * 2 ^ 59
def prefixEnd_626249 : Nat := 4983230072969 + 3 ^ 40 * 626249 * 2
def baseEnd_626249 : Nat := 321566746397625531607439

theorem tailTrace_626249 : CollatzResearch.WordTrace tailWord_626249 prefixEnd_626249 321566746397625531607439 := by
  unfold tailWord_626249
  simp only [CollatzResearch.WordTrace]
  refine ⟨22841177508214302659201801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15227451672142868439467867 22841177508214302659201801)
  ·
    refine ⟨17130883131160726994401351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22841177508214302659201801 17130883131160726994401351)
    ·
      refine ⟨25696324696741090491602027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17130883131160726994401351 25696324696741090491602027)
      ·
        refine ⟨38544487045111635737403041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25696324696741090491602027 38544487045111635737403041)
        ·
          refine ⟨28908365283833726803052281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38544487045111635737403041 28908365283833726803052281)
          ·
            refine ⟨21681273962875295102289211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28908365283833726803052281 21681273962875295102289211)
            ·
              refine ⟨32521910944312942653433817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21681273962875295102289211 32521910944312942653433817)
              ·
                refine ⟨24391433208234706990075363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32521910944312942653433817 24391433208234706990075363)
                ·
                  refine ⟨36587149812352060485113045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24391433208234706990075363 36587149812352060485113045)
                  ·
                    refine ⟨857511323727001417619837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36587149812352060485113045 857511323727001417619837)
                    ·
                      refine ⟨321566746397625531607439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 857511323727001417619837 321566746397625531607439)
                      ·
                        rfl

theorem cell23_626249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 7, 3].length) (baseStart_626249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626249 prefixEnd_626249 := by exact prefixLift 626249
  have htrace : WordTrace (prefixWord ++ tailWord_626249) baseStart_626249 baseEnd_626249 := by
    simpa [prefixWord, tailWord_626249, baseEnd_626249] using wordTrace_append hprefix tailTrace_626249
  have hstable : (prefixWord ++ tailWord_626249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626249).length < 2 ^ (prefixWord ++ tailWord_626249).sum := by decide
  have hdescent : baseEnd_626249 < baseStart_626249 := by decide
  rcases family_descends (prefixWord ++ tailWord_626249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626279 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_626279 : Nat := 118140960795 + 626279 * 2 ^ 59
def prefixEnd_626279 : Nat := 4983230072969 + 3 ^ 40 * 626279 * 2
def baseEnd_626279 : Nat := 321582150817260414232301

theorem tailTrace_626279 : CollatzResearch.WordTrace tailWord_626279 prefixEnd_626279 321582150817260414232301 := by
  unfold tailWord_626279
  simp only [CollatzResearch.WordTrace]
  refine ⟨22842271698105617782793891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15228181132070411855195927 22842271698105617782793891)
  ·
    refine ⟨34263407547158426674190837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22842271698105617782793891 34263407547158426674190837)
    ·
      refine ⟨3212194457546102500705391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34263407547158426674190837 3212194457546102500705391)
      ·
        refine ⟨4818291686319153751058087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3212194457546102500705391 4818291686319153751058087)
        ·
          refine ⟨7227437529478730626587131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4818291686319153751058087 7227437529478730626587131)
          ·
            refine ⟨10841156294218095939880697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7227437529478730626587131 10841156294218095939880697)
            ·
              refine ⟨8130867220663571954910523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10841156294218095939880697 8130867220663571954910523)
              ·
                refine ⟨12196300830995357932365785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8130867220663571954910523 12196300830995357932365785)
                ·
                  refine ⟨9147225623246518449274339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12196300830995357932365785 9147225623246518449274339)
                  ·
                    refine ⟨13720838434869777673911509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9147225623246518449274339 13720838434869777673911509)
                    ·
                      refine ⟨321582150817260414232301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13720838434869777673911509 321582150817260414232301)
                      ·
                        rfl

theorem cell23_626279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_626279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626279 prefixEnd_626279 := by exact prefixLift 626279
  have htrace : WordTrace (prefixWord ++ tailWord_626279) baseStart_626279 baseEnd_626279 := by
    simpa [prefixWord, tailWord_626279, baseEnd_626279] using wordTrace_append hprefix tailTrace_626279
  have hstable : (prefixWord ++ tailWord_626279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626279).length < 2 ^ (prefixWord ++ tailWord_626279).sum := by decide
  have hdescent : baseEnd_626279 < baseStart_626279 := by decide
  rcases family_descends (prefixWord ++ tailWord_626279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626289 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 2, 5, 4]
def baseStart_626289 : Nat := 118140960795 + 626289 * 2 ^ 59
def prefixEnd_626289 : Nat := 4983230072969 + 3 ^ 40 * 626289 * 2
def baseEnd_626289 : Nat := 321587285623805375107255

theorem tailTrace_626289 : CollatzResearch.WordTrace tailWord_626289 prefixEnd_626289 321587285623805375107255 := by
  unfold tailWord_626289
  simp only [CollatzResearch.WordTrace]
  refine ⟨22842636428069389490657921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15228424285379592993771947 22842636428069389490657921)
  ·
    refine ⟨17131977321052042117993441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22842636428069389490657921 17131977321052042117993441)
    ·
      refine ⟨12848982990789031588495081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17131977321052042117993441 12848982990789031588495081)
      ·
        refine ⟨9636737243091773691371311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12848982990789031588495081 9636737243091773691371311)
        ·
          refine ⟨14455105864637660537056967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9636737243091773691371311 14455105864637660537056967)
          ·
            refine ⟨21682658796956490805585451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14455105864637660537056967 21682658796956490805585451)
            ·
              refine ⟨32523988195434736208378177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21682658796956490805585451 32523988195434736208378177)
              ·
                refine ⟨24392991146576052156283633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32523988195434736208378177 24392991146576052156283633)
                ·
                  refine ⟨18294743359932039117212725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24392991146576052156283633 18294743359932039117212725)
                  ·
                    refine ⟨1715132189993628667238693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18294743359932039117212725 1715132189993628667238693)
                    ·
                      refine ⟨321587285623805375107255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1715132189993628667238693 321587285623805375107255)
                      ·
                        rfl

theorem cell23_626289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_626289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626289 prefixEnd_626289 := by exact prefixLift 626289
  have htrace : WordTrace (prefixWord ++ tailWord_626289) baseStart_626289 baseEnd_626289 := by
    simpa [prefixWord, tailWord_626289, baseEnd_626289] using wordTrace_append hprefix tailTrace_626289
  have hstable : (prefixWord ++ tailWord_626289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626289).length < 2 ^ (prefixWord ++ tailWord_626289).sum := by decide
  have hdescent : baseEnd_626289 < baseStart_626289 := by decide
  rcases family_descends (prefixWord ++ tailWord_626289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626299 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 3, 6]
def baseStart_626299 : Nat := 118140960795 + 626299 * 2 ^ 59
def prefixEnd_626299 : Nat := 4983230072969 + 3 ^ 40 * 626299 * 2
def baseEnd_626299 : Nat := 107197473476783445327403

theorem tailTrace_626299 : CollatzResearch.WordTrace tailWord_626299 prefixEnd_626299 107197473476783445327403 := by
  unfold tailWord_626299
  simp only [CollatzResearch.WordTrace]
  refine ⟨22843001158033161198521951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15228667438688774132347967 22843001158033161198521951)
  ·
    refine ⟨34264501737049741797782927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22843001158033161198521951 34264501737049741797782927)
    ·
      refine ⟨51396752605574612696674391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34264501737049741797782927 51396752605574612696674391)
      ·
        refine ⟨77095128908361919045011587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51396752605574612696674391 77095128908361919045011587)
        ·
          refine ⟨115642693362542878567517381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77095128908361919045011587 115642693362542878567517381)
          ·
            refine ⟨21683005005476789731409509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115642693362542878567517381 21683005005476789731409509)
            ·
              refine ⟨4065563438526898074639283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21683005005476789731409509 4065563438526898074639283)
              ·
                refine ⟨6098345157790347111958925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4065563438526898074639283 6098345157790347111958925)
                ·
                  refine ⟨2286879434171380166984597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6098345157790347111958925 2286879434171380166984597)
                  ·
                    refine ⟨107197473476783445327403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2286879434171380166984597 107197473476783445327403)
                    ·
                      rfl

theorem cell23_626299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 3, 6].length) (baseStart_626299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626299 prefixEnd_626299 := by exact prefixLift 626299
  have htrace : WordTrace (prefixWord ++ tailWord_626299) baseStart_626299 baseEnd_626299 := by
    simpa [prefixWord, tailWord_626299, baseEnd_626299] using wordTrace_append hprefix tailTrace_626299
  have hstable : (prefixWord ++ tailWord_626299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626299).length < 2 ^ (prefixWord ++ tailWord_626299).sum := by decide
  have hdescent : baseEnd_626299 < baseStart_626299 := by decide
  rcases family_descends (prefixWord ++ tailWord_626299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626316 : List Nat := [2, 2, 1, 2, 1, 1, 3, 3, 4, 4]
def baseStart_626316 : Nat := 118140960795 + 626316 * 2 ^ 59
def prefixEnd_626316 : Nat := 4983230072969 + 3 ^ 40 * 626316 * 2
def baseEnd_626316 : Nat := 107200383200492256489877

theorem tailTrace_626316 : CollatzResearch.WordTrace tailWord_626316 prefixEnd_626316 107200383200492256489877 := by
  unfold tailWord_626316
  simp only [CollatzResearch.WordTrace]
  refine ⟨11421810599485786550945401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15229080799314382067927201 11421810599485786550945401)
  ·
    refine ⟨8566357949614339913209051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11421810599485786550945401 8566357949614339913209051)
    ·
      refine ⟨12849536924421509869813577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8566357949614339913209051 12849536924421509869813577)
      ·
        refine ⟨9637152693316132402360183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12849536924421509869813577 9637152693316132402360183)
        ·
          refine ⟨14455729039974198603540275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9637152693316132402360183 14455729039974198603540275)
          ·
            refine ⟨21683593559961297905310413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14455729039974198603540275 21683593559961297905310413)
            ·
              refine ⟨8131347584985486714491405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21683593559961297905310413 8131347584985486714491405)
              ·
                refine ⟨3049255344369557517934277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8131347584985486714491405 3049255344369557517934277)
                ·
                  refine ⟨571735377069292034612677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3049255344369557517934277 571735377069292034612677)
                  ·
                    refine ⟨107200383200492256489877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 571735377069292034612677 107200383200492256489877)
                    ·
                      rfl

theorem cell23_626316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 3, 4, 4].length) (baseStart_626316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626316 prefixEnd_626316 := by exact prefixLift 626316
  have htrace : WordTrace (prefixWord ++ tailWord_626316) baseStart_626316 baseEnd_626316 := by
    simpa [prefixWord, tailWord_626316, baseEnd_626316] using wordTrace_append hprefix tailTrace_626316
  have hstable : (prefixWord ++ tailWord_626316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626316).length < 2 ^ (prefixWord ++ tailWord_626316).sum := by decide
  have hdescent : baseEnd_626316 < baseStart_626316 := by decide
  rcases family_descends (prefixWord ++ tailWord_626316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626319 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 4]
def baseStart_626319 : Nat := 118140960795 + 626319 * 2 ^ 59
def prefixEnd_626319 : Nat := 4983230072969 + 3 ^ 40 * 626319 * 2
def baseEnd_626319 : Nat := 321602690043440257732117

theorem tailTrace_626319 : CollatzResearch.WordTrace tailWord_626319 prefixEnd_626319 321602690043440257732117 := by
  unfold tailWord_626319
  simp only [CollatzResearch.WordTrace]
  refine ⟨22843730617960704614250011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15229153745307136409500007 22843730617960704614250011)
  ·
    refine ⟨34265595926941056921375017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22843730617960704614250011 34265595926941056921375017)
    ·
      refine ⟨25699196945205792691031263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34265595926941056921375017 25699196945205792691031263)
      ·
        refine ⟨38548795417808689036546895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25699196945205792691031263 38548795417808689036546895)
        ·
          refine ⟨57823193126713033554820343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38548795417808689036546895 57823193126713033554820343)
          ·
            refine ⟨86734789690069550332230515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57823193126713033554820343 86734789690069550332230515)
            ·
              refine ⟨130102184535104325498345773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86734789690069550332230515 130102184535104325498345773)
              ·
                refine ⟨48788319200664122061879665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130102184535104325498345773 48788319200664122061879665)
                ·
                  refine ⟨36591239400498091546409749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48788319200664122061879665 36591239400498091546409749)
                  ·
                    refine ⟨1715214346898348041237957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36591239400498091546409749 1715214346898348041237957)
                    ·
                      refine ⟨321602690043440257732117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1715214346898348041237957 321602690043440257732117)
                      ·
                        rfl

theorem cell23_626319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 6, 4].length) (baseStart_626319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626319 prefixEnd_626319 := by exact prefixLift 626319
  have htrace : WordTrace (prefixWord ++ tailWord_626319) baseStart_626319 baseEnd_626319 := by
    simpa [prefixWord, tailWord_626319, baseEnd_626319] using wordTrace_append hprefix tailTrace_626319
  have hstable : (prefixWord ++ tailWord_626319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626319).length < 2 ^ (prefixWord ++ tailWord_626319).sum := by decide
  have hdescent : baseEnd_626319 < baseStart_626319 := by decide
  rcases family_descends (prefixWord ++ tailWord_626319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626336 : List Nat := [2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 6]
def baseStart_626336 : Nat := 118140960795 + 626336 * 2 ^ 59
def prefixEnd_626336 : Nat := 4983230072969 + 3 ^ 40 * 626336 * 2
def baseEnd_626336 : Nat := 321611419214566691219539

theorem tailTrace_626336 : CollatzResearch.WordTrace tailWord_626336 prefixEnd_626336 321611419214566691219539 := by
  unfold tailWord_626336
  simp only [CollatzResearch.WordTrace]
  refine ⟨11422175329449558258809431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15229567105932744345079241 11422175329449558258809431)
  ·
    refine ⟨17133262994174337388214147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11422175329449558258809431 17133262994174337388214147)
    ·
      refine ⟨25699894491261506082321221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17133262994174337388214147 25699894491261506082321221)
      ·
        refine ⟨4818730217111532390435229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25699894491261506082321221 4818730217111532390435229)
        ·
          refine ⟨1807023831416824646413211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4818730217111532390435229 1807023831416824646413211)
          ·
            refine ⟨2710535747125236969619817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1807023831416824646413211 2710535747125236969619817)
            ·
              refine ⟨2032901810343927727214863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2710535747125236969619817 2032901810343927727214863)
              ·
                refine ⟨3049352715515891590822295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2032901810343927727214863 3049352715515891590822295)
                ·
                  refine ⟨4574029073273837386233443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3049352715515891590822295 4574029073273837386233443)
                  ·
                    refine ⟨6861043609910756079350165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4574029073273837386233443 6861043609910756079350165)
                    ·
                      refine ⟨321611419214566691219539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6861043609910756079350165 321611419214566691219539)
                      ·
                        rfl

theorem cell23_626336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_626336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626336 prefixEnd_626336 := by exact prefixLift 626336
  have htrace : WordTrace (prefixWord ++ tailWord_626336) baseStart_626336 baseEnd_626336 := by
    simpa [prefixWord, tailWord_626336, baseEnd_626336] using wordTrace_append hprefix tailTrace_626336
  have hstable : (prefixWord ++ tailWord_626336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626336).length < 2 ^ (prefixWord ++ tailWord_626336).sum := by decide
  have hdescent : baseEnd_626336 < baseStart_626336 := by decide
  rcases family_descends (prefixWord ++ tailWord_626336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626340 : List Nat := [2, 3, 1, 2, 2, 4, 1, 2, 1, 1, 4]
def baseStart_626340 : Nat := 118140960795 + 626340 * 2 ^ 59
def prefixEnd_626340 : Nat := 4983230072969 + 3 ^ 40 * 626340 * 2
def baseEnd_626340 : Nat := 321613473137184675569521

theorem tailTrace_626340 : CollatzResearch.WordTrace tailWord_626340 prefixEnd_626340 321613473137184675569521 := by
  unfold tailWord_626340
  simp only [CollatzResearch.WordTrace]
  refine ⟨11422248275442312600382237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15229664367256416800509649 11422248275442312600382237)
  ·
    refine ⟨4283343103290867225143339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11422248275442312600382237 4283343103290867225143339)
    ·
      refine ⟨6425014654936300837715009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4283343103290867225143339 6425014654936300837715009)
      ·
        refine ⟨4818760991202225628286257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6425014654936300837715009 4818760991202225628286257)
        ·
          refine ⟨3614070743401669221214693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4818760991202225628286257 3614070743401669221214693)
          ·
            refine ⟨677638264387812978977755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3614070743401669221214693 677638264387812978977755)
            ·
              refine ⟨1016457396581719468466633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677638264387812978977755 1016457396581719468466633)
              ·
                refine ⟨762343047436289601349975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1016457396581719468466633 762343047436289601349975)
                ·
                  refine ⟨1143514571154434402024963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762343047436289601349975 1143514571154434402024963)
                  ·
                    refine ⟨1715271856731651603037445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1143514571154434402024963 1715271856731651603037445)
                    ·
                      refine ⟨321613473137184675569521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1715271856731651603037445 321613473137184675569521)
                      ·
                        rfl

theorem cell23_626340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_626340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626340 prefixEnd_626340 := by exact prefixLift 626340
  have htrace : WordTrace (prefixWord ++ tailWord_626340) baseStart_626340 baseEnd_626340 := by
    simpa [prefixWord, tailWord_626340, baseEnd_626340] using wordTrace_append hprefix tailTrace_626340
  have hstable : (prefixWord ++ tailWord_626340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626340).length < 2 ^ (prefixWord ++ tailWord_626340).sum := by decide
  have hdescent : baseEnd_626340 < baseStart_626340 := by decide
  rcases family_descends (prefixWord ++ tailWord_626340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626350 : List Nat := [4, 1, 4, 1, 2, 1, 1, 2, 1, 6]
def baseStart_626350 : Nat := 118140960795 + 626350 * 2 ^ 59
def prefixEnd_626350 : Nat := 4983230072969 + 3 ^ 40 * 626350 * 2
def baseEnd_626350 : Nat := 107206202647909878814825

theorem tailTrace_626350 : CollatzResearch.WordTrace tailWord_626350 prefixEnd_626350 107206202647909878814825 := by
  unfold tailWord_626350
  simp only [CollatzResearch.WordTrace]
  refine ⟨2855607660106049613578563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15229907520565597939085669 2855607660106049613578563)
  ·
    refine ⟨4283411490159074420367845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2855607660106049613578563 4283411490159074420367845)
    ·
      refine ⟨803139654404826453818971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4283411490159074420367845 803139654404826453818971)
      ·
        refine ⟨1204709481607239680728457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803139654404826453818971 1204709481607239680728457)
        ·
          refine ⟨903532111205429760546343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1204709481607239680728457 903532111205429760546343)
          ·
            refine ⟨1355298166808144640819515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903532111205429760546343 1355298166808144640819515)
            ·
              refine ⟨2032947250212216961229273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355298166808144640819515 2032947250212216961229273)
              ·
                refine ⟨1524710437659162720921955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2032947250212216961229273 1524710437659162720921955)
                ·
                  refine ⟨2287065656488744081382933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524710437659162720921955 2287065656488744081382933)
                  ·
                    refine ⟨107206202647909878814825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2287065656488744081382933 107206202647909878814825)
                    ·
                      rfl

theorem cell23_626350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_626350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626350 prefixEnd_626350 := by exact prefixLift 626350
  have htrace : WordTrace (prefixWord ++ tailWord_626350) baseStart_626350 baseEnd_626350 := by
    simpa [prefixWord, tailWord_626350, baseEnd_626350] using wordTrace_append hprefix tailTrace_626350
  have hstable : (prefixWord ++ tailWord_626350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626350).length < 2 ^ (prefixWord ++ tailWord_626350).sum := by decide
  have hdescent : baseEnd_626350 < baseStart_626350 := by decide
  rcases family_descends (prefixWord ++ tailWord_626350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626357 : List Nat := [1, 3, 3, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_626357 : Nat := 118140960795 + 626357 * 2 ^ 59
def prefixEnd_626357 : Nat := 4983230072969 + 3 ^ 40 * 626357 * 2
def baseEnd_626357 : Nat := 321622202308311109056943

theorem tailTrace_626357 : CollatzResearch.WordTrace tailWord_626357 prefixEnd_626357 321622202308311109056943 := by
  unfold tailWord_626357
  simp only [CollatzResearch.WordTrace]
  refine ⟨22845116591823037104133325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15230077727882024736088883 22845116591823037104133325)
  ·
    refine ⟨8566918721933638914049997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22845116591823037104133325 8566918721933638914049997)
    ·
      refine ⟨3212594520725114592768749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8566918721933638914049997 3212594520725114592768749)
      ·
        refine ⟨1204722945271917972288281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3212594520725114592768749 1204722945271917972288281)
        ·
          refine ⟨903542208953938479216211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1204722945271917972288281 903542208953938479216211)
          ·
            refine ⟨1355313313430907718824317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903542208953938479216211 1355313313430907718824317)
            ·
              refine ⟨508242492536590394559119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1355313313430907718824317 508242492536590394559119)
              ·
                refine ⟨762363738804885591838679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508242492536590394559119 762363738804885591838679)
                ·
                  refine ⟨1143545608207328387758019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762363738804885591838679 1143545608207328387758019)
                  ·
                    refine ⟨1715318412310992581637029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1143545608207328387758019 1715318412310992581637029)
                    ·
                      refine ⟨321622202308311109056943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1715318412310992581637029 321622202308311109056943)
                      ·
                        rfl

theorem cell23_626357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_626357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626357 prefixEnd_626357 := by exact prefixLift 626357
  have htrace : WordTrace (prefixWord ++ tailWord_626357) baseStart_626357 baseEnd_626357 := by
    simpa [prefixWord, tailWord_626357, baseEnd_626357] using wordTrace_append hprefix tailTrace_626357
  have hstable : (prefixWord ++ tailWord_626357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626357).length < 2 ^ (prefixWord ++ tailWord_626357).sum := by decide
  have hdescent : baseEnd_626357 < baseStart_626357 := by decide
  rcases family_descends (prefixWord ++ tailWord_626357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626380 : List Nat := [2, 2, 1, 5, 3, 1, 1, 8]
def baseStart_626380 : Nat := 118140960795 + 626380 * 2 ^ 59
def prefixEnd_626380 : Nat := 4983230072969 + 3 ^ 40 * 626380 * 2
def baseEnd_626380 : Nat := 11912370828272759965531

theorem tailTrace_626380 : CollatzResearch.WordTrace tailWord_626380 prefixEnd_626380 11912370828272759965531 := by
  unfold tailWord_626380
  simp only [CollatzResearch.WordTrace]
  refine ⟨11422977735369856016110297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15230636980493141354813729 11422977735369856016110297)
  ·
    refine ⟨8567233301527392012082723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11422977735369856016110297 8567233301527392012082723)
    ·
      refine ⟨12850849952291088018124085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8567233301527392012082723 12850849952291088018124085)
      ·
        refine ⟨1204767183027289501699133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12850849952291088018124085 1204767183027289501699133)
        ·
          refine ⟨451787693635233563137175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1204767183027289501699133 451787693635233563137175)
          ·
            refine ⟨677681540452850344705763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451787693635233563137175 677681540452850344705763)
            ·
              refine ⟨1016522310679275517058645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677681540452850344705763 1016522310679275517058645)
              ·
                refine ⟨11912370828272759965531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1016522310679275517058645 11912370828272759965531)
                ·
                  rfl

theorem cell23_626380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 8].length) (baseStart_626380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626380 prefixEnd_626380 := by exact prefixLift 626380
  have htrace : WordTrace (prefixWord ++ tailWord_626380) baseStart_626380 baseEnd_626380 := by
    simpa [prefixWord, tailWord_626380, baseEnd_626380] using wordTrace_append hprefix tailTrace_626380
  have hstable : (prefixWord ++ tailWord_626380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626380).length < 2 ^ (prefixWord ++ tailWord_626380).sum := by decide
  have hdescent : baseEnd_626380 < baseStart_626380 := by decide
  rcases family_descends (prefixWord ++ tailWord_626380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626416 : List Nat := [2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 3]
def baseStart_626416 : Nat := 118140960795 + 626416 * 2 ^ 59
def prefixEnd_626416 : Nat := 4983230072969 + 3 ^ 40 * 626416 * 2
def baseEnd_626416 : Nat := 321652497666926378219171

theorem tailTrace_626416 : CollatzResearch.WordTrace tailWord_626416 prefixEnd_626416 321652497666926378219171 := by
  unfold tailWord_626416
  simp only [CollatzResearch.WordTrace]
  refine ⟨11423634249304645090265551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15231512332406193453687401 11423634249304645090265551)
  ·
    refine ⟨17135451373956967635398327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11423634249304645090265551 17135451373956967635398327)
    ·
      refine ⟨25703177060935451453097491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17135451373956967635398327 25703177060935451453097491)
      ·
        refine ⟨38554765591403177179646237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25703177060935451453097491 38554765591403177179646237)
        ·
          refine ⟨14458037096776191442367339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38554765591403177179646237 14458037096776191442367339)
          ·
            refine ⟨21687055645164287163551009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14458037096776191442367339 21687055645164287163551009)
            ·
              refine ⟨16265291733873215372663257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21687055645164287163551009 16265291733873215372663257)
              ·
                refine ⟨12198968800404911529497443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16265291733873215372663257 12198968800404911529497443)
                ·
                  refine ⟨18298453200607367294246165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12198968800404911529497443 18298453200607367294246165)
                  ·
                    refine ⟨857739993778470341917789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18298453200607367294246165 857739993778470341917789)
                    ·
                      refine ⟨321652497666926378219171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 857739993778470341917789 321652497666926378219171)
                      ·
                        rfl

theorem cell23_626416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 6, 3].length) (baseStart_626416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626416 prefixEnd_626416 := by exact prefixLift 626416
  have htrace : WordTrace (prefixWord ++ tailWord_626416) baseStart_626416 baseEnd_626416 := by
    simpa [prefixWord, tailWord_626416, baseEnd_626416] using wordTrace_append hprefix tailTrace_626416
  have hstable : (prefixWord ++ tailWord_626416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626416).length < 2 ^ (prefixWord ++ tailWord_626416).sum := by decide
  have hdescent : baseEnd_626416 < baseStart_626416 := by decide
  rcases family_descends (prefixWord ++ tailWord_626416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626417 : List Nat := [1, 2, 2, 2, 2, 3, 4, 1, 1, 3, 2]
def baseStart_626417 : Nat := 118140960795 + 626417 * 2 ^ 59
def prefixEnd_626417 : Nat := 4983230072969 + 3 ^ 40 * 626417 * 2
def baseEnd_626417 : Nat := 321653011147580874306667

theorem tailTrace_626417 : CollatzResearch.WordTrace tailWord_626417 prefixEnd_626417 321653011147580874306667 := by
  unfold tailWord_626417
  simp only [CollatzResearch.WordTrace]
  refine ⟨22847304971605667351317505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15231536647737111567545003 22847304971605667351317505)
  ·
    refine ⟨17135478728704250513488129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22847304971605667351317505 17135478728704250513488129)
    ·
      refine ⟨12851609046528187885116097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17135478728704250513488129 12851609046528187885116097)
      ·
        refine ⟨9638706784896140913837073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12851609046528187885116097 9638706784896140913837073)
        ·
          refine ⟨7229030088672105685377805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9638706784896140913837073 7229030088672105685377805)
          ·
            refine ⟨2710886283252039632016677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7229030088672105685377805 2710886283252039632016677)
            ·
              refine ⟨508291178109757431003127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2710886283252039632016677 508291178109757431003127)
              ·
                refine ⟨762436767164636146504691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 508291178109757431003127 762436767164636146504691)
                ·
                  refine ⟨1143655150746954219757037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762436767164636146504691 1143655150746954219757037)
                  ·
                    refine ⟨428870681530107832408889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1143655150746954219757037 428870681530107832408889)
                    ·
                      refine ⟨321653011147580874306667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 428870681530107832408889 321653011147580874306667)
                      ·
                        rfl

theorem cell23_626417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 1, 3, 2].length) (baseStart_626417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626417 prefixEnd_626417 := by exact prefixLift 626417
  have htrace : WordTrace (prefixWord ++ tailWord_626417) baseStart_626417 baseEnd_626417 := by
    simpa [prefixWord, tailWord_626417, baseEnd_626417] using wordTrace_append hprefix tailTrace_626417
  have hstable : (prefixWord ++ tailWord_626417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626417).length < 2 ^ (prefixWord ++ tailWord_626417).sum := by decide
  have hdescent : baseEnd_626417 < baseStart_626417 := by decide
  rcases family_descends (prefixWord ++ tailWord_626417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626438 : List Nat := [6, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4]
def baseStart_626438 : Nat := 118140960795 + 626438 * 2 ^ 59
def prefixEnd_626438 : Nat := 4983230072969 + 3 ^ 40 * 626438 * 2
def baseEnd_626438 : Nat := 321663794241325292144071

theorem tailTrace_626438 : CollatzResearch.WordTrace tailWord_626438 prefixEnd_626438 321663794241325292144071 := by
  unfold tailWord_626438
  simp only [CollatzResearch.WordTrace]
  refine ⟨714002215766549623057249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 15232047269686391958554645 714002215766549623057249)
  ·
    refine ⟨535501661824912217292937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 714002215766549623057249 535501661824912217292937)
    ·
      refine ⟨401626246368684162969703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 535501661824912217292937 401626246368684162969703)
      ·
        refine ⟨602439369553026244454555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 401626246368684162969703 602439369553026244454555)
        ·
          refine ⟨903659054329539366681833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602439369553026244454555 903659054329539366681833)
          ·
            refine ⟨677744290747154525011375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 903659054329539366681833 677744290747154525011375)
            ·
              refine ⟨1016616436120731787517063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677744290747154525011375 1016616436120731787517063)
              ·
                refine ⟨1524924654181097681275595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1016616436120731787517063 1524924654181097681275595)
                ·
                  refine ⟨2287386981271646521913393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524924654181097681275595 2287386981271646521913393)
                  ·
                    refine ⟨1715540235953734891435045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2287386981271646521913393 1715540235953734891435045)
                    ·
                      refine ⟨321663794241325292144071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1715540235953734891435045 321663794241325292144071)
                      ·
                        rfl

theorem cell23_626438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_626438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626438 prefixEnd_626438 := by exact prefixLift 626438
  have htrace : WordTrace (prefixWord ++ tailWord_626438) baseStart_626438 baseEnd_626438 := by
    simpa [prefixWord, tailWord_626438, baseEnd_626438] using wordTrace_append hprefix tailTrace_626438
  have hstable : (prefixWord ++ tailWord_626438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626438).length < 2 ^ (prefixWord ++ tailWord_626438).sum := by decide
  have hdescent : baseEnd_626438 < baseStart_626438 := by decide
  rcases family_descends (prefixWord ++ tailWord_626438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626493 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 7]
def baseStart_626493 : Nat := 118140960795 + 626493 * 2 ^ 59
def prefixEnd_626493 : Nat := 4983230072969 + 3 ^ 40 * 626493 * 2
def baseEnd_626493 : Nat := 321692035677322576956317

theorem tailTrace_626493 : CollatzResearch.WordTrace tailWord_626493 prefixEnd_626493 321692035677322576956317 := by
  unfold tailWord_626493
  simp only [CollatzResearch.WordTrace]
  refine ⟨22850076919330332331084133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15233384612886888220722755 22850076919330332331084133)
  ·
    refine ⟨4284389422374437312078275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22850076919330332331084133 4284389422374437312078275)
    ·
      refine ⟨6426584133561655968117413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4284389422374437312078275 6426584133561655968117413)
      ·
        refine ⟨1204984525042810494022015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6426584133561655968117413 1204984525042810494022015)
        ·
          refine ⟨1807476787564215741033023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1204984525042810494022015 1807476787564215741033023)
          ·
            refine ⟨2711215181346323611549535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1807476787564215741033023 2711215181346323611549535)
            ·
              refine ⟨4066822772019485417324303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2711215181346323611549535 4066822772019485417324303)
              ·
                refine ⟨6100234158029228125986455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4066822772019485417324303 6100234158029228125986455)
                ·
                  refine ⟨9150351237043842188979683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6100234158029228125986455 9150351237043842188979683)
                  ·
                    refine ⟨13725526855565763283469525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9150351237043842188979683 13725526855565763283469525)
                    ·
                      refine ⟨321692035677322576956317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 13725526855565763283469525 321692035677322576956317)
                      ·
                        rfl

theorem cell23_626493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_626493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626493 prefixEnd_626493 := by exact prefixLift 626493
  have htrace : WordTrace (prefixWord ++ tailWord_626493) baseStart_626493 baseEnd_626493 := by
    simpa [prefixWord, tailWord_626493, baseEnd_626493] using wordTrace_append hprefix tailTrace_626493
  have hstable : (prefixWord ++ tailWord_626493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626493).length < 2 ^ (prefixWord ++ tailWord_626493).sum := by decide
  have hdescent : baseEnd_626493 < baseStart_626493 := by decide
  rcases family_descends (prefixWord ++ tailWord_626493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626540 : List Nat := [2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 3]
def baseStart_626540 : Nat := 118140960795 + 626540 * 2 ^ 59
def prefixEnd_626540 : Nat := 4983230072969 + 3 ^ 40 * 626540 * 2
def baseEnd_626540 : Nat := 321716169268083893068601

theorem tailTrace_626540 : CollatzResearch.WordTrace tailWord_626540 prefixEnd_626540 321716169268083893068601 := by
  unfold tailWord_626540
  simp only [CollatzResearch.WordTrace]
  refine ⟨11425895575080029679022537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15234527433440039572030049 11425895575080029679022537)
  ·
    refine ⟨8569421681310022259266903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11425895575080029679022537 8569421681310022259266903)
    ·
      refine ⟨12854132521965033388900355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8569421681310022259266903 12854132521965033388900355)
      ·
        refine ⟨19281198782947550083350533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12854132521965033388900355 19281198782947550083350533)
        ·
          refine ⟨3615224771802665640628225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19281198782947550083350533 3615224771802665640628225)
          ·
            refine ⟨2711418578851999230471169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3615224771802665640628225 2711418578851999230471169)
            ·
              refine ⟨2033563934138999422853377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2711418578851999230471169 2033563934138999422853377)
              ·
                refine ⟨1525172950604249567140033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2033563934138999422853377 1525172950604249567140033)
                ·
                  refine ⟨1143879712953187175355025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1525172950604249567140033 1143879712953187175355025)
                  ·
                    refine ⟨857909784714890381516269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1143879712953187175355025 857909784714890381516269)
                    ·
                      refine ⟨321716169268083893068601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 857909784714890381516269 321716169268083893068601)
                      ·
                        rfl

theorem cell23_626540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 3].length) (baseStart_626540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626540 prefixEnd_626540 := by exact prefixLift 626540
  have htrace : WordTrace (prefixWord ++ tailWord_626540) baseStart_626540 baseEnd_626540 := by
    simpa [prefixWord, tailWord_626540, baseEnd_626540] using wordTrace_append hprefix tailTrace_626540
  have hstable : (prefixWord ++ tailWord_626540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626540).length < 2 ^ (prefixWord ++ tailWord_626540).sum := by decide
  have hdescent : baseEnd_626540 < baseStart_626540 := by decide
  rcases family_descends (prefixWord ++ tailWord_626540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626594 : List Nat := [3, 3, 1, 2, 4, 1, 1, 2, 6]
def baseStart_626594 : Nat := 118140960795 + 626594 * 2 ^ 59
def prefixEnd_626594 : Nat := 4983230072969 + 3 ^ 40 * 626594 * 2
def baseEnd_626594 : Nat := 35749321913714075754817

theorem tailTrace_626594 : CollatzResearch.WordTrace tailWord_626594 prefixEnd_626594 35749321913714075754817 := by
  unfold tailWord_626594
  simp only [CollatzResearch.WordTrace]
  refine ⟨5713440172991106645127709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15235840461309617720340557 5713440172991106645127709)
  ·
    refine ⟨2142540064871664991922891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5713440172991106645127709 2142540064871664991922891)
    ·
      refine ⟨3213810097307497487884337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2142540064871664991922891 3213810097307497487884337)
      ·
        refine ⟨2410357572980623115913253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3213810097307497487884337 2410357572980623115913253)
        ·
          refine ⟨451942044933866834233735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2410357572980623115913253 451942044933866834233735)
          ·
            refine ⟨677913067400800251350603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 451942044933866834233735 677913067400800251350603)
            ·
              refine ⟨1016869601101200377025905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 677913067400800251350603 1016869601101200377025905)
              ·
                refine ⟨762652200825900282769429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1016869601101200377025905 762652200825900282769429)
                ·
                  refine ⟨35749321913714075754817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 762652200825900282769429 35749321913714075754817)
                  ·
                    rfl

theorem cell23_626594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_626594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626594 prefixEnd_626594 := by exact prefixLift 626594
  have htrace : WordTrace (prefixWord ++ tailWord_626594) baseStart_626594 baseEnd_626594 := by
    simpa [prefixWord, tailWord_626594, baseEnd_626594] using wordTrace_append hprefix tailTrace_626594
  have hstable : (prefixWord ++ tailWord_626594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626594).length < 2 ^ (prefixWord ++ tailWord_626594).sum := by decide
  have hdescent : baseEnd_626594 < baseStart_626594 := by decide
  rcases family_descends (prefixWord ++ tailWord_626594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626623 : List Nat := [1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 6]
def baseStart_626623 : Nat := 118140960795 + 626623 * 2 ^ 59
def prefixEnd_626623 : Nat := 4983230072969 + 3 ^ 40 * 626623 * 2
def baseEnd_626623 : Nat := 321758788162407068330719

theorem tailTrace_626623 : CollatzResearch.WordTrace tailWord_626623 prefixEnd_626623 321758788162407068330719 := by
  unfold tailWord_626623
  simp only [CollatzResearch.WordTrace]
  refine ⟨22854818408859364533316523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15236545605906243022211015 22854818408859364533316523)
  ·
    refine ⟨34282227613289046799974785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22854818408859364533316523 34282227613289046799974785)
    ·
      refine ⟨25711670709966785099981089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34282227613289046799974785 25711670709966785099981089)
      ·
        refine ⟨19283753032475088824985817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25711670709966785099981089 19283753032475088824985817)
        ·
          refine ⟨14462814774356316618739363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19283753032475088824985817 14462814774356316618739363)
          ·
            refine ⟨21694222161534474928109045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14462814774356316618739363 21694222161534474928109045)
            ·
              refine ⟨2033833327643857024510223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21694222161534474928109045 2033833327643857024510223)
              ·
                refine ⟨3050749991465785536765335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033833327643857024510223 3050749991465785536765335)
                ·
                  refine ⟨4576124987198678305148003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3050749991465785536765335 4576124987198678305148003)
                  ·
                    refine ⟨6864187480798017457722005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4576124987198678305148003 6864187480798017457722005)
                    ·
                      refine ⟨321758788162407068330719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6864187480798017457722005 321758788162407068330719)
                      ·
                        rfl

theorem cell23_626623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 1, 1, 1, 6].length) (baseStart_626623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626623 prefixEnd_626623 := by exact prefixLift 626623
  have htrace : WordTrace (prefixWord ++ tailWord_626623) baseStart_626623 baseEnd_626623 := by
    simpa [prefixWord, tailWord_626623, baseEnd_626623] using wordTrace_append hprefix tailTrace_626623
  have hstable : (prefixWord ++ tailWord_626623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626623).length < 2 ^ (prefixWord ++ tailWord_626623).sum := by decide
  have hdescent : baseEnd_626623 < baseStart_626623 := by decide
  rcases family_descends (prefixWord ++ tailWord_626623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626650 : List Nat := [3, 1, 1, 2, 5, 2, 9]
def baseStart_626650 : Nat := 118140960795 + 626650 * 2 ^ 59
def prefixEnd_626650 : Nat := 4983230072969 + 3 ^ 40 * 626650 * 2
def baseEnd_626650 : Nat := 3972501878272573613495

theorem tailTrace_626650 : CollatzResearch.WordTrace tailWord_626650 prefixEnd_626650 3972501878272573613495 := by
  unfold tailWord_626650
  simp only [CollatzResearch.WordTrace]
  refine ⟨5713950794940387036137351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15237202119841032096366269 5713950794940387036137351)
  ·
    refine ⟨8570926192410580554206027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5713950794940387036137351 8570926192410580554206027)
    ·
      refine ⟨12856389288615870831309041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8570926192410580554206027 12856389288615870831309041)
      ·
        refine ⟨9642291966461903123481781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12856389288615870831309041 9642291966461903123481781)
        ·
          refine ⟨903964871855803417826417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 9642291966461903123481781 903964871855803417826417)
          ·
            refine ⟨677973653891852563369813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 903964871855803417826417 677973653891852563369813)
            ·
              refine ⟨3972501878272573613495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 677973653891852563369813 3972501878272573613495)
              ·
                rfl

theorem cell23_626650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 9].length) (baseStart_626650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626650 prefixEnd_626650 := by exact prefixLift 626650
  have htrace : WordTrace (prefixWord ++ tailWord_626650) baseStart_626650 baseEnd_626650 := by
    simpa [prefixWord, tailWord_626650, baseEnd_626650] using wordTrace_append hprefix tailTrace_626650
  have hstable : (prefixWord ++ tailWord_626650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626650).length < 2 ^ (prefixWord ++ tailWord_626650).sum := by decide
  have hdescent : baseEnd_626650 < baseStart_626650 := by decide
  rcases family_descends (prefixWord ++ tailWord_626650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626711 : List Nat := [1, 1, 3, 5, 2, 1, 2, 2, 2, 1, 3]
def baseStart_626711 : Nat := 118140960795 + 626711 * 2 ^ 59
def prefixEnd_626711 : Nat := 4983230072969 + 3 ^ 40 * 626711 * 2
def baseEnd_626711 : Nat := 321803974460002724030315

theorem tailTrace_626711 : CollatzResearch.WordTrace tailWord_626711 prefixEnd_626711 321803974460002724030315 := by
  unfold tailWord_626711
  simp only [CollatzResearch.WordTrace]
  refine ⟨22858028032540555562519987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15238685355027037041679991 22858028032540555562519987)
  ·
    refine ⟨34287042048810833343779981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22858028032540555562519987 34287042048810833343779981)
    ·
      refine ⟨12857640768304062503917493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34287042048810833343779981 12857640768304062503917493)
      ·
        refine ⟨1205403822028505859742265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12857640768304062503917493 1205403822028505859742265)
        ·
          refine ⟨904052866521379394806699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1205403822028505859742265 904052866521379394806699)
          ·
            refine ⟨1356079299782069092210049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904052866521379394806699 1356079299782069092210049)
            ·
              refine ⟨1017059474836551819157537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356079299782069092210049 1017059474836551819157537)
              ·
                refine ⟨762794606127413864368153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017059474836551819157537 762794606127413864368153)
                ·
                  refine ⟨572095954595560398276115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 762794606127413864368153 572095954595560398276115)
                  ·
                    refine ⟨858143931893340597414173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 572095954595560398276115 858143931893340597414173)
                    ·
                      refine ⟨321803974460002724030315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 858143931893340597414173 321803974460002724030315)
                      ·
                        rfl

theorem cell23_626711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_626711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626711 prefixEnd_626711 := by exact prefixLift 626711
  have htrace : WordTrace (prefixWord ++ tailWord_626711) baseStart_626711 baseEnd_626711 := by
    simpa [prefixWord, tailWord_626711, baseEnd_626711] using wordTrace_append hprefix tailTrace_626711
  have hstable : (prefixWord ++ tailWord_626711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626711).length < 2 ^ (prefixWord ++ tailWord_626711).sum := by decide
  have hdescent : baseEnd_626711 < baseStart_626711 := by decide
  rcases family_descends (prefixWord ++ tailWord_626711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626713 : List Nat := [1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 6]
def baseStart_626713 : Nat := 118140960795 + 626713 * 2 ^ 59
def prefixEnd_626713 : Nat := 4983230072969 + 3 ^ 40 * 626713 * 2
def baseEnd_626713 : Nat := 321805001421311716205305

theorem tailTrace_626713 : CollatzResearch.WordTrace tailWord_626713 prefixEnd_626713 321805001421311716205305 := by
  unfold tailWord_626713
  simp only [CollatzResearch.WordTrace]
  refine ⟨22858100978533309904092793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15238733985688873269395195 22858100978533309904092793)
  ·
    refine ⟨17143575733899982428069595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22858100978533309904092793 17143575733899982428069595)
    ·
      refine ⟨25715363600849973642104393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17143575733899982428069595 25715363600849973642104393)
      ·
        refine ⟨19286522700637480231578295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25715363600849973642104393 19286522700637480231578295)
        ·
          refine ⟨28929784050956220347367443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19286522700637480231578295 28929784050956220347367443)
          ·
            refine ⟨43394676076434330521051165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28929784050956220347367443 43394676076434330521051165)
            ·
              refine ⟨16273003528662873945394187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43394676076434330521051165 16273003528662873945394187)
              ·
                refine ⟨24409505292994310918091281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16273003528662873945394187 24409505292994310918091281)
                ·
                  refine ⟨18307128969745733188568461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24409505292994310918091281 18307128969745733188568461)
                  ·
                    refine ⟨6865173363654649945713173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18307128969745733188568461 6865173363654649945713173)
                    ·
                      refine ⟨321805001421311716205305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6865173363654649945713173 321805001421311716205305)
                      ·
                        rfl

theorem cell23_626713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 1, 2, 3, 6].length) (baseStart_626713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626713 prefixEnd_626713 := by exact prefixLift 626713
  have htrace : WordTrace (prefixWord ++ tailWord_626713) baseStart_626713 baseEnd_626713 := by
    simpa [prefixWord, tailWord_626713, baseEnd_626713] using wordTrace_append hprefix tailTrace_626713
  have hstable : (prefixWord ++ tailWord_626713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626713).length < 2 ^ (prefixWord ++ tailWord_626713).sum := by decide
  have hdescent : baseEnd_626713 < baseStart_626713 := by decide
  rcases family_descends (prefixWord ++ tailWord_626713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626734 : List Nat := [4, 1, 3, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_626734 : Nat := 118140960795 + 626734 * 2 ^ 59
def prefixEnd_626734 : Nat := 4983230072969 + 3 ^ 40 * 626734 * 2
def baseEnd_626734 : Nat := 321815784515056134042709

theorem tailTrace_626734 : CollatzResearch.WordTrace tailWord_626734 prefixEnd_626734 321815784515056134042709 := by
  unfold tailWord_626734
  simp only [CollatzResearch.WordTrace]
  refine ⟨2857358363932153811325907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15239244607638153660404837 2857358363932153811325907)
  ·
    refine ⟨4286037545898230716988861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2857358363932153811325907 4286037545898230716988861)
    ·
      refine ⟨1607264079711836518870823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4286037545898230716988861 1607264079711836518870823)
      ·
        refine ⟨2410896119567754778306235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607264079711836518870823 2410896119567754778306235)
        ·
          refine ⟨3616344179351632167459353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2410896119567754778306235 3616344179351632167459353)
          ·
            refine ⟨2712258134513724125594515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3616344179351632167459353 2712258134513724125594515)
            ·
              refine ⟨4068387201770586188391773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2712258134513724125594515 4068387201770586188391773)
              ·
                refine ⟨1525645200663969820646915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4068387201770586188391773 1525645200663969820646915)
                ·
                  refine ⟨2288467800995954730970373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1525645200663969820646915 2288467800995954730970373)
                  ·
                    refine ⟨429087712686741512056945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2288467800995954730970373 429087712686741512056945)
                    ·
                      refine ⟨321815784515056134042709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 429087712686741512056945 321815784515056134042709)
                      ·
                        rfl

theorem cell23_626734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_626734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626734 prefixEnd_626734 := by exact prefixLift 626734
  have htrace : WordTrace (prefixWord ++ tailWord_626734) baseStart_626734 baseEnd_626734 := by
    simpa [prefixWord, tailWord_626734, baseEnd_626734] using wordTrace_append hprefix tailTrace_626734
  have hstable : (prefixWord ++ tailWord_626734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626734).length < 2 ^ (prefixWord ++ tailWord_626734).sum := by decide
  have hdescent : baseEnd_626734 < baseStart_626734 := by decide
  rcases family_descends (prefixWord ++ tailWord_626734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626774 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 7]
def baseStart_626774 : Nat := 118140960795 + 626774 * 2 ^ 59
def prefixEnd_626774 : Nat := 4983230072969 + 3 ^ 40 * 626774 * 2
def baseEnd_626774 : Nat := 35759591526803997504725

theorem tailTrace_626774 : CollatzResearch.WordTrace tailWord_626774 prefixEnd_626774 35759591526803997504725 := by
  unfold tailWord_626774
  simp only [CollatzResearch.WordTrace]
  refine ⟨1428770364457019832628961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 15240217220874878214708917 1428770364457019832628961)
  ·
    refine ⟨1071577773342764874471721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1428770364457019832628961 1071577773342764874471721)
    ·
      refine ⟨803683330007073655853791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1071577773342764874471721 803683330007073655853791)
      ·
        refine ⟨1205524995010610483780687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803683330007073655853791 1205524995010610483780687)
        ·
          refine ⟨1808287492515915725671031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205524995010610483780687 1808287492515915725671031)
          ·
            refine ⟨2712431238773873588506547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808287492515915725671031 2712431238773873588506547)
            ·
              refine ⟨4068646858160810382759821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2712431238773873588506547 4068646858160810382759821)
              ·
                refine ⟨1525742571810303893534933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4068646858160810382759821 1525742571810303893534933)
                ·
                  refine ⟨35759591526803997504725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1525742571810303893534933 35759591526803997504725)
                  ·
                    rfl

theorem cell23_626774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_626774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626774 prefixEnd_626774 := by exact prefixLift 626774
  have htrace : WordTrace (prefixWord ++ tailWord_626774) baseStart_626774 baseEnd_626774 := by
    simpa [prefixWord, tailWord_626774, baseEnd_626774] using wordTrace_append hprefix tailTrace_626774
  have hstable : (prefixWord ++ tailWord_626774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626774).length < 2 ^ (prefixWord ++ tailWord_626774).sum := by decide
  have hdescent : baseEnd_626774 < baseStart_626774 := by decide
  rcases family_descends (prefixWord ++ tailWord_626774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626824 : List Nat := [2, 1, 3, 4, 1, 2, 1, 2, 2, 1, 4]
def baseStart_626824 : Nat := 118140960795 + 626824 * 2 ^ 59
def prefixEnd_626824 : Nat := 4983230072969 + 3 ^ 40 * 626824 * 2
def baseEnd_626824 : Nat := 321861997773960781917295

theorem tailTrace_626824 : CollatzResearch.WordTrace tailWord_626824 prefixEnd_626824 321861997773960781917295 := by
  unfold tailWord_626824
  simp only [CollatzResearch.WordTrace]
  refine ⟨11431074740565587930691763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15241432987420783907589017 11431074740565587930691763)
  ·
    refine ⟨17146612110848381896037645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11431074740565587930691763 17146612110848381896037645)
    ·
      refine ⟨6429979541568143211014117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17146612110848381896037645 6429979541568143211014117)
      ·
        refine ⟨1205621164044026852065147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6429979541568143211014117 1205621164044026852065147)
        ·
          refine ⟨1808431746066040278097721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205621164044026852065147 1808431746066040278097721)
          ·
            refine ⟨1356323809549530208573291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1808431746066040278097721 1356323809549530208573291)
            ·
              refine ⟨2034485714324295312859937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356323809549530208573291 2034485714324295312859937)
              ·
                refine ⟨1525864285743221484644953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2034485714324295312859937 1525864285743221484644953)
                ·
                  refine ⟨1144398214307416113483715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1525864285743221484644953 1144398214307416113483715)
                  ·
                    refine ⟨1716597321461124170225573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1144398214307416113483715 1716597321461124170225573)
                    ·
                      refine ⟨321861997773960781917295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1716597321461124170225573 321861997773960781917295)
                      ·
                        rfl

theorem cell23_626824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_626824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626824 prefixEnd_626824 := by exact prefixLift 626824
  have htrace : WordTrace (prefixWord ++ tailWord_626824) baseStart_626824 baseEnd_626824 := by
    simpa [prefixWord, tailWord_626824, baseEnd_626824] using wordTrace_append hprefix tailTrace_626824
  have hstable : (prefixWord ++ tailWord_626824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626824).length < 2 ^ (prefixWord ++ tailWord_626824).sum := by decide
  have hdescent : baseEnd_626824 < baseStart_626824 := by decide
  rcases family_descends (prefixWord ++ tailWord_626824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626861 : List Nat := [1, 5, 2, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_626861 : Nat := 118140960795 + 626861 * 2 ^ 59
def prefixEnd_626861 : Nat := 4983230072969 + 3 ^ 40 * 626861 * 2
def baseEnd_626861 : Nat := 321880996558177137154625

theorem tailTrace_626861 : CollatzResearch.WordTrace tailWord_626861 prefixEnd_626861 321880996558177137154625 := by
  unfold tailWord_626861
  simp only [CollatzResearch.WordTrace]
  refine ⟨22863498981997131180480437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15242332654664754120320291 22863498981997131180480437)
  ·
    refine ⟨2143453029562231048170041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22863498981997131180480437 2143453029562231048170041)
    ·
      refine ⟨1607589772171673286127531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2143453029562231048170041 1607589772171673286127531)
      ·
        refine ⟨2411384658257509929191297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607589772171673286127531 2411384658257509929191297)
        ·
          refine ⟨1808538493693132446893473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2411384658257509929191297 1808538493693132446893473)
          ·
            refine ⟨1356403870269849335170105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1808538493693132446893473 1356403870269849335170105)
            ·
              refine ⟨1017302902702387001377579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356403870269849335170105 1017302902702387001377579)
              ·
                refine ⟨1525954354053580502066369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1017302902702387001377579 1525954354053580502066369)
                ·
                  refine ⟨1144465765540185376549777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1525954354053580502066369 1144465765540185376549777)
                  ·
                    refine ⟨858349324155139032412333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1144465765540185376549777 858349324155139032412333)
                    ·
                      refine ⟨321880996558177137154625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 858349324155139032412333 321880996558177137154625)
                      ·
                        rfl

theorem cell23_626861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_626861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626861 prefixEnd_626861 := by exact prefixLift 626861
  have htrace : WordTrace (prefixWord ++ tailWord_626861) baseStart_626861 baseEnd_626861 := by
    simpa [prefixWord, tailWord_626861, baseEnd_626861] using wordTrace_append hprefix tailTrace_626861
  have hstable : (prefixWord ++ tailWord_626861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626861).length < 2 ^ (prefixWord ++ tailWord_626861).sum := by decide
  have hdescent : baseEnd_626861 < baseStart_626861 := by decide
  rcases family_descends (prefixWord ++ tailWord_626861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626881 : List Nat := [1, 2, 6, 1, 2, 1, 2, 2, 6]
def baseStart_626881 : Nat := 118140960795 + 626881 * 2 ^ 59
def prefixEnd_626881 : Nat := 4983230072969 + 3 ^ 40 * 626881 * 2
def baseEnd_626881 : Nat := 35765696241251895433837

theorem tailTrace_626881 : CollatzResearch.WordTrace tailWord_626881 prefixEnd_626881 35765696241251895433837 := by
  unfold tailWord_626881
  simp only [CollatzResearch.WordTrace]
  refine ⟨22864228441924674596208497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15242818961283116397472331 22864228441924674596208497)
  ·
    refine ⟨17148171331443505947156373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22864228441924674596208497 17148171331443505947156373)
    ·
      refine ⟨803820531161414341272955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 17148171331443505947156373 803820531161414341272955)
      ·
        refine ⟨1205730796742121511909433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 803820531161414341272955 1205730796742121511909433)
        ·
          refine ⟨904298097556591133932075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1205730796742121511909433 904298097556591133932075)
          ·
            refine ⟨1356447146334886700898113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904298097556591133932075 1356447146334886700898113)
            ·
              refine ⟨1017335359751165025673585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356447146334886700898113 1017335359751165025673585)
              ·
                refine ⟨763001519813373769255189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017335359751165025673585 763001519813373769255189)
                ·
                  refine ⟨35765696241251895433837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 763001519813373769255189 35765696241251895433837)
                  ·
                    rfl

theorem cell23_626881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 6].length) (baseStart_626881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626881 prefixEnd_626881 := by exact prefixLift 626881
  have htrace : WordTrace (prefixWord ++ tailWord_626881) baseStart_626881 baseEnd_626881 := by
    simpa [prefixWord, tailWord_626881, baseEnd_626881] using wordTrace_append hprefix tailTrace_626881
  have hstable : (prefixWord ++ tailWord_626881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626881).length < 2 ^ (prefixWord ++ tailWord_626881).sum := by decide
  have hdescent : baseEnd_626881 < baseStart_626881 := by decide
  rcases family_descends (prefixWord ++ tailWord_626881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626891 : List Nat := [1, 1, 1, 1, 3, 2, 5, 4, 1, 1, 3]
def baseStart_626891 : Nat := 118140960795 + 626891 * 2 ^ 59
def prefixEnd_626891 : Nat := 4983230072969 + 3 ^ 40 * 626891 * 2
def baseEnd_626891 : Nat := 321896400977812019779487

theorem tailTrace_626891 : CollatzResearch.WordTrace tailWord_626891 prefixEnd_626891 321896400977812019779487 := by
  unfold tailWord_626891
  simp only [CollatzResearch.WordTrace]
  refine ⟨22864593171888446304072527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15243062114592297536048351 22864593171888446304072527)
  ·
    refine ⟨34296889757832669456108791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22864593171888446304072527 34296889757832669456108791)
    ·
      refine ⟨51445334636749004184163187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34296889757832669456108791 51445334636749004184163187)
      ·
        refine ⟨77168001955123506276244781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51445334636749004184163187 77168001955123506276244781)
        ·
          refine ⟨28938000733171314853591793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77168001955123506276244781 28938000733171314853591793)
          ·
            refine ⟨21703500549878486140193845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28938000733171314853591793 21703500549878486140193845)
            ·
              refine ⟨2034703176551108075643173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21703500549878486140193845 2034703176551108075643173)
              ·
                refine ⟨381506845603332764183095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2034703176551108075643173 381506845603332764183095)
                ·
                  refine ⟨572260268404999146274643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381506845603332764183095 572260268404999146274643)
                  ·
                    refine ⟨858390402607498719411965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 572260268404999146274643 858390402607498719411965)
                    ·
                      refine ⟨321896400977812019779487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 858390402607498719411965 321896400977812019779487)
                      ·
                        rfl

theorem cell23_626891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 5, 4, 1, 1, 3].length) (baseStart_626891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626891 prefixEnd_626891 := by exact prefixLift 626891
  have htrace : WordTrace (prefixWord ++ tailWord_626891) baseStart_626891 baseEnd_626891 := by
    simpa [prefixWord, tailWord_626891, baseEnd_626891] using wordTrace_append hprefix tailTrace_626891
  have hstable : (prefixWord ++ tailWord_626891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626891).length < 2 ^ (prefixWord ++ tailWord_626891).sum := by decide
  have hdescent : baseEnd_626891 < baseStart_626891 := by decide
  rcases family_descends (prefixWord ++ tailWord_626891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626897 : List Nat := [1, 2, 2, 1, 2, 2, 3, 2, 3, 1, 4]
def baseStart_626897 : Nat := 118140960795 + 626897 * 2 ^ 59
def prefixEnd_626897 : Nat := 4983230072969 + 3 ^ 40 * 626897 * 2
def baseEnd_626897 : Nat := 321899481861738996304459

theorem tailTrace_626897 : CollatzResearch.WordTrace tailWord_626897 prefixEnd_626897 321899481861738996304459 := by
  unfold tailWord_626897
  simp only [CollatzResearch.WordTrace]
  refine ⟨22864812009866709328790945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15243208006577806219193963 22864812009866709328790945)
  ·
    refine ⟨17148609007400031996593209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22864812009866709328790945 17148609007400031996593209)
    ·
      refine ⟨12861456755550023997444907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17148609007400031996593209 12861456755550023997444907)
      ·
        refine ⟨19292185133325035996167361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12861456755550023997444907 19292185133325035996167361)
        ·
          refine ⟨14469138849993776997125521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19292185133325035996167361 14469138849993776997125521)
          ·
            refine ⟨10851854137495332747844141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14469138849993776997125521 10851854137495332747844141)
            ·
              refine ⟨4069445301560749780441553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10851854137495332747844141 4069445301560749780441553)
              ·
                refine ⟨3052083976170562335331165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4069445301560749780441553 3052083976170562335331165)
                ·
                  refine ⟨1144531491063960875749187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3052083976170562335331165 1144531491063960875749187)
                  ·
                    refine ⟨1716797236595941313623781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1144531491063960875749187 1716797236595941313623781)
                    ·
                      refine ⟨321899481861738996304459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1716797236595941313623781 321899481861738996304459)
                      ·
                        rfl

theorem cell23_626897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_626897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626897 prefixEnd_626897 := by exact prefixLift 626897
  have htrace : WordTrace (prefixWord ++ tailWord_626897) baseStart_626897 baseEnd_626897 := by
    simpa [prefixWord, tailWord_626897, baseEnd_626897] using wordTrace_append hprefix tailTrace_626897
  have hstable : (prefixWord ++ tailWord_626897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626897).length < 2 ^ (prefixWord ++ tailWord_626897).sum := by decide
  have hdescent : baseEnd_626897 < baseStart_626897 := by decide
  rcases family_descends (prefixWord ++ tailWord_626897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626925 : List Nat := [1, 5, 1, 2, 3, 1, 2, 3, 1, 1, 3]
def baseStart_626925 : Nat := 118140960795 + 626925 * 2 ^ 59
def prefixEnd_626925 : Nat := 4983230072969 + 3 ^ 40 * 626925 * 2
def baseEnd_626925 : Nat := 321913859320064886754331

theorem tailTrace_626925 : CollatzResearch.WordTrace tailWord_626925 prefixEnd_626925 321913859320064886754331 := by
  unfold tailWord_626925
  simp only [CollatzResearch.WordTrace]
  refine ⟨22865833253765270110810229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15243888835843513407206819 22865833253765270110810229)
  ·
    refine ⟨2143671867540494072888459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22865833253765270110810229 2143671867540494072888459)
    ·
      refine ⟨3215507801310741109332689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2143671867540494072888459 3215507801310741109332689)
      ·
        refine ⟨2411630850983055831999517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3215507801310741109332689 2411630850983055831999517)
        ·
          refine ⟨904361569118645936999819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2411630850983055831999517 904361569118645936999819)
          ·
            refine ⟨1356542353677968905499729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904361569118645936999819 1356542353677968905499729)
            ·
              refine ⟨1017406765258476679124797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356542353677968905499729 1017406765258476679124797)
              ·
                refine ⟨381527536971928754671799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1017406765258476679124797 381527536971928754671799)
                ·
                  refine ⟨572291305457893132007699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381527536971928754671799 572291305457893132007699)
                  ·
                    refine ⟨858436958186839698011549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 572291305457893132007699 858436958186839698011549)
                    ·
                      refine ⟨321913859320064886754331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 858436958186839698011549 321913859320064886754331)
                      ·
                        rfl

theorem cell23_626925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_626925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626925 prefixEnd_626925 := by exact prefixLift 626925
  have htrace : WordTrace (prefixWord ++ tailWord_626925) baseStart_626925 baseEnd_626925 := by
    simpa [prefixWord, tailWord_626925, baseEnd_626925] using wordTrace_append hprefix tailTrace_626925
  have hstable : (prefixWord ++ tailWord_626925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626925).length < 2 ^ (prefixWord ++ tailWord_626925).sum := by decide
  have hdescent : baseEnd_626925 < baseStart_626925 := by decide
  rcases family_descends (prefixWord ++ tailWord_626925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626951 : List Nat := [1, 1, 4, 5, 1, 1, 1, 2, 1, 1, 5]
def baseStart_626951 : Nat := 118140960795 + 626951 * 2 ^ 59
def prefixEnd_626951 : Nat := 4983230072969 + 3 ^ 40 * 626951 * 2
def baseEnd_626951 : Nat := 321927209817081785029211

theorem tailTrace_626951 : CollatzResearch.WordTrace tailWord_626951 prefixEnd_626951 321927209817081785029211 := by
  unfold tailWord_626951
  simp only [CollatzResearch.WordTrace]
  refine ⟨22866781551671076551256707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15244521034447384367504471 22866781551671076551256707)
  ·
    refine ⟨34300172327506614826885061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22866781551671076551256707 34300172327506614826885061)
    ·
      refine ⟨6431282311407490280040949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34300172327506614826885061 6431282311407490280040949)
      ·
        refine ⟨602932716694452213753839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6431282311407490280040949 602932716694452213753839)
        ·
          refine ⟨904399075041678320630759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 602932716694452213753839 904399075041678320630759)
          ·
            refine ⟨1356598612562517480946139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904399075041678320630759 1356598612562517480946139)
            ·
              refine ⟨2034897918843776221419209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356598612562517480946139 2034897918843776221419209)
              ·
                refine ⟨1526173439132832166064407, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2034897918843776221419209 1526173439132832166064407)
                ·
                  refine ⟨2289260158699248249096611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526173439132832166064407 2289260158699248249096611)
                  ·
                    refine ⟨3433890238048872373644917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2289260158699248249096611 3433890238048872373644917)
                    ·
                      refine ⟨321927209817081785029211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3433890238048872373644917 321927209817081785029211)
                      ·
                        rfl

theorem cell23_626951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 1, 2, 1, 1, 5].length) (baseStart_626951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626951 prefixEnd_626951 := by exact prefixLift 626951
  have htrace : WordTrace (prefixWord ++ tailWord_626951) baseStart_626951 baseEnd_626951 := by
    simpa [prefixWord, tailWord_626951, baseEnd_626951] using wordTrace_append hprefix tailTrace_626951
  have hstable : (prefixWord ++ tailWord_626951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626951).length < 2 ^ (prefixWord ++ tailWord_626951).sum := by decide
  have hdescent : baseEnd_626951 < baseStart_626951 := by decide
  rcases family_descends (prefixWord ++ tailWord_626951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626977 : List Nat := [1, 2, 3, 2, 1, 1, 3, 1, 2, 2, 5]
def baseStart_626977 : Nat := 118140960795 + 626977 * 2 ^ 59
def prefixEnd_626977 : Nat := 4983230072969 + 3 ^ 40 * 626977 * 2
def baseEnd_626977 : Nat := 321940560314098683304091

theorem tailTrace_626977 : CollatzResearch.WordTrace tailWord_626977 prefixEnd_626977 321940560314098683304091 := by
  unfold tailWord_626977
  simp only [CollatzResearch.WordTrace]
  refine ⟨22867729849576882991703185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15245153233051255327802123 22867729849576882991703185)
  ·
    refine ⟨17150797387182662243777389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22867729849576882991703185 17150797387182662243777389)
    ·
      refine ⟨6431549020193498341416521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17150797387182662243777389 6431549020193498341416521)
      ·
        refine ⟨4823661765145123756062391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6431549020193498341416521 4823661765145123756062391)
        ·
          refine ⟨7235492647717685634093587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4823661765145123756062391 7235492647717685634093587)
          ·
            refine ⟨10853238971576528451140381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7235492647717685634093587 10853238971576528451140381)
            ·
              refine ⟨4069964614341198169177643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10853238971576528451140381 4069964614341198169177643)
              ·
                refine ⟨6104946921511797253766465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4069964614341198169177643 6104946921511797253766465)
                ·
                  refine ⟨4578710191133847940324849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6104946921511797253766465 4578710191133847940324849)
                  ·
                    refine ⟨3434032643350385955243637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4578710191133847940324849 3434032643350385955243637)
                    ·
                      refine ⟨321940560314098683304091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3434032643350385955243637 321940560314098683304091)
                      ·
                        rfl

theorem cell23_626977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 1, 2, 2, 5].length) (baseStart_626977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626977 prefixEnd_626977 := by exact prefixLift 626977
  have htrace : WordTrace (prefixWord ++ tailWord_626977) baseStart_626977 baseEnd_626977 := by
    simpa [prefixWord, tailWord_626977, baseEnd_626977] using wordTrace_append hprefix tailTrace_626977
  have hstable : (prefixWord ++ tailWord_626977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626977).length < 2 ^ (prefixWord ++ tailWord_626977).sum := by decide
  have hdescent : baseEnd_626977 < baseStart_626977 := by decide
  rcases family_descends (prefixWord ++ tailWord_626977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_626991 : List Nat := [1, 1, 2, 1, 2, 1, 6, 3, 1, 3, 2]
def baseStart_626991 : Nat := 118140960795 + 626991 * 2 ^ 59
def prefixEnd_626991 : Nat := 4983230072969 + 3 ^ 40 * 626991 * 2
def baseEnd_626991 : Nat := 321947749043261628529027

theorem tailTrace_626991 : CollatzResearch.WordTrace tailWord_626991 prefixEnd_626991 321947749043261628529027 := by
  unfold tailWord_626991
  simp only [CollatzResearch.WordTrace]
  refine ⟨22868240471526163382712827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15245493647684108921808551 22868240471526163382712827)
  ·
    refine ⟨34302360707289245074069241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22868240471526163382712827 34302360707289245074069241)
    ·
      refine ⟨25726770530466933805551931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34302360707289245074069241 25726770530466933805551931)
      ·
        refine ⟨38590155795700400708327897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25726770530466933805551931 38590155795700400708327897)
        ·
          refine ⟨28942616846775300531245923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38590155795700400708327897 28942616846775300531245923)
          ·
            refine ⟨43413925270162950796868885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28942616846775300531245923 43413925270162950796868885)
            ·
              refine ⟨2035027747038888318603229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43413925270162950796868885 2035027747038888318603229)
              ·
                refine ⟨763135405139583119476211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2035027747038888318603229 763135405139583119476211)
                ·
                  refine ⟨1144703107709374679214317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763135405139583119476211 1144703107709374679214317)
                  ·
                    refine ⟨429263665391015504705369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1144703107709374679214317 429263665391015504705369)
                    ·
                      refine ⟨321947749043261628529027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 429263665391015504705369 321947749043261628529027)
                      ·
                        rfl

theorem cell23_626991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 3, 1, 3, 2].length) (baseStart_626991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_626991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_626991 prefixEnd_626991 := by exact prefixLift 626991
  have htrace : WordTrace (prefixWord ++ tailWord_626991) baseStart_626991 baseEnd_626991 := by
    simpa [prefixWord, tailWord_626991, baseEnd_626991] using wordTrace_append hprefix tailTrace_626991
  have hstable : (prefixWord ++ tailWord_626991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_626991).length < 2 ^ (prefixWord ++ tailWord_626991).sum := by decide
  have hdescent : baseEnd_626991 < baseStart_626991 := by decide
  rcases family_descends (prefixWord ++ tailWord_626991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627007 : List Nat := [1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 5]
def baseStart_627007 : Nat := 118140960795 + 627007 * 2 ^ 59
def prefixEnd_627007 : Nat := 4983230072969 + 3 ^ 40 * 627007 * 2
def baseEnd_627007 : Nat := 321955964733733565928953

theorem tailTrace_627007 : CollatzResearch.WordTrace tailWord_627007 prefixEnd_627007 321955964733733565928953 := by
  unfold tailWord_627007
  simp only [CollatzResearch.WordTrace]
  refine ⟨22868824039468198115295275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15245882692978798743530183 22868824039468198115295275)
  ·
    refine ⟨34303236059202297172942913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22868824039468198115295275 34303236059202297172942913)
    ·
      refine ⟨25727427044401722879707185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34303236059202297172942913 25727427044401722879707185)
      ·
        refine ⟨19295570283301292159780389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25727427044401722879707185 19295570283301292159780389)
        ·
          refine ⟨3617919428118992279958823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19295570283301292159780389 3617919428118992279958823)
          ·
            refine ⟨5426879142178488419938235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3617919428118992279958823 5426879142178488419938235)
            ·
              refine ⟨8140318713267732629907353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5426879142178488419938235 8140318713267732629907353)
              ·
                refine ⟨6105239034950799472430515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8140318713267732629907353 6105239034950799472430515)
                ·
                  refine ⟨9157858552426199208645773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6105239034950799472430515 9157858552426199208645773)
                  ·
                    refine ⟨3434196957159824703242165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9157858552426199208645773 3434196957159824703242165)
                    ·
                      refine ⟨321955964733733565928953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 3434196957159824703242165 321955964733733565928953)
                      ·
                        rfl

theorem cell23_627007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 5].length) (baseStart_627007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627007 prefixEnd_627007 := by exact prefixLift 627007
  have htrace : WordTrace (prefixWord ++ tailWord_627007) baseStart_627007 baseEnd_627007 := by
    simpa [prefixWord, tailWord_627007, baseEnd_627007] using wordTrace_append hprefix tailTrace_627007
  have hstable : (prefixWord ++ tailWord_627007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627007).length < 2 ^ (prefixWord ++ tailWord_627007).sum := by decide
  have hdescent : baseEnd_627007 < baseStart_627007 := by decide
  rcases family_descends (prefixWord ++ tailWord_627007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627017 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 1, 4, 4]
def baseStart_627017 : Nat := 118140960795 + 627017 * 2 ^ 59
def prefixEnd_627017 : Nat := 4983230072969 + 3 ^ 40 * 627017 * 2
def baseEnd_627017 : Nat := 321961099540278526803907

theorem tailTrace_627017 : CollatzResearch.WordTrace tailWord_627017 prefixEnd_627017 321961099540278526803907 := by
  unfold tailWord_627017
  simp only [CollatzResearch.WordTrace]
  refine ⟨22869188769431969823159305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15246125846287979882106203 22869188769431969823159305)
  ·
    refine ⟨17151891577073977367369479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22869188769431969823159305 17151891577073977367369479)
    ·
      refine ⟨25727837365610966051054219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17151891577073977367369479 25727837365610966051054219)
      ·
        refine ⟨38591756048416449076581329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25727837365610966051054219 38591756048416449076581329)
        ·
          refine ⟨28943817036312336807435997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38591756048416449076581329 28943817036312336807435997)
          ·
            refine ⟨10853931388617126302788499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28943817036312336807435997 10853931388617126302788499)
            ·
              refine ⟨16280897082925689454182749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10853931388617126302788499 16280897082925689454182749)
              ·
                refine ⟨6105336406097133545318531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16280897082925689454182749 6105336406097133545318531)
                ·
                  refine ⟨9158004609145700317977797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6105336406097133545318531 9158004609145700317977797)
                  ·
                    refine ⟨1717125864214818809620837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9158004609145700317977797 1717125864214818809620837)
                    ·
                      refine ⟨321961099540278526803907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1717125864214818809620837 321961099540278526803907)
                      ·
                        rfl

theorem cell23_627017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 1, 4, 4].length) (baseStart_627017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627017 prefixEnd_627017 := by exact prefixLift 627017
  have htrace : WordTrace (prefixWord ++ tailWord_627017) baseStart_627017 baseEnd_627017 := by
    simpa [prefixWord, tailWord_627017, baseEnd_627017] using wordTrace_append hprefix tailTrace_627017
  have hstable : (prefixWord ++ tailWord_627017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627017).length < 2 ^ (prefixWord ++ tailWord_627017).sum := by decide
  have hdescent : baseEnd_627017 < baseStart_627017 := by decide
  rcases family_descends (prefixWord ++ tailWord_627017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627057 : List Nat := [1, 2, 2, 2, 1, 2, 1, 2, 3, 7]
def baseStart_627057 : Nat := 118140960795 + 627057 * 2 ^ 59
def prefixEnd_627057 : Nat := 4983230072969 + 3 ^ 40 * 627057 * 2
def baseEnd_627057 : Nat := 107327212922152790101241

theorem tailTrace_627057 : CollatzResearch.WordTrace tailWord_627057 prefixEnd_627057 107327212922152790101241 := by
  unfold tailWord_627057
  simp only [CollatzResearch.WordTrace]
  refine ⟨22870647689287056654615425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15247098459524704436410283 22870647689287056654615425)
  ·
    refine ⟨17152985766965292490961569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22870647689287056654615425 17152985766965292490961569)
    ·
      refine ⟨12864739325223969368221177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17152985766965292490961569 12864739325223969368221177)
      ·
        refine ⟨9648554493917977026165883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12864739325223969368221177 9648554493917977026165883)
        ·
          refine ⟨14472831740876965539248825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9648554493917977026165883 14472831740876965539248825)
          ·
            refine ⟨10854623805657724154436619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14472831740876965539248825 10854623805657724154436619)
            ·
              refine ⟨16281935708486586231654929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10854623805657724154436619 16281935708486586231654929)
              ·
                refine ⟨12211451781364939673741197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16281935708486586231654929 12211451781364939673741197)
                ·
                  refine ⟨4579294418011852377652949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12211451781364939673741197 4579294418011852377652949)
                  ·
                    refine ⟨107327212922152790101241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 4579294418011852377652949 107327212922152790101241)
                    ·
                      rfl

theorem cell23_627057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 2, 3, 7].length) (baseStart_627057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627057 prefixEnd_627057 := by exact prefixLift 627057
  have htrace : WordTrace (prefixWord ++ tailWord_627057) baseStart_627057 baseEnd_627057 := by
    simpa [prefixWord, tailWord_627057, baseEnd_627057] using wordTrace_append hprefix tailTrace_627057
  have hstable : (prefixWord ++ tailWord_627057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627057).length < 2 ^ (prefixWord ++ tailWord_627057).sum := by decide
  have hdescent : baseEnd_627057 < baseStart_627057 := by decide
  rcases family_descends (prefixWord ++ tailWord_627057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627121 : List Nat := [1, 2, 2, 4, 1, 2, 1, 3, 3, 4]
def baseStart_627121 : Nat := 118140960795 + 627121 * 2 ^ 59
def prefixEnd_627121 : Nat := 4983230072969 + 3 ^ 40 * 627121 * 2
def baseEnd_627121 : Nat := 107338167176115373301143

theorem tailTrace_627121 : CollatzResearch.WordTrace tailWord_627121 prefixEnd_627121 107338167176115373301143 := by
  unfold tailWord_627121
  simp only [CollatzResearch.WordTrace]
  refine ⟨22872981961055195584945217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15248654640703463723296811 22872981961055195584945217)
  ·
    refine ⟨17154736470791396688708913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22872981961055195584945217 17154736470791396688708913)
    ·
      refine ⟨12866052353093547516531685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17154736470791396688708913 12866052353093547516531685)
      ·
        refine ⟨2412384816205040159349691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12866052353093547516531685 2412384816205040159349691)
        ·
          refine ⟨3618577224307560239024537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2412384816205040159349691 3618577224307560239024537)
          ·
            refine ⟨2713932918230670179268403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3618577224307560239024537 2713932918230670179268403)
            ·
              refine ⟨4070899377346005268902605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2713932918230670179268403 4070899377346005268902605)
              ·
                refine ⟨1526587266504751975838477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4070899377346005268902605 1526587266504751975838477)
                ·
                  refine ⟨572470224939281990939429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1526587266504751975838477 572470224939281990939429)
                  ·
                    refine ⟨107338167176115373301143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 572470224939281990939429 107338167176115373301143)
                    ·
                      rfl

theorem cell23_627121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 1, 3, 3, 4].length) (baseStart_627121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627121 prefixEnd_627121 := by exact prefixLift 627121
  have htrace : WordTrace (prefixWord ++ tailWord_627121) baseStart_627121 baseEnd_627121 := by
    simpa [prefixWord, tailWord_627121, baseEnd_627121] using wordTrace_append hprefix tailTrace_627121
  have hstable : (prefixWord ++ tailWord_627121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627121).length < 2 ^ (prefixWord ++ tailWord_627121).sum := by decide
  have hdescent : baseEnd_627121 < baseStart_627121 := by decide
  rcases family_descends (prefixWord ++ tailWord_627121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627211 : List Nat := [1, 1, 1, 1, 7, 2, 1, 2, 1, 6]
def baseStart_627211 : Nat := 118140960795 + 627211 * 2 ^ 59
def prefixEnd_627211 : Nat := 4983230072969 + 3 ^ 40 * 627211 * 2
def baseEnd_627211 : Nat := 107353571595750255926005

theorem tailTrace_627211 : CollatzResearch.WordTrace tailWord_627211 prefixEnd_627211 107353571595750255926005 := by
  unfold tailWord_627211
  simp only [CollatzResearch.WordTrace]
  refine ⟨22876264530729140955721487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15250843020486093970480991 22876264530729140955721487)
  ·
    refine ⟨34314396796093711433582231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22876264530729140955721487 34314396796093711433582231)
    ·
      refine ⟨51471595194140567150373347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34314396796093711433582231 51471595194140567150373347)
      ·
        refine ⟨77207392791210850725560021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51471595194140567150373347 77207392791210850725560021)
        ·
          refine ⟨1809548268544004313880313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 77207392791210850725560021 1809548268544004313880313)
          ·
            refine ⟨1357161201408003235410235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1809548268544004313880313 1357161201408003235410235)
            ·
              refine ⟨2035741802112004853115353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357161201408003235410235 2035741802112004853115353)
              ·
                refine ⟨1526806351584003639836515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2035741802112004853115353 1526806351584003639836515)
                ·
                  refine ⟨2290209527376005459754773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526806351584003639836515 2290209527376005459754773)
                  ·
                    refine ⟨107353571595750255926005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2290209527376005459754773 107353571595750255926005)
                    ·
                      rfl

theorem cell23_627211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2, 1, 2, 1, 6].length) (baseStart_627211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627211 prefixEnd_627211 := by exact prefixLift 627211
  have htrace : WordTrace (prefixWord ++ tailWord_627211) baseStart_627211 baseEnd_627211 := by
    simpa [prefixWord, tailWord_627211, baseEnd_627211] using wordTrace_append hprefix tailTrace_627211
  have hstable : (prefixWord ++ tailWord_627211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627211).length < 2 ^ (prefixWord ++ tailWord_627211).sum := by decide
  have hdescent : baseEnd_627211 < baseStart_627211 := by decide
  rcases family_descends (prefixWord ++ tailWord_627211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627224 : List Nat := [2, 1, 2, 3, 3, 12]
def baseStart_627224 : Nat := 118140960795 + 627224 * 2 ^ 59
def prefixEnd_627224 : Nat := 4983230072969 + 3 ^ 40 * 627224 * 2
def baseEnd_627224 : Nat := 1325380205908474143685

theorem tailTrace_627224 : CollatzResearch.WordTrace tailWord_627224 prefixEnd_627224 1325380205908474143685 := by
  unfold tailWord_627224
  simp only [CollatzResearch.WordTrace]
  refine ⟨11438369339841022087972363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15251159119788029450629817 11438369339841022087972363)
  ·
    refine ⟨17157554009761533131958545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11438369339841022087972363 17157554009761533131958545)
    ·
      refine ⟨12868165507321149848968909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17157554009761533131958545 12868165507321149848968909)
      ·
        refine ⟨4825562065245431193363341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12868165507321149848968909 4825562065245431193363341)
        ·
          refine ⟨1809585774467036697511253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4825562065245431193363341 1809585774467036697511253)
          ·
            refine ⟨1325380205908474143685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 1809585774467036697511253 1325380205908474143685)
            ·
              rfl

theorem cell23_627224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 12].length) (baseStart_627224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627224 prefixEnd_627224 := by exact prefixLift 627224
  have htrace : WordTrace (prefixWord ++ tailWord_627224) baseStart_627224 baseEnd_627224 := by
    simpa [prefixWord, tailWord_627224, baseEnd_627224] using wordTrace_append hprefix tailTrace_627224
  have hstable : (prefixWord ++ tailWord_627224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627224).length < 2 ^ (prefixWord ++ tailWord_627224).sum := by decide
  have hdescent : baseEnd_627224 < baseStart_627224 := by decide
  rcases family_descends (prefixWord ++ tailWord_627224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627228 : List Nat := [2, 2, 3, 1, 2, 2, 1, 4, 2, 4]
def baseStart_627228 : Nat := 118140960795 + 627228 * 2 ^ 59
def prefixEnd_627228 : Nat := 4983230072969 + 3 ^ 40 * 627228 * 2
def baseEnd_627228 : Nat := 107356481319459067088479

theorem tailTrace_627228 : CollatzResearch.WordTrace tailWord_627228 prefixEnd_627228 107356481319459067088479 := by
  unfold tailWord_627228
  simp only [CollatzResearch.WordTrace]
  refine ⟨11438442285833776429545169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15251256381111701906060225 11438442285833776429545169)
  ·
    refine ⟨8578831714375332322158877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11438442285833776429545169 8578831714375332322158877)
    ·
      refine ⟨3217061892890749620809579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8578831714375332322158877 3217061892890749620809579)
      ·
        refine ⟨4825592839336124431214369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3217061892890749620809579 4825592839336124431214369)
        ·
          refine ⟨3619194629502093323410777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4825592839336124431214369 3619194629502093323410777)
          ·
            refine ⟨2714395972126569992558083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3619194629502093323410777 2714395972126569992558083)
            ·
              refine ⟨4071593958189854988837125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2714395972126569992558083 4071593958189854988837125)
              ·
                refine ⟨763423867160597810406961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4071593958189854988837125 763423867160597810406961)
                ·
                  refine ⟨572567900370448357805221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 763423867160597810406961 572567900370448357805221)
                  ·
                    refine ⟨107356481319459067088479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 572567900370448357805221 107356481319459067088479)
                    ·
                      rfl

theorem cell23_627228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_627228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627228 prefixEnd_627228 := by exact prefixLift 627228
  have htrace : WordTrace (prefixWord ++ tailWord_627228) baseStart_627228 baseEnd_627228 := by
    simpa [prefixWord, tailWord_627228, baseEnd_627228] using wordTrace_append hprefix tailTrace_627228
  have hstable : (prefixWord ++ tailWord_627228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627228).length < 2 ^ (prefixWord ++ tailWord_627228).sum := by decide
  have hdescent : baseEnd_627228 < baseStart_627228 := by decide
  rcases family_descends (prefixWord ++ tailWord_627228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627229 : List Nat := [1, 4, 2, 2, 1, 4, 2, 2, 1, 1, 3]
def baseStart_627229 : Nat := 118140960795 + 627229 * 2 ^ 59
def prefixEnd_627229 : Nat := 4983230072969 + 3 ^ 40 * 627229 * 2
def baseEnd_627229 : Nat := 322069957439031697352933

theorem tailTrace_627229 : CollatzResearch.WordTrace tailWord_627229 prefixEnd_627229 322069957439031697352933 := by
  unfold tailWord_627229
  simp only [CollatzResearch.WordTrace]
  refine ⟨22876921044663930029876741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15251280696442620019917827 22876921044663930029876741)
  ·
    refine ⟨4289422695874486880601889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22876921044663930029876741 4289422695874486880601889)
    ·
      refine ⟨3217067021905865160451417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4289422695874486880601889 3217067021905865160451417)
      ·
        refine ⟨2412800266429398870338563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3217067021905865160451417 2412800266429398870338563)
        ·
          refine ⟨3619200399644098305507845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2412800266429398870338563 3619200399644098305507845)
          ·
            refine ⟨678600074933268432282721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3619200399644098305507845 678600074933268432282721)
            ·
              refine ⟨508950056199951324212041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 678600074933268432282721 508950056199951324212041)
              ·
                refine ⟨381712542149963493159031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 508950056199951324212041 381712542149963493159031)
                ·
                  refine ⟨572568813224945239738547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381712542149963493159031 572568813224945239738547)
                  ·
                    refine ⟨858853219837417859607821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 572568813224945239738547 858853219837417859607821)
                    ·
                      refine ⟨322069957439031697352933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 858853219837417859607821 322069957439031697352933)
                      ·
                        rfl

theorem cell23_627229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_627229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627229 prefixEnd_627229 := by exact prefixLift 627229
  have htrace : WordTrace (prefixWord ++ tailWord_627229) baseStart_627229 baseEnd_627229 := by
    simpa [prefixWord, tailWord_627229, baseEnd_627229] using wordTrace_append hprefix tailTrace_627229
  have hstable : (prefixWord ++ tailWord_627229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627229).length < 2 ^ (prefixWord ++ tailWord_627229).sum := by decide
  have hdescent : baseEnd_627229 < baseStart_627229 := by decide
  rcases family_descends (prefixWord ++ tailWord_627229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627244 : List Nat := [2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 6]
def baseStart_627244 : Nat := 118140960795 + 627244 * 2 ^ 59
def prefixEnd_627244 : Nat := 4983230072969 + 3 ^ 40 * 627244 * 2
def baseEnd_627244 : Nat := 322077659648849138665363

theorem tailTrace_627244 : CollatzResearch.WordTrace tailWord_627244 prefixEnd_627244 322077659648849138665363 := by
  unfold tailWord_627244
  simp only [CollatzResearch.WordTrace]
  refine ⟨11438734069804793795836393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15251645426406391727781857 11438734069804793795836393)
  ·
    refine ⟨8579050552353595346877295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11438734069804793795836393 8579050552353595346877295)
    ·
      refine ⟨12868575828530393020315943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8579050552353595346877295 12868575828530393020315943)
      ·
        refine ⟨19302863742795589530473915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12868575828530393020315943 19302863742795589530473915)
        ·
          refine ⟨28954295614193384295710873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19302863742795589530473915 28954295614193384295710873)
          ·
            refine ⟨21715721710645038221783155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28954295614193384295710873 21715721710645038221783155)
            ·
              refine ⟨32573582565967557332674733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21715721710645038221783155 32573582565967557332674733)
              ·
                refine ⟨12215093462237833999753025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32573582565967557332674733 12215093462237833999753025)
                ·
                  refine ⟨9161320096678375499814769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12215093462237833999753025 9161320096678375499814769)
                  ·
                    refine ⟨6870990072508781624861077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9161320096678375499814769 6870990072508781624861077)
                    ·
                      refine ⟨322077659648849138665363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 6870990072508781624861077 322077659648849138665363)
                      ·
                        rfl

theorem cell23_627244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 6].length) (baseStart_627244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627244 prefixEnd_627244 := by exact prefixLift 627244
  have htrace : WordTrace (prefixWord ++ tailWord_627244) baseStart_627244 baseEnd_627244 := by
    simpa [prefixWord, tailWord_627244, baseEnd_627244] using wordTrace_append hprefix tailTrace_627244
  have hstable : (prefixWord ++ tailWord_627244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627244).length < 2 ^ (prefixWord ++ tailWord_627244).sum := by decide
  have hdescent : baseEnd_627244 < baseStart_627244 := by decide
  rcases family_descends (prefixWord ++ tailWord_627244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627285 : List Nat := [1, 3, 2, 2, 1, 1, 5, 2, 2, 1, 3]
def baseStart_627285 : Nat := 118140960795 + 627285 * 2 ^ 59
def prefixEnd_627285 : Nat := 4983230072969 + 3 ^ 40 * 627285 * 2
def baseEnd_627285 : Nat := 322098712355683478252675

theorem tailTrace_627285 : CollatzResearch.WordTrace tailWord_627285 prefixEnd_627285 322098712355683478252675 := by
  unfold tailWord_627285
  simp only [CollatzResearch.WordTrace]
  refine ⟨22878963532461051593915309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15252642354974034395943539 22878963532461051593915309)
  ·
    refine ⟨8579611324672894347718241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22878963532461051593915309 8579611324672894347718241)
    ·
      refine ⟨6434708493504670760788681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8579611324672894347718241 6434708493504670760788681)
      ·
        refine ⟨4826031370128503070591511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6434708493504670760788681 4826031370128503070591511)
        ·
          refine ⟨7239047055192754605887267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4826031370128503070591511 7239047055192754605887267)
          ·
            refine ⟨10858570582789131908830901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7239047055192754605887267 10858570582789131908830901)
            ·
              refine ⟨1017990992136481116452897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10858570582789131908830901 1017990992136481116452897)
              ·
                refine ⟨763493244102360837339673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017990992136481116452897 763493244102360837339673)
                ·
                  refine ⟨572619933076770628004755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 763493244102360837339673 572619933076770628004755)
                  ·
                    refine ⟨858929899615155942007133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 572619933076770628004755 858929899615155942007133)
                    ·
                      refine ⟨322098712355683478252675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 858929899615155942007133 322098712355683478252675)
                      ·
                        rfl

theorem cell23_627285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_627285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627285 prefixEnd_627285 := by exact prefixLift 627285
  have htrace : WordTrace (prefixWord ++ tailWord_627285) baseStart_627285 baseEnd_627285 := by
    simpa [prefixWord, tailWord_627285, baseEnd_627285] using wordTrace_append hprefix tailTrace_627285
  have hstable : (prefixWord ++ tailWord_627285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627285).length < 2 ^ (prefixWord ++ tailWord_627285).sum := by decide
  have hdescent : baseEnd_627285 < baseStart_627285 := by decide
  rcases family_descends (prefixWord ++ tailWord_627285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627311 : List Nat := [1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 3]
def baseStart_627311 : Nat := 118140960795 + 627311 * 2 ^ 59
def prefixEnd_627311 : Nat := 4983230072969 + 3 ^ 40 * 627311 * 2
def baseEnd_627311 : Nat := 322112062852700376527555

theorem tailTrace_627311 : CollatzResearch.WordTrace tailWord_627311 prefixEnd_627311 322112062852700376527555 := by
  unfold tailWord_627311
  simp only [CollatzResearch.WordTrace]
  refine ⟨22879911830366858034361787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15253274553577905356241191 22879911830366858034361787)
  ·
    refine ⟨34319867745550287051542681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22879911830366858034361787 34319867745550287051542681)
    ·
      refine ⟨25739900809162715288657011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34319867745550287051542681 25739900809162715288657011)
      ·
        refine ⟨38609851213744072932985517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25739900809162715288657011 38609851213744072932985517)
        ·
          refine ⟨14478694205154027349869569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38609851213744072932985517 14478694205154027349869569)
          ·
            refine ⟨10859020653865520512402177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14478694205154027349869569 10859020653865520512402177)
            ·
              refine ⟨8144265490399140384301633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10859020653865520512402177 8144265490399140384301633)
              ·
                refine ⟨6108199117799355288226225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8144265490399140384301633 6108199117799355288226225)
                ·
                  refine ⟨4581149338349516466169669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6108199117799355288226225 4581149338349516466169669)
                  ·
                    refine ⟨858965500940534337406813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4581149338349516466169669 858965500940534337406813)
                    ·
                      refine ⟨322112062852700376527555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 858965500940534337406813 322112062852700376527555)
                      ·
                        rfl

theorem cell23_627311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 2, 2, 4, 3].length) (baseStart_627311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627311 prefixEnd_627311 := by exact prefixLift 627311
  have htrace : WordTrace (prefixWord ++ tailWord_627311) baseStart_627311 baseEnd_627311 := by
    simpa [prefixWord, tailWord_627311, baseEnd_627311] using wordTrace_append hprefix tailTrace_627311
  have hstable : (prefixWord ++ tailWord_627311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627311).length < 2 ^ (prefixWord ++ tailWord_627311).sum := by decide
  have hdescent : baseEnd_627311 < baseStart_627311 := by decide
  rcases family_descends (prefixWord ++ tailWord_627311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627312 : List Nat := [2, 1, 1, 1, 7, 1, 2, 2, 1, 3, 2]
def baseStart_627312 : Nat := 118140960795 + 627312 * 2 ^ 59
def prefixEnd_627312 : Nat := 4983230072969 + 3 ^ 40 * 627312 * 2
def baseEnd_627312 : Nat := 322112576333354872615051

theorem tailTrace_627312 : CollatzResearch.WordTrace tailWord_627312 prefixEnd_627312 322112576333354872615051 := by
  unfold tailWord_627312
  simp only [CollatzResearch.WordTrace]
  refine ⟨11439974151681617602574095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15253298868908823470098793 11439974151681617602574095)
  ·
    refine ⟨17159961227522426403861143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11439974151681617602574095 17159961227522426403861143)
    ·
      refine ⟨25739941841283639605791715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17159961227522426403861143 25739941841283639605791715)
      ·
        refine ⟨38609912761925459408687573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25739941841283639605791715 38609912761925459408687573)
        ·
          refine ⟨904919830357627954891115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 38609912761925459408687573 904919830357627954891115)
          ·
            refine ⟨1357379745536441932336673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904919830357627954891115 1357379745536441932336673)
            ·
              refine ⟨1018034809152331449252505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1357379745536441932336673 1018034809152331449252505)
              ·
                refine ⟨763526106864248586939379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1018034809152331449252505 763526106864248586939379)
                ·
                  refine ⟨1145289160296372880409069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763526106864248586939379 1145289160296372880409069)
                  ·
                    refine ⟨429483435111139830153401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1145289160296372880409069 429483435111139830153401)
                    ·
                      refine ⟨322112576333354872615051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 429483435111139830153401 322112576333354872615051)
                      ·
                        rfl

theorem cell23_627312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 2, 2, 1, 3, 2].length) (baseStart_627312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627312 prefixEnd_627312 := by exact prefixLift 627312
  have htrace : WordTrace (prefixWord ++ tailWord_627312) baseStart_627312 baseEnd_627312 := by
    simpa [prefixWord, tailWord_627312, baseEnd_627312] using wordTrace_append hprefix tailTrace_627312
  have hstable : (prefixWord ++ tailWord_627312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627312).length < 2 ^ (prefixWord ++ tailWord_627312).sum := by decide
  have hdescent : baseEnd_627312 < baseStart_627312 := by decide
  rcases family_descends (prefixWord ++ tailWord_627312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627342 : List Nat := [4, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2]
def baseStart_627342 : Nat := 118140960795 + 627342 * 2 ^ 59
def prefixEnd_627342 : Nat := 4983230072969 + 3 ^ 40 * 627342 * 2
def baseEnd_627342 : Nat := 322127980752989755239913

theorem tailTrace_627342 : CollatzResearch.WordTrace tailWord_627342 prefixEnd_627342 322127980752989755239913 := by
  unfold tailWord_627342
  simp only [CollatzResearch.WordTrace]
  refine ⟨2860130311656818791092535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15254028328836366885826853 2860130311656818791092535)
  ·
    refine ⟨4290195467485228186638803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2860130311656818791092535 4290195467485228186638803)
    ·
      refine ⟨6435293201227842279958205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4290195467485228186638803 6435293201227842279958205)
      ·
        refine ⟨2413234950460440854984327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6435293201227842279958205 2413234950460440854984327)
        ·
          refine ⟨3619852425690661282476491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2413234950460440854984327 3619852425690661282476491)
          ·
            refine ⟨5429778638535991923714737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3619852425690661282476491 5429778638535991923714737)
            ·
              refine ⟨4072333978901993942786053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5429778638535991923714737 4072333978901993942786053)
              ·
                refine ⟨763562621044123864272385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4072333978901993942786053 763562621044123864272385)
                ·
                  refine ⟨572671965783092898204289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 763562621044123864272385 572671965783092898204289)
                  ·
                    refine ⟨429503974337319673653217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 572671965783092898204289 429503974337319673653217)
                    ·
                      refine ⟨322127980752989755239913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 429503974337319673653217 322127980752989755239913)
                      ·
                        rfl

theorem cell23_627342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_627342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627342 prefixEnd_627342 := by exact prefixLift 627342
  have htrace : WordTrace (prefixWord ++ tailWord_627342) baseStart_627342 baseEnd_627342 := by
    simpa [prefixWord, tailWord_627342, baseEnd_627342] using wordTrace_append hprefix tailTrace_627342
  have hstable : (prefixWord ++ tailWord_627342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627342).length < 2 ^ (prefixWord ++ tailWord_627342).sum := by decide
  have hdescent : baseEnd_627342 < baseStart_627342 := by decide
  rcases family_descends (prefixWord ++ tailWord_627342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627415 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 2, 4, 2]
def baseStart_627415 : Nat := 118140960795 + 627415 * 2 ^ 59
def prefixEnd_627415 : Nat := 4983230072969 + 3 ^ 40 * 627415 * 2
def baseEnd_627415 : Nat := 322165464840767969627077

theorem tailTrace_627415 : CollatzResearch.WordTrace tailWord_627415 prefixEnd_627415 322165464840767969627077 := by
  unfold tailWord_627415
  simp only [CollatzResearch.WordTrace]
  refine ⟨22883705021990083796147699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15255803347993389197431799 22883705021990083796147699)
  ·
    refine ⟨34325557532985125694221549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22883705021990083796147699 34325557532985125694221549)
    ·
      refine ⟨12872084074869422135333081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34325557532985125694221549 12872084074869422135333081)
      ·
        refine ⟨9654063056152066601499811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12872084074869422135333081 9654063056152066601499811)
        ·
          refine ⟨14481094584228099902249717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9654063056152066601499811 14481094584228099902249717)
          ·
            refine ⟨1357602617271384365835911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14481094584228099902249717 1357602617271384365835911)
            ·
              refine ⟨2036403925907076548753867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357602617271384365835911 2036403925907076548753867)
              ·
                refine ⟨3054605888860614823130801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2036403925907076548753867 3054605888860614823130801)
                ·
                  refine ⟨2290954416645461117348101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3054605888860614823130801 2290954416645461117348101)
                  ·
                    refine ⟨429553953121023959502769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2290954416645461117348101 429553953121023959502769)
                    ·
                      refine ⟨322165464840767969627077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 429553953121023959502769 322165464840767969627077)
                      ·
                        rfl

theorem cell23_627415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 4, 2].length) (baseStart_627415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627415 prefixEnd_627415 := by exact prefixLift 627415
  have htrace : WordTrace (prefixWord ++ tailWord_627415) baseStart_627415 baseEnd_627415 := by
    simpa [prefixWord, tailWord_627415, baseEnd_627415] using wordTrace_append hprefix tailTrace_627415
  have hstable : (prefixWord ++ tailWord_627415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627415).length < 2 ^ (prefixWord ++ tailWord_627415).sum := by decide
  have hdescent : baseEnd_627415 < baseStart_627415 := by decide
  rcases family_descends (prefixWord ++ tailWord_627415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627418 : List Nat := [3, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3]
def baseStart_627418 : Nat := 118140960795 + 627418 * 2 ^ 59
def prefixEnd_627418 : Nat := 4983230072969 + 3 ^ 40 * 627418 * 2
def baseEnd_627418 : Nat := 322167005282731457889563

theorem tailTrace_627418 : CollatzResearch.WordTrace tailWord_627418 prefixEnd_627418 322167005282731457889563 := by
  unfold tailWord_627418
  simp only [CollatzResearch.WordTrace]
  refine ⟨5720953610244803827126727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15255876293986143539004605 5720953610244803827126727)
  ·
    refine ⟨8581430415367205740690091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5720953610244803827126727 8581430415367205740690091)
    ·
      refine ⟨12872145623050808611035137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8581430415367205740690091 12872145623050808611035137)
      ·
        refine ⟨9654109217288106458276353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12872145623050808611035137 9654109217288106458276353)
        ·
          refine ⟨7240581912966079843707265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9654109217288106458276353 7240581912966079843707265)
          ·
            refine ⟨5430436434724559882780449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7240581912966079843707265 5430436434724559882780449)
            ·
              refine ⟨4072827326043419912085337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5430436434724559882780449 4072827326043419912085337)
              ·
                refine ⟨3054620494532564934064003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4072827326043419912085337 3054620494532564934064003)
                ·
                  refine ⟨4581930741798847401096005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054620494532564934064003 4581930741798847401096005)
                  ·
                    refine ⟨859112014087283887705501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4581930741798847401096005 859112014087283887705501)
                    ·
                      refine ⟨322167005282731457889563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 859112014087283887705501 322167005282731457889563)
                      ·
                        rfl

theorem cell23_627418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_627418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627418 prefixEnd_627418 := by exact prefixLift 627418
  have htrace : WordTrace (prefixWord ++ tailWord_627418) baseStart_627418 baseEnd_627418 := by
    simpa [prefixWord, tailWord_627418, baseEnd_627418] using wordTrace_append hprefix tailTrace_627418
  have hstable : (prefixWord ++ tailWord_627418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627418).length < 2 ^ (prefixWord ++ tailWord_627418).sum := by decide
  have hdescent : baseEnd_627418 < baseStart_627418 := by decide
  rcases family_descends (prefixWord ++ tailWord_627418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627425 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 3, 4]
def baseStart_627425 : Nat := 118140960795 + 627425 * 2 ^ 59
def prefixEnd_627425 : Nat := 4983230072969 + 3 ^ 40 * 627425 * 2
def baseEnd_627425 : Nat := 107390199882437643500677

theorem tailTrace_627425 : CollatzResearch.WordTrace tailWord_627425 prefixEnd_627425 107390199882437643500677 := by
  unfold tailWord_627425
  simp only [CollatzResearch.WordTrace]
  refine ⟨22884069751953855504011729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15256046501302570336007819 22884069751953855504011729)
  ·
    refine ⟨17163052313965391628008797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22884069751953855504011729 17163052313965391628008797)
    ·
      refine ⟨6436144617737021860503299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17163052313965391628008797 6436144617737021860503299)
      ·
        refine ⟨9654216926605532790754949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6436144617737021860503299 9654216926605532790754949)
        ·
          refine ⟨1810165673738537398266553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9654216926605532790754949 1810165673738537398266553)
          ·
            refine ⟨1357624255303903048699915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1810165673738537398266553 1357624255303903048699915)
            ·
              refine ⟨2036436382955854573049873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357624255303903048699915 2036436382955854573049873)
              ·
                refine ⟨1527327287216890929787405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2036436382955854573049873 1527327287216890929787405)
                ·
                  refine ⟨572747732706334098670277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1527327287216890929787405 572747732706334098670277)
                  ·
                    refine ⟨107390199882437643500677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 572747732706334098670277 107390199882437643500677)
                    ·
                      rfl

theorem cell23_627425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 3, 4].length) (baseStart_627425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627425 prefixEnd_627425 := by exact prefixLift 627425
  have htrace : WordTrace (prefixWord ++ tailWord_627425) baseStart_627425 baseEnd_627425 := by
    simpa [prefixWord, tailWord_627425, baseEnd_627425] using wordTrace_append hprefix tailTrace_627425
  have hstable : (prefixWord ++ tailWord_627425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627425).length < 2 ^ (prefixWord ++ tailWord_627425).sum := by decide
  have hdescent : baseEnd_627425 < baseStart_627425 := by decide
  rcases family_descends (prefixWord ++ tailWord_627425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627432 : List Nat := [2, 1, 4, 1, 4, 2, 1, 1, 2, 1, 4]
def baseStart_627432 : Nat := 118140960795 + 627432 * 2 ^ 59
def prefixEnd_627432 : Nat := 4983230072969 + 3 ^ 40 * 627432 * 2
def baseEnd_627432 : Nat := 322174194011894403114499

theorem tailTrace_627432 : CollatzResearch.WordTrace tailWord_627432 prefixEnd_627432 322174194011894403114499 := by
  unfold tailWord_627432
  simp only [CollatzResearch.WordTrace]
  refine ⟨11442162531464247849758275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15256216708618997133011033 11442162531464247849758275)
  ·
    refine ⟨17163243797196371774637413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11442162531464247849758275 17163243797196371774637413)
    ·
      refine ⟨3218108211974319707744515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17163243797196371774637413 3218108211974319707744515)
      ·
        refine ⟨4827162317961479561616773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3218108211974319707744515 4827162317961479561616773)
        ·
          refine ⟨905092934617777417803145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4827162317961479561616773 905092934617777417803145)
          ·
            refine ⟨678819700963333063352359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 905092934617777417803145 678819700963333063352359)
            ·
              refine ⟨1018229551444999595028539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 678819700963333063352359 1018229551444999595028539)
              ·
                refine ⟨1527344327167499392542809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1018229551444999595028539 1527344327167499392542809)
                ·
                  refine ⟨1145508245375624544407107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1527344327167499392542809 1145508245375624544407107)
                  ·
                    refine ⟨1718262368063436816610661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1145508245375624544407107 1718262368063436816610661)
                    ·
                      refine ⟨322174194011894403114499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1718262368063436816610661 322174194011894403114499)
                      ·
                        rfl

theorem cell23_627432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_627432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627432 prefixEnd_627432 := by exact prefixLift 627432
  have htrace : WordTrace (prefixWord ++ tailWord_627432) baseStart_627432 baseEnd_627432 := by
    simpa [prefixWord, tailWord_627432, baseEnd_627432] using wordTrace_append hprefix tailTrace_627432
  have hstable : (prefixWord ++ tailWord_627432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627432).length < 2 ^ (prefixWord ++ tailWord_627432).sum := by decide
  have hdescent : baseEnd_627432 < baseStart_627432 := by decide
  rcases family_descends (prefixWord ++ tailWord_627432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627442 : List Nat := [3, 2, 1, 3, 1, 2, 1, 5, 1, 4]
def baseStart_627442 : Nat := 118140960795 + 627442 * 2 ^ 59
def prefixEnd_627442 : Nat := 4983230072969 + 3 ^ 40 * 627442 * 2
def baseEnd_627442 : Nat := 107393109606146454663151

theorem tailTrace_627442 : CollatzResearch.WordTrace tailWord_627442 prefixEnd_627442 107393109606146454663151 := by
  unfold tailWord_627442
  simp only [CollatzResearch.WordTrace]
  refine ⟨5721172448223066851845145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 15256459861928178271587053 5721172448223066851845145)
  ·
    refine ⟨4290879336167300138883859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5721172448223066851845145 4290879336167300138883859)
    ·
      refine ⟨6436319004250950208325789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4290879336167300138883859 6436319004250950208325789)
      ·
        refine ⟨2413619626594106328122171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6436319004250950208325789 2413619626594106328122171)
        ·
          refine ⟨3620429439891159492183257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2413619626594106328122171 3620429439891159492183257)
          ·
            refine ⟨2715322079918369619137443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3620429439891159492183257 2715322079918369619137443)
            ·
              refine ⟨4072983119877554428706165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715322079918369619137443 4072983119877554428706165)
              ·
                refine ⟨381842167488520727691203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4072983119877554428706165 381842167488520727691203)
                ·
                  refine ⟨572763251232781091536805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 381842167488520727691203 572763251232781091536805)
                  ·
                    refine ⟨107393109606146454663151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 572763251232781091536805 107393109606146454663151)
                    ·
                      rfl

theorem cell23_627442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_627442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627442 prefixEnd_627442 := by exact prefixLift 627442
  have htrace : WordTrace (prefixWord ++ tailWord_627442) baseStart_627442 baseEnd_627442 := by
    simpa [prefixWord, tailWord_627442, baseEnd_627442] using wordTrace_append hprefix tailTrace_627442
  have hstable : (prefixWord ++ tailWord_627442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627442).length < 2 ^ (prefixWord ++ tailWord_627442).sum := by decide
  have hdescent : baseEnd_627442 < baseStart_627442 := by decide
  rcases family_descends (prefixWord ++ tailWord_627442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627465 : List Nat := [1, 2, 1, 1, 3, 2, 3, 3, 3, 1, 3]
def baseStart_627465 : Nat := 118140960795 + 627465 * 2 ^ 59
def prefixEnd_627465 : Nat := 4983230072969 + 3 ^ 40 * 627465 * 2
def baseEnd_627465 : Nat := 322191138873492774001847

theorem tailTrace_627465 : CollatzResearch.WordTrace tailWord_627465 prefixEnd_627465 322191138873492774001847 := by
  unfold tailWord_627465
  simp only [CollatzResearch.WordTrace]
  refine ⟨22885528671808942335467849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15257019114539294890311899 22885528671808942335467849)
  ·
    refine ⟨17164146503856706751600887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22885528671808942335467849 17164146503856706751600887)
    ·
      refine ⟨25746219755785060127401331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17164146503856706751600887 25746219755785060127401331)
      ·
        refine ⟨38619329633677590191101997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25746219755785060127401331 38619329633677590191101997)
        ·
          refine ⟨14482248612629096321663249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38619329633677590191101997 14482248612629096321663249)
          ·
            refine ⟨10861686459471822241247437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14482248612629096321663249 10861686459471822241247437)
            ·
              refine ⟨4073132422301933340467789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10861686459471822241247437 4073132422301933340467789)
              ·
                refine ⟨1527424658363225002675421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4073132422301933340467789 1527424658363225002675421)
                ·
                  refine ⟨572784246886209376003283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1527424658363225002675421 572784246886209376003283)
                  ·
                    refine ⟨859176370329314064004925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 572784246886209376003283 859176370329314064004925)
                    ·
                      refine ⟨322191138873492774001847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 859176370329314064004925 322191138873492774001847)
                      ·
                        rfl

theorem cell23_627465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 3, 3, 3, 1, 3].length) (baseStart_627465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627465 prefixEnd_627465 := by exact prefixLift 627465
  have htrace : WordTrace (prefixWord ++ tailWord_627465) baseStart_627465 baseEnd_627465 := by
    simpa [prefixWord, tailWord_627465, baseEnd_627465] using wordTrace_append hprefix tailTrace_627465
  have hstable : (prefixWord ++ tailWord_627465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627465).length < 2 ^ (prefixWord ++ tailWord_627465).sum := by decide
  have hdescent : baseEnd_627465 < baseStart_627465 := by decide
  rcases family_descends (prefixWord ++ tailWord_627465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627502 : List Nat := [4, 1, 3, 2, 1, 1, 2, 3, 1, 5]
def baseStart_627502 : Nat := 118140960795 + 627502 * 2 ^ 59
def prefixEnd_627502 : Nat := 4983230072969 + 3 ^ 40 * 627502 * 2
def baseEnd_627502 : Nat := 107403379219236376413059

theorem tailTrace_627502 : CollatzResearch.WordTrace tailWord_627502 prefixEnd_627502 107403379219236376413059 := by
  unfold tailWord_627502
  simp only [CollatzResearch.WordTrace]
  refine ⟨2860859771584362206820595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 15257918781783265103043173 2860859771584362206820595)
  ·
    refine ⟨4291289657376543310230893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2860859771584362206820595 4291289657376543310230893)
    ·
      refine ⟨1609233621516203741336585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4291289657376543310230893 1609233621516203741336585)
      ·
        refine ⟨1206925216137152806002439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1609233621516203741336585 1206925216137152806002439)
        ·
          refine ⟨1810387824205729209003659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1206925216137152806002439 1810387824205729209003659)
          ·
            refine ⟨2715581736308593813505489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810387824205729209003659 2715581736308593813505489)
            ·
              refine ⟨2036686302231445360129117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2715581736308593813505489 2036686302231445360129117)
              ·
                refine ⟨763757363336792010048419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2036686302231445360129117 763757363336792010048419)
                ·
                  refine ⟨1145636045005188015072629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763757363336792010048419 1145636045005188015072629)
                  ·
                    refine ⟨107403379219236376413059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1145636045005188015072629 107403379219236376413059)
                    ·
                      rfl

theorem cell23_627502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_627502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627502 prefixEnd_627502 := by exact prefixLift 627502
  have htrace : WordTrace (prefixWord ++ tailWord_627502) baseStart_627502 baseEnd_627502 := by
    simpa [prefixWord, tailWord_627502, baseEnd_627502] using wordTrace_append hprefix tailTrace_627502
  have hstable : (prefixWord ++ tailWord_627502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627502).length < 2 ^ (prefixWord ++ tailWord_627502).sum := by decide
  have hdescent : baseEnd_627502 < baseStart_627502 := by decide
  rcases family_descends (prefixWord ++ tailWord_627502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627505 : List Nat := [1, 2, 2, 3, 2, 1, 1, 5, 1, 1, 4]
def baseStart_627505 : Nat := 118140960795 + 627505 * 2 ^ 59
def prefixEnd_627505 : Nat := 4983230072969 + 3 ^ 40 * 627505 * 2
def baseEnd_627505 : Nat := 322211678099672617501663

theorem tailTrace_627505 : CollatzResearch.WordTrace tailWord_627505 prefixEnd_627505 322211678099672617501663 := by
  unfold tailWord_627505
  simp only [CollatzResearch.WordTrace]
  refine ⟨22886987591664029166923969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15257991727776019444615979 22886987591664029166923969)
  ·
    refine ⟨17165240693748021875192977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22886987591664029166923969 17165240693748021875192977)
    ·
      refine ⟨12873930520311016406394733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17165240693748021875192977 12873930520311016406394733)
      ·
        refine ⟨4827723945116631152398025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12873930520311016406394733 4827723945116631152398025)
        ·
          refine ⟨3620792958837473364298519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4827723945116631152398025 3620792958837473364298519)
          ·
            refine ⟨5431189438256210046447779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3620792958837473364298519 5431189438256210046447779)
            ·
              refine ⟨8146784157384315069671669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5431189438256210046447779 8146784157384315069671669)
              ·
                refine ⟨763761014754779537781719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8146784157384315069671669 763761014754779537781719)
                ·
                  refine ⟨1145641522132169306672579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763761014754779537781719 1145641522132169306672579)
                  ·
                    refine ⟨1718462283198253960008869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1145641522132169306672579 1718462283198253960008869)
                    ·
                      refine ⟨322211678099672617501663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 1718462283198253960008869 322211678099672617501663)
                      ·
                        rfl

theorem cell23_627505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 5, 1, 1, 4].length) (baseStart_627505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627505 prefixEnd_627505 := by exact prefixLift 627505
  have htrace : WordTrace (prefixWord ++ tailWord_627505) baseStart_627505 baseEnd_627505 := by
    simpa [prefixWord, tailWord_627505, baseEnd_627505] using wordTrace_append hprefix tailTrace_627505
  have hstable : (prefixWord ++ tailWord_627505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627505).length < 2 ^ (prefixWord ++ tailWord_627505).sum := by decide
  have hdescent : baseEnd_627505 < baseStart_627505 := by decide
  rcases family_descends (prefixWord ++ tailWord_627505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627528 : List Nat := [2, 1, 3, 1, 1, 3, 4, 8]
def baseStart_627528 : Nat := 118140960795 + 627528 * 2 ^ 59
def prefixEnd_627528 : Nat := 4983230072969 + 3 ^ 40 * 627528 * 2
def baseEnd_627528 : Nat := 11934203264989852870891

theorem tailTrace_627528 : CollatzResearch.WordTrace tailWord_627528 prefixEnd_627528 11934203264989852870891 := by
  unfold tailWord_627528
  simp only [CollatzResearch.WordTrace]
  refine ⟨11443913235290352047505619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15258550980387136063340825 11443913235290352047505619)
  ·
    refine ⟨17165869852935528071258429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11443913235290352047505619 17165869852935528071258429)
    ·
      refine ⟨6437201194850823026721911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17165869852935528071258429 6437201194850823026721911)
      ·
        refine ⟨9655801792276234540082867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6437201194850823026721911 9655801792276234540082867)
        ·
          refine ⟨14483702688414351810124301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9655801792276234540082867 14483702688414351810124301)
          ·
            refine ⟨5431388508155381928796613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14483702688414351810124301 5431388508155381928796613)
            ·
              refine ⟨1018385345279134111649365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5431388508155381928796613 1018385345279134111649365)
              ·
                refine ⟨11934203264989852870891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1018385345279134111649365 11934203264989852870891)
                ·
                  rfl

theorem cell23_627528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 8].length) (baseStart_627528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627528 prefixEnd_627528 := by exact prefixLift 627528
  have htrace : WordTrace (prefixWord ++ tailWord_627528) baseStart_627528 baseEnd_627528 := by
    simpa [prefixWord, tailWord_627528, baseEnd_627528] using wordTrace_append hprefix tailTrace_627528
  have hstable : (prefixWord ++ tailWord_627528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627528).length < 2 ^ (prefixWord ++ tailWord_627528).sum := by decide
  have hdescent : baseEnd_627528 < baseStart_627528 := by decide
  rcases family_descends (prefixWord ++ tailWord_627528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627532 : List Nat := [2, 2, 1, 3, 3, 2, 1, 3, 2, 4]
def baseStart_627532 : Nat := 118140960795 + 627532 * 2 ^ 59
def prefixEnd_627532 : Nat := 4983230072969 + 3 ^ 40 * 627532 * 2
def baseEnd_627532 : Nat := 107408514025781337288013

theorem tailTrace_627532 : CollatzResearch.WordTrace tailWord_627532 prefixEnd_627532 107408514025781337288013 := by
  unfold tailWord_627532
  simp only [CollatzResearch.WordTrace]
  refine ⟨11443986181283106389078425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 15258648241710808518771233 11443986181283106389078425)
  ·
    refine ⟨8582989635962329791808819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11443986181283106389078425 8582989635962329791808819)
    ·
      refine ⟨12874484453943494687713229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8582989635962329791808819 12874484453943494687713229)
      ·
        refine ⟨4827931670228810507892461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12874484453943494687713229 4827931670228810507892461)
        ·
          refine ⟨1810474376335803940459673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4827931670228810507892461 1810474376335803940459673)
          ·
            refine ⟨1357855782251852955344755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1810474376335803940459673 1357855782251852955344755)
            ·
              refine ⟨2036783673377779433017133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1357855782251852955344755 2036783673377779433017133)
              ·
                refine ⟨763793877516667287381425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2036783673377779433017133 763793877516667287381425)
                ·
                  refine ⟨572845408137500465536069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 763793877516667287381425 572845408137500465536069)
                  ·
                    refine ⟨107408514025781337288013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 572845408137500465536069 107408514025781337288013)
                    ·
                      rfl

theorem cell23_627532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 2, 4].length) (baseStart_627532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627532 prefixEnd_627532 := by exact prefixLift 627532
  have htrace : WordTrace (prefixWord ++ tailWord_627532) baseStart_627532 baseEnd_627532 := by
    simpa [prefixWord, tailWord_627532, baseEnd_627532] using wordTrace_append hprefix tailTrace_627532
  have hstable : (prefixWord ++ tailWord_627532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627532).length < 2 ^ (prefixWord ++ tailWord_627532).sum := by decide
  have hdescent : baseEnd_627532 < baseStart_627532 := by decide
  rcases family_descends (prefixWord ++ tailWord_627532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_627555 : List Nat := [1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 3]
def baseStart_627555 : Nat := 118140960795 + 627555 * 2 ^ 59
def prefixEnd_627555 : Nat := 4983230072969 + 3 ^ 40 * 627555 * 2
def baseEnd_627555 : Nat := 322237352132397421876433

theorem tailTrace_627555 : CollatzResearch.WordTrace tailWord_627555 prefixEnd_627555 322237352132397421876433 := by
  unfold tailWord_627555
  simp only [CollatzResearch.WordTrace]
  refine ⟨22888811241482887706244119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 15259207494321925137496079 22888811241482887706244119)
  ·
    refine ⟨34333216862224331559366179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22888811241482887706244119 34333216862224331559366179)
    ·
      refine ⟨51499825293336497339049269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34333216862224331559366179 51499825293336497339049269)
      ·
        refine ⟨4828108621250296625535869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51499825293336497339049269 4828108621250296625535869)
        ·
          refine ⟨1810540732968861234575951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4828108621250296625535869 1810540732968861234575951)
          ·
            refine ⟨2715811099453291851863927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1810540732968861234575951 2715811099453291851863927)
            ·
              refine ⟨4073716649179937777795891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2715811099453291851863927 4073716649179937777795891)
              ·
                refine ⟨6110574973769906666693837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073716649179937777795891 6110574973769906666693837)
                ·
                  refine ⟨2291465615163715000010189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6110574973769906666693837 2291465615163715000010189)
                  ·
                    refine ⟨859299605686393125003821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2291465615163715000010189 859299605686393125003821)
                    ·
                      refine ⟨322237352132397421876433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 859299605686393125003821 322237352132397421876433)
                      ·
                        rfl

theorem cell23_627555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 1, 3, 3, 3].length) (baseStart_627555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_627555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_627555 prefixEnd_627555 := by exact prefixLift 627555
  have htrace : WordTrace (prefixWord ++ tailWord_627555) baseStart_627555 baseEnd_627555 := by
    simpa [prefixWord, tailWord_627555, baseEnd_627555] using wordTrace_append hprefix tailTrace_627555
  have hstable : (prefixWord ++ tailWord_627555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_627555).length < 2 ^ (prefixWord ++ tailWord_627555).sum := by decide
  have hdescent : baseEnd_627555 < baseStart_627555 := by decide
  rcases family_descends (prefixWord ++ tailWord_627555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
